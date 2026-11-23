#!/usr/bin/env python3
"""Count the CPU instructions Lean spends on the modules a branch changes, before and after.

Run it from a checkout whose compiled files are current (`lake exe cache get`):

    python3 scripts/count-instructions.py                # this checkout against upstream/main
    python3 scripts/count-instructions.py --head pr/123  # another commit, without checking it out

Each changed module is compiled as it is at the merge base and as it is after the change. The script
calls `lean` the way Lake does and keeps what it compiles in a temporary folder, so `.lake` is not
changed. It prints a Markdown table for the pull request. Modules that import a changed module are
not counted.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile

if sys.version_info < (3, 11):
    raise SystemExit("count-instructions.py needs Python 3.11 or newer.")
import tomllib

RETIRED = re.compile(r"^\s*(\d+)\s+instructions retired\s*$", re.M)
BASES = ("upstream/main", "origin/main", "main")
NO_COUNTER = f"No instruction counter is set up for {platform.system()}. Linux (perf) and macOS (time -l) work."


def git(root, *arguments):
    return subprocess.run(["git", *arguments], cwd=root, capture_output=True, check=True).stdout


def read_header(text):
    """Parse the header of a Lean source.

    Returns whether it is a `module`, its imports as `(name, exported, meta, all)`, and whether the
    header ended before `text` did. Outside a `module`, every import is exported.
    """
    module, imports, modifiers, position, end = False, [], set(), 0, len(text)
    while position < end:
        if text[position].isspace():
            position += 1
        elif text.startswith("--", position):
            newline = text.find("\n", position)
            position = end if newline < 0 else newline
        elif text.startswith("/-", position):
            depth, position = 1, position + 2
            while depth and position < end:
                if text.startswith("/-", position):
                    depth, position = depth + 1, position + 2
                elif text.startswith("-/", position):
                    depth, position = depth - 1, position + 2
                else:
                    position += 1
        else:
            stop = position
            while stop < end and not text[stop].isspace():
                stop += 1
            if stop == end:  # The word may be cut off; the caller reads more.
                break
            word, position = text[position:stop], stop
            if "import" in modifiers and word != "all":
                name = word.replace("«", "").replace("»", "")
                imports.append((name, "public" in modifiers or not module, "meta" in modifiers, "all" in modifiers))
                modifiers = set()
            elif word in ("public", "meta", "import", "all"):
                modifiers.add(word)
            elif word == "module":
                module = True
            elif word != "prelude":
                return module, imports, True
    return module, imports, False


def header_of(path):
    with path.open(encoding="utf-8-sig", errors="replace") as stream:
        module, imports, complete = read_header(stream.read(16384))
    if not complete:
        module, imports, _ = read_header(path.read_text(encoding="utf-8-sig", errors="replace") + "\n")
    return module, imports


def import_artifacts(module, imports, header):
    """Which modules Lake lists for the compiler, and whether with their private part.

    This is `fetchTransImportArts` in Lake's `Build/Module.lean` (Lean 4.37). `imports` are the direct
    imports of the module being compiled, `module` says whether that one is a `module`, and `header`
    gives `(module, imports)` for a module of the workspace and `None` for any other.
    """
    listed, with_all, with_meta, queue = {}, set(), set(), []

    def enqueue(private, meta, name):
        for imported, exported, is_meta, is_all in header(name)[1]:
            if header(imported):
                reachable = private or exported
                needs_meta = meta or (reachable and is_meta)
                if reachable or needs_meta:
                    queue.append((imported, not module or (private and is_all), needs_meta))

    for name, _, is_meta, is_all in imports:
        if header(name):
            listed[name] = listed.get(name, False) or not module or is_all
            enqueue(not module or is_all, is_meta, name)
    while queue:
        name, private, meta = queue.pop()
        widen = (private and name not in with_all) or (meta and name not in with_meta)
        if name in listed and not (header(name)[0] and widen):
            continue
        if private:
            with_all.add(name)
        if meta:
            with_meta.add(name)
        listed[name] = name in with_all or listed.get(name, False)
        enqueue(private, meta, name)
    return listed


def dotted(table, prefix=""):
    """Turn TOML's nested tables back into dotted Lean option names."""
    for key, value in table.items():
        if isinstance(value, dict):
            yield from dotted(value, f"{prefix}{key}.")
        else:
            yield prefix + key, value


def glob_matches(pattern, module):
    """Lake's three forms: `A` is that module, `A.*` adds its submodules, `A.+` is the submodules only."""
    if pattern.endswith((".*", ".+")):
        return module.startswith(pattern[:-1]) or (pattern.endswith("*") and module == pattern[:-2])
    return module == pattern


def lean_settings(config, module):
    """The options and extra arguments lakefile.toml gives `module`: the package's, then its library's."""
    scopes = [config]
    for library in reversed(config.get("lean_lib", [])):  # Lake takes the last library that builds the module.
        roots = library.get("roots", [library["name"]])
        globs = library.get("globs", roots)
        if any(glob_matches(pattern, module) for pattern in globs) or any(
                module.startswith(root + ".") and any(glob_matches(pattern, root) for pattern in globs)
                for root in roots):
            scopes.append(library)
            break
    options = {}
    for scope in scopes:
        options.update(dotted(scope.get("leanOptions", {})))
    return options, [argument for key in ("moreLeanArgs", "weakLeanArgs") for scope in scopes
                     for argument in scope.get(key, [])]


def perf_instructions(report):
    """Sum the instruction counters in `perf stat -j` output. A CPU with two kinds of core reports two."""
    total = None
    for line in report.splitlines():
        try:
            row = json.loads(line)
            if "instructions" in row["event"]:
                total = (total or 0) + int(float(row["counter-value"]))
        except (ValueError, KeyError, TypeError):  # Not a counter line, or `<not supported>`.
            continue
    return total


def perf_stat(command, environment):
    """Run `command` under `perf stat`. Return the exit status, what perf wrote as its report, the output."""
    # The counter and the flags of Mathlib's build benchmark (scripts/bench/measure.py).
    with tempfile.NamedTemporaryFile("r") as report:
        try:
            result = subprocess.run(
                ["perf", "stat", "-j", "-o", report.name, "-e", "instructions:u", "--", *command],
                env={**environment, "LC_ALL": "C"}, capture_output=True, text=True)
        except FileNotFoundError:
            raise SystemExit("`perf` is not installed. On Linux this script counts with `perf stat`.") from None
        return result.returncode, report.read(), result.stdout + result.stderr


def check_perf(environment):
    """Count the instructions of `true`, and stop if `perf` cannot.

    The script runs this before it compiles anything. Without it, a `perf` that fails would be
    reported as a failure of Lean, on the first module.
    """
    status, report, output = perf_stat(["true"], environment)
    if status == 0 and perf_instructions(report) is not None:
        return
    said = "\n".join(text.strip() for text in (output, report) if text.strip())
    if "unknown switch" in said or "unknown option" in said:
        reason = "This `perf` does not know the `-j` flag (JSON output). perf has it from version 6.0 on."
    elif status:
        reason = "`perf` was not allowed to count, or could not."
    else:
        reason = ("`perf` ran but reported no count. This machine gives it no instruction counter, "
                  "as on many virtual machines.")
    raise SystemExit(f"`perf stat` cannot count instructions here, so nothing was compiled. {reason}\n"
                     f"perf said:\n{said}")


def counted(command, environment):
    """Run `command`. Return its exit status, its instruction count (None if none was reported), its output."""
    system = platform.system()
    if system == "Darwin":
        # `time -l` counts the process it starts and not that process's children, so `command` must be `lean`.
        result = subprocess.run(["/usr/bin/time", "-l", *command], env=environment, capture_output=True, text=True)
        found = RETIRED.search(result.stderr)
        return result.returncode, int(found[1]) if found else None, result.stdout + result.stderr
    if system == "Linux":
        status, report, output = perf_stat(command, environment)
        return status, perf_instructions(report), output
    raise SystemExit(NO_COUNTER)


class Project:
    """The checkout: its sources, its compiled modules and those of its dependencies."""

    def __init__(self, root):
        self.root = root
        self.config = tomllib.loads((root / "lakefile.toml").read_text())
        self.source_dir = Path(self.config.get("srcDir", "."))
        self.sources = root / self.source_dir
        self.compiled = root / self.config.get("buildDir", ".lake/build") / self.config.get("leanLibDir", "lib/lean")
        listing = subprocess.check_output(["lake", "env", "printenv"], cwd=root, text=True)
        self.environment = dict(line.split("=", 1) for line in listing.splitlines() if "=" in line)
        self.lean = self.environment["LEAN"]
        toolchain = self.environment.get("LEAN_SYSROOT", "\0")
        self.libraries = [Path(entry) for entry in self.environment.get("LEAN_PATH", "").split(os.pathsep)
                          if entry and Path(entry) != self.compiled]
        self.package_sources = [Path(entry) for entry in dict.fromkeys(
            self.environment.get("LEAN_SRC_PATH", "").split(os.pathsep))
            if entry and not entry.startswith(toolchain) and Path(entry) != self.sources]
        self.packages, self.headers = {}, {}

    def source(self, module):
        return self.sources / Path(*module.split(".")).with_suffix(".lean")

    def package(self, module):
        """Where a dependency keeps `module`: `(source, folder of compiled modules)`, or None."""
        if module not in self.packages:
            relative = Path(*module.split("."))
            source = next((root / relative.with_suffix(".lean") for root in self.package_sources
                           if (root / relative.with_suffix(".lean")).is_file()), None)
            library = next((root for root in self.libraries if (root / relative.with_suffix(".olean")).is_file()),
                           None)
            self.packages[module] = (source, library) if source and library else None
        return self.packages[module]

    def package_header(self, module):
        if module not in self.headers:
            found = self.package(module)
            self.headers[module] = header_of(found[0]) if found else None
        return self.headers[module]

    def modules(self, *diff):
        """Map each Lean module named by `git diff --name-status -z` output to its status letter."""
        fields = git(self.root, *diff, "--", self.source_dir.as_posix()).decode().split("\0")
        found = {}
        for status, name in zip(fields[0::2], fields[1::2]):
            path = Path(name)
            if path.suffix == ".lean":
                found[".".join(path.relative_to(self.source_dir).with_suffix("").parts)] = status
        return found

    def untracked(self):
        names = git(self.root, "ls-files", "--others", "--exclude-standard", "-z", "--", self.source_dir.as_posix())
        return {".".join(Path(name).relative_to(self.source_dir).with_suffix("").parts): "A"
                for name in names.decode().split("\0") if name.endswith(".lean")}


class Side:
    """The sources before or after the change, and the modules recompiled for them."""

    def __init__(self, project, label, revision, index, changed, work):
        self.project, self.label, self.revision, self.index, self.changed = project, label, revision, index, changed
        self.sources, self.compiled, self.setups = work / "src", work / "lib", work / "setup"
        self.headers, self.recompiled, self.used = {}, set(), set()
        self.config = tomllib.loads(self.read("lakefile.toml").decode())

    def read(self, path):
        if self.revision:
            return git(self.project.root, "show", f"{self.revision}:{path}")
        return (self.project.root / path).read_bytes()

    def own(self, module):
        """Whether `module` is one of the project's own modules on this side."""
        if module in self.changed:
            return self.changed[module][self.index]
        return self.project.source(module).is_file()

    def file(self, module):
        relative = Path(*module.split(".")).with_suffix(".lean")
        if module not in self.changed or not self.revision:
            return self.project.sources / relative
        path = self.sources / relative
        if not path.exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(self.read((self.project.source_dir / relative).as_posix()))
        return path

    def header(self, module):
        """`(module, imports)` for a module of the project or of a dependency, None for any other."""
        if module not in self.headers:
            self.headers[module] = (header_of(self.file(module)) if self.own(module)
                                    else self.project.package_header(module))
        return self.headers[module]

    def imported(self, module):
        """The project's own modules that `module` imports on this side."""
        self.used.add(module)
        return [name for name, *_ in self.header(module)[1] if self.own(name)]

    def plan(self, targets):
        """Order what to recompile: the targets, and what they import that itself reaches a changed module."""
        reaches, order = {}, []
        for target in targets:
            if target in reaches:
                continue
            reaches[target] = target in self.changed
            stack = [(target, iter(self.imported(target)))]
            while stack:
                module, rest = stack[-1]
                for dependency in rest:
                    if dependency not in reaches:
                        reaches[dependency] = dependency in self.changed
                        stack.append((dependency, iter(self.imported(dependency))))
                        break
                else:
                    stack.pop()
                    reaches[module] = reaches[module] or any(reaches[name] for name in self.imported(module))
                    if reaches[module]:
                        order.append(module)
        return order

    def artifacts(self, module, private):
        """The compiled files of `module` in the layout of Lean's `ImportArtifacts`."""
        folder = (self.compiled if module in self.recompiled else
                  self.project.compiled if self.own(module) else self.project.package(module)[1])
        stem = str(folder.joinpath(*module.split(".")))
        parts = [".olean", ".olean.server"] + [".olean.private"] * private
        return [[stem + part for part in parts if os.path.exists(stem + part)],
                [stem + part for part in (".ir.sig", ".ir") if os.path.exists(stem + part)]]

    def command(self, module):
        """Lake's call of `lean` for `module`, with the output in this side's folder."""
        is_module, imports = self.header(module)
        options, arguments = lean_settings(self.config, module)
        setup = {"name": module, "package": self.config.get("name"), "isModule": is_module, "options": options,
                 "importArts": {name: self.artifacts(name, private)
                                for name, private in import_artifacts(is_module, imports, self.header).items()},
                 "dynlibs": [], "plugins": []}
        output = self.compiled.joinpath(*module.split("."))
        output.parent.mkdir(parents=True, exist_ok=True)
        self.setups.mkdir(exist_ok=True)
        (self.setups / "setup.json").write_text(json.dumps(setup))
        self.recompiled.add(module)
        return [self.project.lean, str(self.file(module)), "-o", f"{output}.olean", "-i", f"{output}.ilean",
                "-c", str(self.setups / "module.c"), "--setup", str(self.setups / "setup.json"), *arguments]


def fail(side, module, output):
    lines = output.strip().splitlines()
    hint = ""
    if "object file" in output or "unknown module prefix" in output:
        hint = ("\nLean could not find an imported module. Either a compiled file is missing (run "
                "`lake exe cache get`), or this Lean lists imports differently from the script's `import_artifacts`.")
    raise SystemExit(f"Lean failed on {module} as it is {side.label}:\n" + "\n".join(lines[:30]) + hint)


def measure(side, targets, runs, log):
    """Recompile on one side. Return `{module: [instruction counts]}` for the targets, and how many others."""
    order, counts = side.plan(targets), {}
    # Every imported module is named in the setup file. An empty search path makes Lean fail on one
    # that is not, where it would otherwise pick up a file from `.lake` that may be out of date.
    environment = {**side.project.environment, "LEAN_PATH": ""}
    for position, module in enumerate(order, 1):
        command = side.command(module)
        if module not in targets:
            result = subprocess.run(command, env=environment, capture_output=True, text=True)
            if result.returncode:
                fail(side, module, result.stdout + result.stderr)
            log(f"{side.label} [{position}/{len(order)}] {module}  (recompiled, not counted)")
            continue
        counts[module] = []
        for _ in range(runs):
            status, count, output = counted(command, environment)
            if status:
                fail(side, module, output)
            if count is None:
                raise SystemExit("The instruction counter reported nothing. Its output was:\n" + output.strip())
            counts[module].append(count)
        log(f"{side.label} [{position}/{len(order)}] {module}  {min(counts[module]) / 1e9:.3f}")
    return counts, len(order) - len(counts)


def change(before, after):
    return f"{(after - before) / before * 100:+.1f}%" if before else ""


def table(before, after):
    """A Markdown table of the lowest count of each module, in billions, with a total."""
    rows = ["| Module | Before | After | Change |", "|---|---:|---:|---:|"]
    totals = [0, 0]
    for module in sorted(before.keys() | after.keys()):
        low = [min(side[module]) if module in side else None for side in (before, after)]
        cells = ["" if count is None else f"{count / 1e9:.3f}" for count in low]
        note = "new" if low[0] is None else "removed" if low[1] is None else change(*low)
        rows.append(f"| `{module}` | {cells[0]} | {cells[1]} | {note} |")
        totals = [total + (count or 0) for total, count in zip(totals, low)]
    rows.append(f"| **Total** | {totals[0] / 1e9:.3f} | {totals[1] / 1e9:.3f} | {change(*totals)} |")
    return "\n".join(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("files", nargs="*", type=Path, help="count only these changed files (default: all of them)")
    parser.add_argument("--base", help="branch the change is against (default: the first of " + ", ".join(BASES) + ")")
    parser.add_argument("--head", help="commit that holds the change (default: the files in this checkout)")
    parser.add_argument("--runs", type=int, default=3, help="compile each module this often and keep the lowest count")
    parser.add_argument("--project", type=Path, default=Path.cwd())
    arguments = parser.parse_args()
    if platform.system() not in ("Darwin", "Linux"):
        raise SystemExit(NO_COUNTER)
    project = Project(arguments.project.resolve())
    root = project.root
    if platform.system() == "Linux":
        check_perf(project.environment)

    def commit(name):
        result = subprocess.run(["git", "rev-parse", "--verify", "--quiet", name + "^{commit}"], cwd=root,
                                capture_output=True, text=True)
        return result.stdout.strip()

    base = arguments.base or next((name for name in BASES if commit(name)), None)
    if not base or not commit(base):
        raise SystemExit(f"Cannot find the base branch {arguments.base or ' or '.join(BASES)}. Pass --base.")
    head = commit(arguments.head) if arguments.head else None
    if arguments.head and not head:
        raise SystemExit(f"Cannot find the commit {arguments.head}.")
    merge_base = git(root, "merge-base", base, head or "HEAD").decode().strip()

    statuses = project.modules("diff", "--name-status", "--no-renames", "-z", merge_base, *([head] if head else []))
    if not head:
        statuses.update(project.untracked())
    changed = {module: (status != "A", status != "D") for module, status in statuses.items()}
    selected = set(changed)
    if arguments.files:
        wanted = {".".join(path.resolve().relative_to(project.sources).with_suffix("").parts)
                  for path in arguments.files}
        if wanted - selected:
            raise SystemExit("Not changed against the base: " + ", ".join(sorted(wanted - selected)))
        selected = wanted
    if not selected:
        print(f"No Lean file under {project.source_dir}/ differs from {base} (merge base {merge_base[:10]}).")
        return

    with tempfile.TemporaryDirectory(prefix="rh-count-instructions-") as work:
        work = Path(work)
        after_label = f"at {head[:10]}" if head else "in this checkout"
        sides = [Side(project, f"at {merge_base[:10]}", merge_base, 0, changed, work / "before"),
                 Side(project, after_label, head, 1, changed, work / "after")]
        for name in ("lean-toolchain", "lake-manifest.json"):
            if len({side.read(name) for side in sides} | {(root / name).read_bytes()}) > 1:
                raise SystemExit(f"{name} is not the same before the change, after it and in this checkout. "
                                 "The compiled files here fit only one of them.")
        if head:  # Files of this checkout that match neither side have compiled files that match neither.
            stale = {**project.modules("diff", "--name-status", "--no-renames", "-z", merge_base),
                     **project.untracked()}.keys() - changed.keys()
            for side in sides:
                side.plan(sorted(module for module in selected if changed[module][side.index]))
                used = sorted(stale & side.used)
                if used:
                    raise SystemExit(f"This checkout differs from the merge base {merge_base[:10]} in {len(used)} "
                                     f"modules that the changed modules import, such as {used[0]}. Their compiled "
                                     "files fit neither side. Update the checkout or rebase the change.")

        def log(line):
            print(line, file=sys.stderr, flush=True)

        results, extra = [], 0
        for side in sides:
            targets = sorted(module for module in selected if changed[module][side.index])
            counts, uncounted = measure(side, targets, arguments.runs, log)
            results.append(counts)
            extra = max(extra, uncounted)

    print(table(*results))
    toolchain = (root / "lean-toolchain").read_text().strip().split(":")[-1]
    print(f"\nBillions of CPU instructions spent in `lean`, lowest of {arguments.runs} runs for each module. "
          f"Lean {toolchain}, {platform.system()} {platform.machine()}.")
    print(f"Before: `{merge_base[:10]}`, the merge base with {base}. After: "
          + (f"`{head[:10]}`." if head else "the files in the checkout."))
    spreads = [(max(counts) - min(counts)) / min(counts) for side in results for counts in side.values()]
    if arguments.runs > 1:
        print(f"Runs of the same module differed by at most {max(spreads) * 100:.2f}%.")
    if extra:
        print(f"{extra} unchanged {'module' if extra == 1 else 'modules'} between the changed ones had to be "
              "recompiled too. Their cost is not counted.")
    print("Modules that import the changed ones are not counted.")


if __name__ == "__main__":
    main()
