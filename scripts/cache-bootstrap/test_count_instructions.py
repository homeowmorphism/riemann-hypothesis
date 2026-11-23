#!/usr/bin/env python3
"""Offline tests of count-instructions.py against a small project with a stand-in `lean`.

The stand-in loads imports only from the files its setup file names, the way Lean does when the
search path is empty. It derives its "instruction count" from the source and from every compiled
file it loaded, so a stale, missing or misplaced file changes the count or stops it.
"""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("count_instructions", HERE.parent / "count-instructions.py")
counter = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(counter)

IMPORT = r"^(public )?(?:meta )?import (?:all )?(\S+)"
FAKE_LEAN = r'''#!/usr/bin/env python3
import hashlib, json, os, re, sys
from pathlib import Path
arguments = sys.argv[1:]
text = Path(arguments[0]).read_text()
output = arguments[arguments.index("-o") + 1][:-len(".olean")]
setup = json.loads(Path(arguments[arguments.index("--setup") + 1]).read_text())
if "FAIL" in text:
    sys.exit("error: FAIL")
if os.environ.get("LEAN_PATH") or setup["isModule"] != text.startswith("module") or setup["package"] != "tree":
    sys.exit("error: wrong search path or setup")
if setup["options"] != {"autoImplicit": False, "pp.unicode.fun": True} or "--tstack=1" not in arguments:
    sys.exit("error: wrong options")
loaded, waiting = {}, [m[1] for m in re.findall(IMPORT, text, re.M)]
while waiting:
    name = waiting.pop()
    if name not in loaded:
        if name not in setup["importArts"]:
            sys.exit(f"error: object file of module {name} does not exist")
        loaded[name] = json.loads(Path(setup["importArts"][name][0][0]).read_text())
        waiting += loaded[name]["exports"]
digest = hashlib.sha256((text + "".join(loaded[name]["digest"] for name in sorted(loaded))).encode()).hexdigest()
exports = [m[1] for m in re.findall(IMPORT, text, re.M) if m[0] or not text.startswith("module")]
for suffix in (".olean", ".olean.server", ".olean.private", ".ilean"):
    Path(output + suffix).write_text(json.dumps({"digest": digest, "exports": exports}))
print("COST", int(digest[:8], 16))
'''.replace("IMPORT", repr(IMPORT))

# A stand-in `perf stat` of the kind named in the file `perf-kind`: "works", "denied" (may not read the
# counter), "unsupported" (the machine has none) or "old" (no `-j`). It notes each command in `perf-calls`.
FAKE_PERF = r'''#!/usr/bin/env python3
import subprocess, sys
from pathlib import Path
kind = (Path(__file__).parent / "perf-kind").read_text()
arguments = sys.argv[1:]
command = arguments[arguments.index("--") + 1:]
with (Path(__file__).parent / "perf-calls").open("a") as calls:
    calls.write(" ".join(command) + "\n")
if kind == "old":
    sys.exit(" Error: unknown switch `j'\n\n Usage: perf stat [<options>] [<command>]")
if kind == "denied":
    sys.exit("Error:\nAccess to performance monitoring and observability operations is limited.")
result = subprocess.run(command, capture_output=True, text=True)
sys.stdout.write(result.stdout)
sys.stderr.write(result.stderr)
count = "<not supported>" if kind == "unsupported" else f"{(result.stdout.split() or [1])[-1]}.000000"
Path(arguments[arguments.index("-o") + 1]).write_text(
    f'{{"counter-value" : "{count}", "unit" : "", "event" : "instructions:u"}}\n')
sys.exit(result.returncode)
'''

BEFORE = {
    "Lib": "module\n",
    "Lib.A": "module\n-- a comment\ndef a := 1\n",
    "Lib.U": "module\npublic import Lib.A\ndef u := a\n",
    "Lib.C": "def c := 3\n",
    "Lib.B": "module\n/- block /- nested -/ -/\nimport Lib.U\nimport all Lib.C\npublic meta import Top.Sub\ndef b := 2\n",
    "Lib.D": "import Lib.C\ndef d := 4\n",
    "Top": "def top := 0\n",
    "Top.Sub": "def sub := 0\n",
}
AFTER = {**BEFORE, "Lib.A": "module\ndef a := 10\n", "Lib.B": BEFORE["Lib.B"] + "def b' := 20\n",
         "Lib.E": "import Lib.U\nimport Lib\nimport Top\ndef e := 5\n", "Top": "def top := 1\n"}
del AFTER["Lib.D"]
CHANGED = ["Lib.A", "Lib.B", "Lib.D", "Lib.E", "Top"]
ORDER = ["Lib", "Lib.A", "Lib.U", "Lib.C", "Top.Sub", "Top", "Lib.B", "Lib.D", "Lib.E"]  # Imports come first.
LAKEFILE = ('name = "tree"\nsrcDir = "src"\nmoreLeanArgs = ["--tstack=1"]\n'
            "[leanOptions]\nautoImplicit = false\npp.unicode.fun = true\n")


def build(tree):
    """What the stand-in writes for every module of `tree` when each is compiled against fresh imports."""
    compiled = {}
    for module in ORDER:
        if module in tree:
            text = tree[module]
            imports = re.findall(IMPORT, text, re.M)
            loaded, waiting = set(), [name for _, name in imports]
            while waiting:
                name = waiting.pop()
                if name not in loaded:
                    loaded.add(name)
                    waiting += compiled[name]["exports"]
            digest = hashlib.sha256((text + "".join(compiled[name]["digest"] for name in sorted(loaded))).encode())
            compiled[module] = {"digest": digest.hexdigest(),
                                "exports": [name for public, name in imports if public or not text.startswith("module")]}
    return compiled


def cost(compiled):
    return f"{int(compiled['digest'][:8], 16) / 1e9:.3f}"


def fake_counted(command, environment):
    result = subprocess.run(command, env=environment, capture_output=True, text=True)
    count = int(result.stdout.split()[-1]) if result.returncode == 0 else None
    return result.returncode, count, result.stdout + result.stderr


class Project:
    def __init__(self, folder):
        self.root = folder / "project"
        self.compiled = self.root / ".lake/build/lib/lean"
        self.tools = tools = folder / "bin"
        tools.mkdir()
        (tools / "lean").write_text(FAKE_LEAN)
        (tools / "perf").write_text(FAKE_PERF)
        # Like `lake env printenv`, the stand-in passes on the rest of the environment; `perf` is found on its PATH.
        (tools / "lake").write_text(f'#!/bin/sh\necho "LEAN={tools}/lean"\necho "LEAN_PATH={self.compiled}"\n'
                                    f'echo "LEAN_SRC_PATH={self.root}/src"\necho "LEAN_SYSROOT={folder}/none"\n'
                                    'echo "PATH=$PATH"\n')
        for tool in tools.iterdir():
            tool.chmod(0o755)
        self.path = f"{tools}{os.pathsep}{os.environ['PATH']}"
        self.write(BEFORE)
        for name, text in (("lakefile.toml", LAKEFILE), ("lean-toolchain", "leanprover/lean4:v0\n"),
                           ("lake-manifest.json", "{}\n"), (".gitignore", ".lake\n")):
            (self.root / name).write_text(text)
        self.git("init", "-q", "-b", "main")
        self.commit("before")
        for module, compiled in build(BEFORE).items():  # As after `lake exe cache get` on main.
            path = self.compiled.joinpath(*module.split("."))
            path.parent.mkdir(parents=True, exist_ok=True)
            for suffix in (".olean", ".olean.server", ".olean.private", ".ilean"):
                Path(f"{path}{suffix}").write_text(json.dumps(compiled))

    def git(self, *arguments):
        subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@example.invalid", *arguments],
                       cwd=self.root, check=True, capture_output=True)

    def commit(self, message):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)

    def write(self, tree):
        sources = self.root / "src"
        for path in sources.rglob("*.lean") if sources.exists() else []:
            path.unlink()
        for module, text in tree.items():
            path = sources.joinpath(*module.split(".")).with_suffix(".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)

    def snapshot(self):
        return {str(path): path.read_bytes() for path in sorted(self.root.rglob("*"))
                if path.is_file() and ".git/" not in str(path)}

    def run(self, *arguments, perf=None):
        """Run the script's `main` in the project; return what it printed.

        With `perf`, the script runs as it does on Linux and counts with a stand-in `perf` of that kind.
        Without it, `fake_counted` does the counting and the check of the real counter is left out.
        """
        printed, saved = io.StringIO(), (sys.argv, os.environ["PATH"], counter.counted, counter.check_perf)
        sys.argv = ["count-instructions.py", "--project", str(self.root), "--base", "main", *arguments]
        os.environ["PATH"] = self.path
        if perf:
            (self.tools / "perf-kind").write_text(perf)
            system = mock.patch.object(counter.platform, "system", return_value="Linux")
        else:
            counter.counted, counter.check_perf = fake_counted, lambda environment: None
            system = contextlib.nullcontext()
        try:
            with contextlib.redirect_stdout(printed), contextlib.redirect_stderr(io.StringIO()), system:
                counter.main()
        finally:
            sys.argv, os.environ["PATH"], counter.counted, counter.check_perf = saved
        return printed.getvalue()


class Counts(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="rh-count-test-")
        self.addCleanup(temporary.cleanup)
        self.project = Project(Path(temporary.name).resolve())

    def check(self, printed):
        before, after = build(BEFORE), build(AFTER)
        for module in CHANGED:
            cells = [cost(side[module]) if module in side else "" for side in (before, after)]
            row = next(line for line in printed.splitlines() if line.startswith(f"| `{module}` |"))
            self.assertEqual([cell.strip() for cell in row.split("|")[2:4]], cells, module)
        self.assertIn("| new |", printed)
        self.assertIn("| removed |", printed)
        self.assertIn("1 unchanged module between the changed ones had to be recompiled too", printed)

    def test_uncommitted_change_in_the_checkout(self):
        self.project.write(AFTER)
        (self.project.compiled / "Lib/A.olean").write_text("left over from some other build")
        untouched = self.project.snapshot()
        self.check(self.project.run())
        self.assertEqual(self.project.snapshot(), untouched)

    def test_another_commit_without_checking_it_out(self):
        self.project.git("switch", "-q", "-c", "change")
        self.project.write(AFTER)
        self.project.commit("after")
        self.project.git("switch", "-q", "main")
        untouched = self.project.snapshot()
        self.check(self.project.run("--head", "change"))
        self.assertEqual(self.project.snapshot(), untouched)

    def test_only_the_named_files(self):
        self.project.write(AFTER)
        printed = self.project.run(str(self.project.root / "src/Lib/B.lean"))
        self.assertIn("| `Lib.B` |", printed)
        self.assertNotIn("| `Lib.A` |", printed)
        self.assertIn(cost(build(AFTER)["Lib.B"]), printed)

    def test_refuses_a_checkout_that_fits_neither_side(self):
        self.project.git("switch", "-q", "-c", "change")
        self.project.write(AFTER)
        self.project.commit("after")
        self.project.git("switch", "-q", "main")
        (self.project.root / "src/Lib/U.lean").write_text(BEFORE["Lib.U"] + "def other := 0\n")
        with self.assertRaisesRegex(SystemExit, "Update the checkout or rebase"):
            self.project.run("--head", "change")

    def test_refuses_another_toolchain(self):
        self.project.write(AFTER)
        (self.project.root / "lean-toolchain").write_text("leanprover/lean4:v1\n")
        with self.assertRaisesRegex(SystemExit, "lean-toolchain is not the same"):
            self.project.run()

    def test_reports_a_module_that_does_not_compile(self):
        self.project.write({**AFTER, "Lib.B": AFTER["Lib.B"] + "FAIL\n"})
        with self.assertRaisesRegex(SystemExit, "Lean failed on Lib.B as it is in this checkout"):
            self.project.run()

    def test_refuses_fewer_than_one_run(self):
        self.project.write(AFTER)
        with self.assertRaisesRegex(SystemExit, "--runs must be at least 1"):
            self.project.run("--runs", "0")

    def test_counts_with_perf_on_linux(self):

        self.project.write(AFTER)
        self.check(self.project.run(perf="works"))
        calls = (self.project.tools / "perf-calls").read_text().splitlines()
        self.assertEqual(calls[0], "true")  # The counter is tried before anything is compiled.

    def test_stops_before_compiling_when_perf_cannot_count(self):
        self.project.write(AFTER)
        ran = self.project.tools / "lean-ran"
        (self.project.tools / "lean").write_text(f'#!/bin/sh\ntouch "{ran}"\nexit 1\n')
        for kind, reason, said in (("denied", "not allowed to count", "Access to performance monitoring"),
                                   ("unsupported", "no instruction counter", "<not supported>"),
                                   ("old", "does not know the `-j` flag", "unknown switch")):
            message = f"(?s)^`perf stat` cannot count instructions here.*{reason}.*perf said:.*{said}"
            with self.subTest(kind), self.assertRaisesRegex(SystemExit, message):
                self.project.run(perf=kind)
            self.assertFalse(ran.exists(), kind)


class Parsing(unittest.TestCase):
    def test_header(self):
        text = "/- licence -/\nmodule\n\npublic import A.B -- why\nimport all «C».D\nmeta import E\n\nopen A\nimport F\n"
        imports = [("A.B", True, False, False), ("C.D", False, False, True), ("E", False, True, False)]
        self.assertEqual(counter.read_header(text), (True, imports, True))
        self.assertEqual(counter.read_header("import A.B\nimport C.D"), (False, [("A.B", True, False, False)], False))
        self.assertEqual(counter.read_header("prelude\nimport A\n")[1], [("A", True, False, False)])

    def test_listed_imports_follow_lake(self):
        def imports(*specs):  # "public A", "meta A", "all A" or "A"
            return [(spec.split()[-1], "public" in spec, "meta" in spec, "all" in spec) for spec in specs]
        headers = {"A": (True, imports("public B", "C")), "B": (True, []), "C": (True, imports("public D")),
                   "D": (True, []), "Old": (False, [("C", True, False, False)])}
        listed = lambda module, *specs: counter.import_artifacts(module, imports(*specs), headers.get)
        self.assertEqual(listed(True, "A", "Init"), {"A": False, "B": False})
        self.assertEqual(listed(True, "all A"), {"A": True, "B": False, "C": False, "D": False})
        self.assertEqual(listed(True, "meta A"), {"A": False, "B": False, "C": False, "D": False})
        self.assertEqual(listed(False, "A"), {"A": True, "B": True, "C": True, "D": True})
        self.assertEqual(listed(True, "Old"), {"Old": False, "C": False, "D": False})

    def test_lean_settings(self):
        config = {"moreLeanArgs": ["--tstack=400000"],
                  "leanOptions": {"autoImplicit": False, "pp": {"unicode": {"fun": True}}, "maxHeartbeats": 4000000},
                  "lean_lib": [{"name": "Ground", "globs": ["Ground.Brauer.+"]},
                               {"name": "GroundFields", "globs": ["Ground.Local.+"], "weakLeanArgs": ["-j1"],
                                "leanOptions": {"synthInstance": {"maxHeartbeats": 400000}}},
                               {"name": "Main", "roots": ["Statements", "Main"]}]}
        common = {"autoImplicit": False, "pp.unicode.fun": True, "maxHeartbeats": 4000000}
        self.assertEqual(counter.lean_settings(config, "Ground.Brauer.X"), (common, ["--tstack=400000"]))
        self.assertEqual(counter.lean_settings(config, "Ground.Local.X"),
                         ({**common, "synthInstance.maxHeartbeats": 400000}, ["--tstack=400000", "-j1"]))
        self.assertEqual(counter.lean_settings(config, "Main"), (common, ["--tstack=400000"]))

    def test_time_report(self):
        report = "        1.41 real         1.15 user         0.52 sys\n         21084439185  instructions retired\n"
        self.assertEqual(int(counter.RETIRED.search(report)[1]), 21084439185)

    def test_perf_report(self):
        line = '{{"counter-value" : "{}", "unit" : "", "event" : "{}", "event-runtime" : 1, "pcnt-running" : 100.00}}\n'
        self.assertEqual(counter.perf_instructions(line.format("21084439185.000000", "instructions:u")), 21084439185)
        both = line.format("7.000000", "cpu_core/instructions:u/") + line.format("5.000000", "cpu_atom/instructions:u/")
        self.assertEqual(counter.perf_instructions("# started on Mon\n" + both), 12)
        self.assertIsNone(counter.perf_instructions(line.format("<not supported>", "instructions:u")))


if __name__ == "__main__":
    unittest.main()
