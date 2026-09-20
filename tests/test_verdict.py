"""tools/verdict.py: the box lock, reading an existing gate, and the table.

Three defects drove these, and each has a case here. The tool kept a lock
scheme of its own (an atomic `mkdir` on `.verdict.lock`) beside the `flock`
file the hand-written gate scripts take, and two schemes that cannot see
each other are not a lock. `--reuse-gate` asked for `gate.done`, which no
hand gate writes, so every hand gate fell through to the path that ships a
commit and starts a certification. And the per-root row came from
`acl2_exit_codes`, which the certify driver's `(quit)` makes 0 for a book
whose `certify-book` failed: on persvati's `dev-909e055` that read 1 failing
root where `book_results` names 25.

No ssh here: every box interaction is stubbed, and what is under test is the
script this tool sends and what it does with the answer.
"""

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parent.parent / "tools"
sys.path.insert(0, str(TOOLS))
SPEC = importlib.util.spec_from_file_location("verdict", TOOLS / "verdict.py")
verdict = importlib.util.module_from_spec(SPEC)
sys.modules["verdict"] = verdict
SPEC.loader.exec_module(verdict)


class Box:
    """A stand-in host: it remembers every script and answers by keyword."""

    def __init__(self, answers: dict[str, tuple[int, str]]):
        self.answers = answers
        self.scripts: list[tuple[str, str]] = []

    def __call__(self, host: str, script: str, timeout: int = 300):
        self.scripts.append((host, script))
        for needle, answer in self.answers.items():
            if needle in script:
                return answer
        return (0, "")

    def sent(self, needle: str) -> list[str]:
        return [script for _, script in self.scripts if needle in script]


class GateLockTests(unittest.TestCase):
    """One lock per box, and it is the file the hand gates already take."""

    def test_the_lock_is_the_hand_gates_flock_file_on_each_box(self):
        # Measured on the boxes 2026-09-20: persvati's gate.sh does
        # `exec 9>~/fn-gates/.gate.lock; flock 9`, hbox's does
        # `exec 9>/tank/fn/gates/.lock; flock 9`.
        self.assertEqual(verdict.gate_lock("hbox"), "/tank/fn/gates/.lock")
        self.assertEqual(verdict.gate_lock("persvati"),
                         "$HOME/fn-gates/.gate.lock")
        self.assertEqual(verdict.gate_lock("somewhere-else"),
                         "$HOME/fn-gates/.gate.lock")
        # And nothing takes a second one.  The old scheme is named in the
        # module docstring as history, so this looks for the mechanism.
        source = (TOOLS / "verdict.py").read_text()
        code = source.split('"""', 2)[-1]
        self.assertNotIn(".verdict.lock", code)
        self.assertNotIn('mkdir "$lock"', code)

    def test_the_generated_gate_script_holds_that_lock_while_it_certifies(self):
        script = verdict.GATE_SH.format(
            gate="/tank/fn/gates/dev-abc", acl2="/tank/fn/acl2", timeout=5400,
            jobs=8, cache="/tank/fn/certcache",
            lock=verdict.gate_lock("hbox"))
        self.assertIn("exec 9>/tank/fn/gates/.lock", script)
        self.assertIn("\nflock 9\n", script)
        # Held across the certification, not released before it.
        self.assertLess(script.index("flock 9"), script.index("make certify"))

    def test_a_held_lock_refuses_and_names_the_file_and_the_holder(self):
        box = Box({"flock -n": (0, "HELD gate.sh 1151069\n")})
        with mock.patch.object(verdict, "ssh", box):
            with self.assertRaises(SystemExit) as raised:
                verdict.GateLock(["hbox"], wait=False).check()
        said = str(raised.exception)
        self.assertIn("/tank/fn/gates/.lock", said)
        self.assertIn("gate.sh 1151069", said)
        self.assertIn("--wait-for-lock", said)

    def test_wait_for_lock_queues_instead_of_refusing(self):
        box = Box({"flock -n": (0, "HELD gate.sh 1\n")})
        with mock.patch.object(verdict, "ssh", box):
            verdict.GateLock(["hbox"], wait=True).check()  # no SystemExit

    def test_a_free_lock_is_not_taken_here(self):
        """The hold belongs to the gate script; this only asks."""
        box = Box({"flock -n": (0, "FREE\n")})
        with mock.patch.object(verdict, "ssh", box):
            verdict.GateLock(["persvati"], wait=False).check()
        probe = box.sent("flock -n")[0]
        self.assertIn("flock -n \"$lock\" true", probe)
        self.assertNotIn("mkdir \"$lock\"", probe)


HAND_GATE = """PRESENT
DONE
HAS certify.log exit=2
HAS pytests.log exit=1
HAS publish.log exit=0
MANIFESTS 1
"""


class ReuseGateTests(unittest.TestCase):
    """Reading a gate directory someone else made, and never certifying."""

    MANIFEST = {
        "manifest": "build/acl2/certify-1/manifest.json",
        "status": "failed", "acl2_version": "ACL2 Version 8.7",
        "roots": 3, "verdict_source": "book_results",
        "bad": ["books/served"],
        "certify": "exit=2\n", "pytests": "Ran 9 tests in 1.0s\nOK\n",
        "publish": "exit=0\n",
    }

    def fiber(self) -> verdict.Fiber:
        return verdict.Fiber("gate", "persvati", "make certify")

    def test_a_hand_gate_with_no_gate_done_is_read_rather_than_re_run(self):
        box = Box({"test -d": (0, HAND_GATE),
                   "VERDICT_HARVEST": (0, json.dumps(self.MANIFEST))})
        fiber = self.fiber()
        with mock.patch.object(verdict, "ssh", box):
            facts = verdict.certify_gate(fiber, Path("."), "c0ffee", "c0ffee",
                                         "dev", 6, "$HOME/fn-certcache",
                                         "acl2", 60, reuse="909e055")
        self.assertTrue(facts["reused"])
        self.assertEqual(facts["gate"], "$HOME/fn-gates/dev-909e055")
        self.assertEqual(facts["missing_artefacts"], [])
        # Nothing was shipped and nothing was launched.
        self.assertEqual(box.sent("tar -x"), [])
        self.assertEqual(box.sent("gate.sh"), [])
        self.assertEqual(box.sent("setsid"), [])

    def test_the_reused_revision_names_the_directory_not_the_commit(self):
        box = Box({"test -d": (0, HAND_GATE),
                   "VERDICT_HARVEST": (0, json.dumps(self.MANIFEST))})
        with mock.patch.object(verdict, "ssh", box):
            facts = verdict.certify_gate(self.fiber(), Path("."), "c0ffee",
                                         "c0ffee", "dev", 6, "cache", "acl2",
                                         60, reuse="")
        self.assertEqual(facts["gate"], "$HOME/fn-gates/dev-c0ffee")

    def test_a_gate_directory_that_is_not_there_is_a_row_saying_so(self):
        box = Box({"test -d": (0, "ABSENT\n")})
        fiber = self.fiber()
        with mock.patch.object(verdict, "ssh", box):
            verdict.certify_gate(fiber, Path("."), "c0ffee", "c0ffee", "dev",
                                 6, "cache", "acl2", 60, reuse="nosuch")
        self.assertEqual(fiber.state, "not run")
        self.assertIn("nothing was started", fiber.summary)
        self.assertEqual(box.sent("tar -x"), [])

    def test_an_interrupted_gate_names_the_artefact_it_is_missing(self):
        listing = "PRESENT\nDONE\nHAS certify.log exit=2\nABSENT pytests.log\n" \
                  "ABSENT publish.log\nMANIFESTS 1\n"
        box = Box({"test -d": (0, listing),
                   "VERDICT_HARVEST": (0, json.dumps(self.MANIFEST))})
        fiber = self.fiber()
        with mock.patch.object(verdict, "ssh", box):
            facts = verdict.certify_gate(fiber, Path("."), "c0ffee", "c0ffee",
                                         "dev", 6, "cache", "acl2", 60,
                                         reuse="52eb0db")
        self.assertEqual(facts["missing_artefacts"],
                         ["publish.log", "pytests.log"])
        self.assertIn("absent from this gate: publish.log, pytests.log",
                      fiber.summary)

    def test_a_gate_with_no_manifest_certified_nothing_this_can_read(self):
        box = Box({"test -d": (0, "PRESENT\nDONE\nABSENT certify.log\n"
                                  "ABSENT pytests.log\nABSENT publish.log\n"
                                  "MANIFESTS 0\n")})
        fiber = self.fiber()
        with mock.patch.object(verdict, "ssh", box):
            verdict.certify_gate(fiber, Path("."), "c0ffee", "c0ffee", "dev",
                                 6, "cache", "acl2", 60, reuse="empty")
        self.assertEqual(fiber.rc, 1)
        self.assertIn("no certification manifest", fiber.summary)


class PerRootVerdictTests(unittest.TestCase):
    """The row counts failing ROOTS, and an exit code is not a verdict."""

    def harvest_of(self, manifest: dict) -> tuple[verdict.Fiber, dict]:
        payload = dict(self.PAYLOAD, **manifest)
        # The harvester runs on the box and prints one JSON line; here the
        # real reader runs over a real manifest and the ssh is the stub.
        box = Box({"VERDICT_HARVEST": (0, json.dumps(payload))})
        fiber = verdict.Fiber("gate", "persvati", "make certify")
        with mock.patch.object(verdict, "ssh", box):
            return fiber, verdict.harvest(fiber, "$HOME/fn-gates/dev-x")

    PAYLOAD = {"status": "passed", "certify": "exit=0\n",
               "pytests": "Ran 9 tests in 1.0s\nOK\n", "publish": "exit=0\n"}

    def test_a_clean_gate_passes_the_row(self):
        fiber, facts = self.harvest_of({"roots": 3, "bad": [],
                                        "verdict_source": "book_results"})
        self.assertEqual((fiber.rc, fiber.failed), (0, 0))
        self.assertEqual(facts["verdict_source"], "book_results")

    def test_the_manifest_status_word_is_passed_not_certified(self):
        """`certify_books.py` writes "passed"; nothing writes "certified"."""
        source = (TOOLS / "certify_books.py").read_text()
        self.assertIn('manifest["status"] = "passed"', source)
        self.assertNotIn('data.get("status") == "certified"',
                         (TOOLS / "verdict.py").read_text())
        self.assertIn('data.get("status") == "passed"',
                      (TOOLS / "verdict.py").read_text())

    def test_each_failing_root_is_attributed_to_the_deputy_that_owns_it(self):
        fiber, _ = self.harvest_of(
            {"roots": 3, "bad": ["books/served", "books/checkpoint-codec"]})
        self.assertEqual(fiber.failed, 2)
        self.assertEqual(fiber.failures,
                         ["books/served (nntp)", "books/checkpoint-codec (store)"])

    def test_the_box_side_reader_counts_book_results_not_exit_codes(self):
        """The reader that runs on the box, over a manifest of the real shape.

        Both books here exit 0, because the certify driver ends in `(quit)`
        and ACL2 reaches it whether or not `certify-book` succeeded. Reading
        the exit codes therefore called a failed root clean: on persvati's
        `dev-909e055` that was 1 bad root reported against 25 real ones.
        """
        manifest = {
            "status": "failed",
            "acl2_exit_codes": {"books/a": 0, "books/b": 0},
            "book_results": {"books/a": "passed", "books/b": "failed"},
            "certificate_digests_sha256": {"books/a": "d"},
        }
        with tempfile.TemporaryDirectory() as directory:
            gate = Path(directory)
            run = gate / "build" / "acl2" / "certify-1"
            run.mkdir(parents=True)
            (run / "manifest.json").write_text(json.dumps(manifest))
            body = verdict.HARVEST.split("<<'VERDICT_HARVEST'\n", 1)[1]
            body = body.split("VERDICT_HARVEST", 1)[0]
            script = gate / "harvest.py"
            script.write_text(body)
            done = subprocess.run([sys.executable, str(script), str(gate)],
                                  stdout=subprocess.PIPE, check=True)
        out = json.loads(done.stdout.decode().strip().splitlines()[-1])
        self.assertEqual(out["bad"], ["books/b"])
        self.assertEqual(out["roots"], 2)
        self.assertEqual(out["verdict_source"], "book_results")

    def test_an_older_manifest_with_no_book_results_falls_back_to_exit_codes(self):
        manifest = {"status": "passed",
                    "acl2_exit_codes": {"books/a": 0, "books/b": 1}}
        with tempfile.TemporaryDirectory() as directory:
            gate = Path(directory)
            run = gate / "build" / "acl2" / "certify-1"
            run.mkdir(parents=True)
            (run / "manifest.json").write_text(json.dumps(manifest))
            body = verdict.HARVEST.split("<<'VERDICT_HARVEST'\n", 1)[1]
            body = body.split("VERDICT_HARVEST", 1)[0]
            script = gate / "harvest.py"
            script.write_text(body)
            done = subprocess.run([sys.executable, str(script), str(gate)],
                                  stdout=subprocess.PIPE, check=True)
        out = json.loads(done.stdout.decode().strip().splitlines()[-1])
        self.assertEqual(out["bad"], ["books/b"])
        self.assertEqual(out["verdict_source"], "acl2_exit_codes")


if __name__ == "__main__":
    unittest.main()
