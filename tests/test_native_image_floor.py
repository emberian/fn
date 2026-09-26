"""HST-017: the saved image's logical world is the execution world.

host/native/build.lisp strips the world before save-exec
(host/native/strip-world.lisp): every property the prover, the undo stack and
the history commands read goes, and what the executable counterparts, guard
checking, stobj and attachment dispatch, LP's start and error reporting read
stays at its current value.  These witnesses run the saved images:

* a guard violation at the host boundary (the developer verb `guard-probe'
  calls fn-sha256-of-string on 42 through fnn-call) is the fault it was
  before the strip: the same stderr line and exit 4
  (planning/evidence/image-floor-2026-09-26.md has the unstripped image's
  line, byte-identical);
* the same with ACL2_SYSTEM_BOOKS set, the start path on which LP's
  replace-project-dir-alist walks the world from event 0 (the strip keeps a
  bottom of command 0, event 0 and the project-dir-alist triple for it);
* the production image refuses the verb by name (exit 5);
* the core's dynamic content is under 128 MiB (271 MiB before the strip and
  the residue drop), and
  a fresh node started with a 256 MB dynamic space takes a POST and serves
  it back;
* the control stack books/heap-reservation.lisp decides for the small,
  development and scale profiles (1,192 KiB: 512 KiB + 40 octets for each
  of the 16,384 + 1,024 lines a 32,768-octet article can have) posts, serves,
  reopens and serves again the worst such article, every body line empty; and
  a third of it (384 KiB) does not (the owner faults on control-stack
  exhaustion), so the witness measures the stack and not the harness.

Each witness skips, naming the image, when that image is absent.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
DEVELOPER = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
MEASURE = ROOT / "tools" / "runtime_image" / "node_measure.py"

EXIT_FAULT, EXIT_USAGE = 4, 5
GUARD_LINE = (b"store: ACL2 error in fn-sha256-of-string: "
              b"(EV-FNCALL-GUARD-ER FN-SHA256-OF-STRING (42) (STRINGP S) (NIL) NIL)\n")
CORE_CEILING_KIB = 128 * 1024
SMALL_STACK_KIB = 1192          # fn-heap-stack-kib of the 32,768-octet presets


def environment(**extra):
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("SBCL_USER_ARGS", None)
    env.update(extra)
    return env


def executable(image):
    return image.is_file() and os.access(image, os.X_OK)


def run(image, args, env):
    return subprocess.run([str(image), "--fn"] + args, env=env, stdin=subprocess.DEVNULL,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)


class GuardViolationTests(unittest.TestCase):
    def setUp(self):
        if not executable(DEVELOPER):
            self.skipTest("needs the developer image %s" % DEVELOPER)

    def test_guard_violation_is_one_fault_line(self):
        res = run(DEVELOPER, ["guard-probe"], environment())
        self.assertEqual(res.returncode, EXIT_FAULT, res.stderr)
        self.assertEqual(res.stdout, b"")
        self.assertEqual(res.stderr, GUARD_LINE)

    def test_guard_violation_with_system_books(self):
        with tempfile.TemporaryDirectory() as books:
            res = run(DEVELOPER, ["guard-probe"], environment(ACL2_SYSTEM_BOOKS=books))
        self.assertEqual(res.returncode, EXIT_FAULT, res.stderr)
        self.assertEqual(res.stderr, GUARD_LINE)


class ProductionTests(unittest.TestCase):
    def setUp(self):
        if not executable(IMAGE):
            self.skipTest("needs the production image %s" % IMAGE)

    def test_production_refuses_guard_probe(self):
        res = run(IMAGE, ["guard-probe"], environment())
        self.assertEqual(res.returncode, EXIT_USAGE, res.stderr)
        self.assertIn(b"guard-probe is available only in the developer image", res.stderr)

    def test_core_dynamic_content(self):
        res = subprocess.run([sys.executable, str(MEASURE), "core", str(IMAGE)],
                             env=environment(), stdout=subprocess.PIPE, check=True, timeout=120)
        doc = json.loads(res.stdout)
        self.assertIsNotNone(doc["core_required_kib"], doc)
        self.assertLess(doc["core_required_kib"], CORE_CEILING_KIB, doc)

    def test_fresh_node_serves_in_256_mb(self):
        with tempfile.TemporaryDirectory() as work:
            res = subprocess.run([sys.executable, str(MEASURE), "floor", str(IMAGE), work,
                                  "--lo", "248", "--hi", "256"],
                                 env=environment(), stdout=subprocess.PIPE, check=True,
                                 timeout=600)
        doc = json.loads(res.stdout)
        self.assertEqual(doc["trials"][0][:2], [256, True], doc)

    def stack_trial(self, kib):
        with tempfile.TemporaryDirectory() as work:
            res = subprocess.run([sys.executable, str(MEASURE), "stack-floor", str(IMAGE),
                                  work, "--octets", "32768", "--line-octets", "2",
                                  "--heap", "1024", "--hi", str(kib), "--lo", str(kib - 1)],
                                 env=environment(), stdout=subprocess.PIPE, check=True,
                                 timeout=900)
        return json.loads(res.stdout)

    def test_decided_stack_holds_the_largest_small_article(self):
        doc = self.stack_trial(SMALL_STACK_KIB)
        self.assertEqual(doc["trials"][0][:2], [SMALL_STACK_KIB, True], doc)

    def test_a_third_of_the_stack_does_not(self):
        doc = self.stack_trial(384)
        self.assertEqual(doc["trials"][0][:2], [384, False], doc)
        self.assertIsNone(doc["stack_floor_kib"], doc)


if __name__ == "__main__":
    unittest.main()
