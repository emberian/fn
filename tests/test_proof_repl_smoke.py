"""check-fast's live check of tools/proof_repl.py: start, admit one defthm, stop.

Every lane iterates proofs in proof_repl (DEPUTY-RULES, REPL-first), so a
merge that breaks it stops the whole team without failing any gate:
7469e52af deleted theory_check.TOKEN, which proof_repl's form reader still
called, and every `proof_repl start` died at load on dev until lane
n-repl-token.  This test runs the real tool end to end through ACL2 on a
fixture book with no includes (no certificate cache, no farm): `start` loads
the book, `send` admits a defthm over the book's defun and refuses a false
one, `stop` ends the session.  It does not skip when ACL2 is missing: a box
that runs check-fast is a box lanes REPL on.
"""

import os
import shutil
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "tools" / "proof_repl.py"
SESSIONS = ROOT / "build" / "proof-repl"


def cli(*words, timeout=60):
    return subprocess.run([sys.executable, str(TOOL), *words], capture_output=True,
                          text=True, cwd=ROOT, timeout=timeout)


class ProofReplSmokeTests(unittest.TestCase):
    def test_start_admits_a_defthm_and_refuses_a_false_one(self):
        tag = str(os.getpid())
        scratch = ROOT / "build" / ("proof-repl-smoke-" + tag)
        scratch.mkdir(parents=True, exist_ok=True)
        book = scratch.relative_to(ROOT).as_posix() + "/smoke"
        (scratch / "smoke.lisp").write_text(
            '(in-package "ACL2")\n'
            '; The fixture of tests/test_proof_repl_smoke.py: one defun, no includes.\n'
            '(defun smoke-twice (x) (declare (xargs :guard (acl2-numberp x))) (* 2 x))\n')
        name = "smoke-" + tag
        try:
            started = cli("start", name, book, timeout=60)
            self.assertEqual(started.returncode, 0, started.stdout + started.stderr)
            proved = cli("send", name,
                         "(defthm smoke-twice-is-a-sum (implies (acl2-numberp x)"
                         " (equal (smoke-twice x) (+ x x))))")
            self.assertEqual(proved.returncode, 0, proved.stdout + proved.stderr)
            refused = cli("send", name,
                          "(defthm smoke-twice-is-the-identity (equal (smoke-twice x) x))")
            self.assertEqual(refused.returncode, 1, refused.stdout + refused.stderr)
        finally:
            cli("stop", name)
            shutil.rmtree(SESSIONS / name, ignore_errors=True)
            shutil.rmtree(scratch, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
