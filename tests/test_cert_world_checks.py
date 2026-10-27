"""The make-check steps that need the certified world run where it is.

On a tree without certificates or an ACL2 launcher, protocol_emit --wire,
host_check's translate, system_books and reach_check --strict (for its
events behind a generated function) exit 2 with NOT RUN, a capability
skip that tools/check_steps.py does not count red (coordinator ruling
2026-10-10, MAKE-CHECK-CERT-WORLD-NOT-RUN).  The condition of that ruling is
that a tree WITH the world runs them, so nothing reaches dev skipped: this
module is that witness, on the train's box step and any certified tree.
"""
import os
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

STEPS = (
    ("protocol_emit", [sys.executable, "tools/protocol_emit.py", "--wire", "--check"]),
    ("host_check", [sys.executable, "tools/host_check.py"]),
    ("system_books", [sys.executable, "tools/system_books.py", "check"]),
)


def cert_cache() -> str | None:
    """The certificate cache the steps read: FN_CERT_CACHE, else the farm
    cache this machine holds (tools/farm.py HOSTS, the cache the box step's
    certify installed from)."""
    named = os.environ.get("FN_CERT_CACHE")
    if named:
        return named
    sys.path.insert(0, str(ROOT / "tools"))
    import farm
    for settings in farm.HOSTS.values():
        cache = Path(str(settings.get("cache", ""))).expanduser()
        if settings.get("cache") and cache.is_dir():
            return str(cache)
    return None


def world() -> str | None:
    """Why this tree cannot run the steps, or None when it can."""
    if not os.environ.get("FN_ACL2"):
        return "no ACL2 launcher (FN_ACL2)"
    for book in ("books/wire-export", "books/image-world", "books/image-world-dtn"):
        if not (ROOT / (book + ".cert")).is_file():
            return "no certificate for " + book
    return None


class CertifiedWorldTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        missing = world()
        if missing and os.environ.get("FN_CERT_WORLD_REQUIRED"):
            # the train's box step certifies the world and sets this: a skip
            # there would let the three steps reach dev unrun
            raise AssertionError("FN_CERT_WORLD_REQUIRED and " + missing)
        if missing:
            raise unittest.SkipTest("capability -- " + missing +
                                    "; the train's box step runs this module")

    def test_each_world_step_runs_and_passes(self):
        env = dict(os.environ)
        cache = cert_cache()
        if cache:
            env["FN_CERT_CACHE"] = cache
        for name, command in STEPS:
            with self.subTest(step=name):
                done = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                      timeout=3600, env=env)
                said = done.stdout + done.stderr
                self.assertNotIn("NOT RUN", said, said[-2000:])
                # with the world in hand each step's verdict is the box step's:
                # a red blocks the train, as a skip does (ruling (b) 2026-10-10)
                self.assertEqual(done.returncode, 0, said[-2000:])


if __name__ == "__main__":
    unittest.main()
