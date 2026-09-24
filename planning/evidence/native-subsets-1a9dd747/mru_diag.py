# Diagnostic only: run test_older_mru_wait_allows_younger_forward_and_replays
# with assertEqual wrapped to list the receiver lifecycle directory on failure.
import sys, unittest
sys.path.insert(0, ".")
from tests.test_bp_node_native import NativeBpNodeTests as T
orig = unittest.TestCase.assertEqual
def patched(self, a, b, msg=None):
    try:
        orig(self, a, b, msg)
    except AssertionError:
        d = getattr(self, "receiver_journal", None)
        if d is not None:
            for p in sorted((d / "lifecycle").glob("*")):
                print("LIFECYCLE", p.name, p.stat().st_size, p.read_bytes()[:48].hex())
        raise
unittest.TestCase.assertEqual = patched
orig_run = __import__("subprocess").run
def run(*a, **k):
    r = orig_run(*a, **k)
    if r.stdout and b"BP forwarding" in r.stdout:
        print("DISPATCH-STDOUT", r.stdout.decode("utf-8", "replace")[-4000:])
    return r
T.__module__
import tests.test_bp_node_native as m
m.subprocess.run = run
suite = unittest.TestSuite([T("test_older_mru_wait_allows_younger_forward_and_replays")])
unittest.TextTestRunner(verbosity=2).run(suite)
