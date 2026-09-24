# Diagnostic only: run the hybrid peering case with each owner's stderr and
# stdout teed to files under DIAG so the feed's behaviour is visible.
import os, sys, subprocess, unittest, itertools
sys.path.insert(0, ".")
DIAG = sys.argv[1]
os.makedirs(DIAG, exist_ok=True)
import tests.test_native_hybrid_author as m
counter = itertools.count()
real = subprocess.Popen
class Tee(real):
    def __init__(self, args, *a, **k):
        if "operator" in [str(x) for x in args] and "run" in [str(x) for x in args]:
            n = next(counter)
            k["stderr"] = open(os.path.join(DIAG, f"owner{n}.stderr"), "wb")
        super().__init__(args, *a, **k)
m.subprocess.Popen = Tee
suite = unittest.TestSuite([m.NativeHybridAuthorTest(
    "test_authored_carrier_survives_native_peering_and_receiver_restart")])
unittest.TextTestRunner(verbosity=2).run(suite)
