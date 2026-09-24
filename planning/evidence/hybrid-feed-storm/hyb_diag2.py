# Diagnostic: run the hybrid peering case with each owner's stderr teed and the
# temporary root kept, so both owner logs and feed journals survive.
import os, sys, subprocess, unittest, itertools, tempfile, shutil
sys.path.insert(0, ".")
DIAG = sys.argv[1]
TEST = sys.argv[2] if len(sys.argv) > 2 else "test_authored_carrier_survives_native_peering_and_receiver_restart"
os.makedirs(DIAG, exist_ok=True)
import tests.test_native_hybrid_author as m
counter = itertools.count()
real = subprocess.Popen
class Tee(real):
    def __init__(self, args, *a, **k):
        s = [str(x) for x in args]
        if "operator" in s and "run" in s:
            n = next(counter)
            k["stderr"] = open(os.path.join(DIAG, f"owner{n}-{os.path.basename(s[-2])}.stderr"), "wb")
            if os.environ.get("STRACE") and n == 0:
                args = ["strace", "-f", "-tt", "-s", "400", "-e", "trace=connect,sendto,recvfrom,read,write,close,shutdown",
                        "-o", os.path.join(DIAG, "owner0.strace")] + list(args)
        super().__init__(args, *a, **k)
m.subprocess.Popen = Tee
class Kept:
    def __init__(self, prefix=None, **k):
        self.name = os.path.join(DIAG, "root")
        shutil.rmtree(self.name, ignore_errors=True)
        os.makedirs(self.name)
    def cleanup(self): pass
m.tempfile.TemporaryDirectory = Kept
suite = unittest.TestSuite([m.NativeHybridAuthorTest(TEST)])
r = unittest.TextTestRunner(verbosity=2).run(suite)
sys.exit(0 if r.wasSuccessful() else 1)
