# Diagnostic only: repeat the first half of
# test_native_and_python_cross_open_identical_acl2_frames and dump both txn frames.
import sys, difflib
sys.path.insert(0, ".")
from tests.test_native_storage_codec import NativeStorageCodecTests as T
t = T("test_native_and_python_cross_open_identical_acl2_frames")
t.setUp()
try:
    n = t.base / "native-store"; p = t.base / "python-store"
    t.invoke(True, n, "init"); cid = "<cross-runtime@example.invalid>"
    t.post(False, n, cid)
    t.invoke(False, p, "init"); t.post(True, p, cid)
    a = (p / "transactions" / "00000000000000000000.txn").read_bytes()
    b = (n / "transactions" / "00000000000000000000.txn").read_bytes()
    print("native-wrote len", len(a), "python-wrote len", len(b))
    i = next((k for k in range(min(len(a), len(b))) if a[k] != b[k]), None)
    print("first diff at", i)
    print("native-wrote tail", a[max(0, i-40):].hex())
    print("python-wrote tail", b[max(0, i-40):].hex())
    print("native-wrote ascii", a[max(0,i-80):i+10])
finally:
    t.tearDown()
