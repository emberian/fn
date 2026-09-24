# Diagnostic only: start the test's receiver and sender, wait 45 s, stop both
# (only these two PIDs), print their output.
import sys, time
sys.path.insert(0, ".")
from tests.test_bp_app_native import NativeBpApplicationTests as T
T.setUpClass() if hasattr(T, "setUpClass") else None
t = T("test_lost_receipt_restart_replays_without_second_acceptance")
t.setUp()
try:
    r, port = t.start_receiver()
    s = t.start_sender(port)
    print("pids receiver", r.pid, "sender", s.pid, flush=True)
    time.sleep(45)
    for name, p in (("sender", s), ("receiver", r)):
        print(name, "poll", p.poll())
        if p.poll() is None:
            p.terminate()
        try:
            out, err = p.communicate(timeout=20)
        except Exception:
            p.kill(); out, err = p.communicate(timeout=20)
        print("==", name, "rc", p.returncode)
        print("-- stdout tail\n", (out or b"")[-3000:].decode("utf-8", "replace"))
        print("-- stderr tail\n", (err or b"")[-3000:].decode("utf-8", "replace"))
finally:
    t.tearDown() if hasattr(t, "tearDown") else None
    for c in reversed(getattr(t, "_cleanups", [])):
        pass
t.doCleanups()
