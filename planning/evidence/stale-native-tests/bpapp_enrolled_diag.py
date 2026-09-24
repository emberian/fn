"""bp-app with the sender enrolled: what each side logs, after 30 s.

Run from the tree root with the native-subsets environment.  Uses the test's
own setUp (store init, sender boundary enrollment, request ADU), starts the
receiver and a one-shot `bp send`, waits 30 s, then prints both sides' output
and whether each process had exited.
"""
import time
import unittest

from tests.test_bp_app_native import NativeBpApplicationTests

case = NativeBpApplicationTests("test_application_receipt_releases_forward_pin_only_after_durable_record")
NativeBpApplicationTests.setUpClass()
case.setUp()
try:
    receiver, port = case.start_receiver()
    sender = case.start_sender(port)
    time.sleep(30)
    for name, proc in (("sender", sender), ("receiver", receiver)):
        print(f"== {name} poll after 30 s: {proc.poll()}")
        if proc.poll() is None:
            proc.terminate()
        out, err = proc.communicate(timeout=30)
        print(f"== {name} rc {proc.returncode}\n-- stdout\n{out.decode('utf-8', 'replace')}\n-- stderr\n{err.decode('utf-8', 'replace')}")
    evidence = sorted(p.relative_to(case.temp).as_posix()
                      for p in case.temp.rglob("receive-evidence/*"))
    print("== receive-evidence files:", evidence)
    for p in case.temp.rglob("receive-evidence/*refused*"):
        print("--", p.name, p.read_bytes()[:200])
finally:
    case.doCleanups()
