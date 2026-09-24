# Diagnostic only: run the dated-source signed-poll case with acl2_boolean
# wrapped to print the raw ACL2 answer it could not read as T or NIL.
import sys, unittest
from tools import run_store
real = run_store.acl2_boolean
def shown(output):
    try:
        return real(output)
    except run_store.StoreError:
        print("RAW ACL2 ANSWER:", repr(output[-4000:]), flush=True)
        raise
run_store.acl2_boolean = shown
import tests.test_native_consumer_e2 as m
suite = unittest.TestSuite([m.NativeConsumerE2Tests(
    "test_signed_composite_poll_and_lost_positive_ack_reply")])
unittest.TextTestRunner(verbosity=2).run(suite)
