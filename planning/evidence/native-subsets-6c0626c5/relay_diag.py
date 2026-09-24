"""Replay test_interrupted_contact_receiver_restart_then_expiry and print every
process's rc/stdout/stderr instead of stopping at the first assertion.
Run from the tree root with run.sh's environment:  python3 relay_diag.py"""
import sys
from tests.test_bp_contact_relay_native import NativeBpContactRelayTests as T

T.setUpClass()
t = T("test_interrupted_contact_receiver_restart_then_expiry")
t.setUp()
def show(tag, rc, out, err):
    print(f"== {tag} rc={rc}\n-- stdout\n{out.decode(errors='replace')}-- stderr\n{err.decode(errors='replace')}", flush=True)
try:
    first, port = t.receive_once()
    t.relay.route(port, cut_next=True)
    r = t.service_run("work-interrupted"); show("service-run interrupted", r.returncode, r.stdout, r.stderr)
    try:
        o, e = first.communicate(timeout=15)
    except Exception:
        first.kill(); o, e = first.communicate()
    show("first receiver", first.returncode, o, e)
    restarted, port2 = t.receive_once()
    t.relay.route(port2)
    c = t.tick(1, 60000); show("tick closed", c.returncode, c.stdout, c.stderr)
    print("receiver alive after closed tick:", restarted.poll() is None, flush=True)
    d = t.tick(0, 60000); show("tick open", d.returncode, d.stdout, d.stderr)
    try:
        o, e = restarted.communicate(timeout=90)
    except Exception:
        restarted.kill(); o, e = restarted.communicate()
    show("restarted receiver", restarted.returncode, o, e)
    for side in (t.sender_journal, t.receiver_journal):
        print("== tree", side)
        for p in sorted(side.rglob("*")):
            print(" ", p.relative_to(side), p.stat().st_size if p.is_file() else "/")
finally:
    t.relay.close()
