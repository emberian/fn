import sys
from pathlib import Path
sys.path.insert(0, "."); sys.path.insert(0, "tests/bp-dtn7")
from tools import run_store, workflow_journal
from tools.workflow_bridge import Acl2WorkflowReplay
run = Path(sys.argv[1])
wf = run / "relay-a" / "workflow" / "records"
recs = [workflow_journal.decode_record(p.read_bytes()) for p in sorted(wf.iterdir())]
for p, (k, v) in zip(sorted(wf.iterdir()), recs):
    print(p.name, k, {x: v[x] for x in v if x in ("txid", "tx-generation", "work-id", "phase", "result", "msgid")})
store, acl2, _ = run_store.open_live_store(run / "relay-a" / "store", False)
b = Acl2WorkflowReplay(acl2)
b(tuple(recs))
print("fenced", b.fenced())
pending = [v for k, v in recs if k == "enqueue"][-1]
for phase, result in (("recovery", "committed"), ("recovery", "absent")):
    rec = ("outcome", {"txid": pending["txid"], "tx-generation": pending["tx-generation"], "phase": phase, "result": result})
    print(phase, result, "history", b.history_preflight(tuple(recs) + (rec,)), "record", b.preflight(rec))
print("history alone", b.history_preflight(tuple(recs)))

rec = ("outcome", {"txid": pending["txid"], "tx-generation": pending["tx-generation"], "phase": "recovery", "result": "committed"})
b2 = Acl2WorkflowReplay(acl2)
try:
    b2(tuple(recs) + (rec,)); print("install of history+recovery outcome: ready, fenced", b2.fenced())
except Exception as e:
    print("install of history+recovery outcome:", repr(e))
b3 = Acl2WorkflowReplay(acl2); b3(tuple(recs))
try:
    b3.apply_record(rec); print("live apply of recovery outcome on the installed image: ready, fenced", b3.fenced())
except Exception as e:
    print("live apply:", repr(e))
