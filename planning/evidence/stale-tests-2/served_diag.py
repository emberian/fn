"""Diagnostic: evaluate the served stored-octets derivation's parts."""
import os, sys, tempfile
from pathlib import Path
sys.path.insert(0, os.getcwd())
from tests.campaign import model_images
from tests.campaign.native_operator_campaign import CANDIDATE_ID, GROUP, PRIOR_ID, Node, article
from tests import test_native_served_crash_model as m

with tempfile.TemporaryDirectory(prefix="fn-served-diag-") as scratch:
    base = Path(scratch)
    prior = base / "prior.art"; prior.write_bytes(article(PRIOR_ID, "prior", "prior retained body"))
    cand = article(CANDIDATE_ID, "candidate", "interrupted body")
    node = Node(Path(os.environ["FN_NATIVE_CRASH_HOST"]), base, "diag")
    try:
        assert node.operator("init", GROUP)["rc"] == 0
        owner = node.start_owner(); assert owner["ready"]
        assert node.post(PRIOR_ID, prior)["rc"] == 0
        node.stop_owner(owner)
        before = model_images.import_image(node.store)
        form = m.served_stored_payload(node.store, CANDIDATE_ID, cand).format(unix_ms=1790272091000)
        print("config files", sorted(p.name for p in (node.store / "config").iterdir()))
        b = model_images.ModelBridge()
        for f in ('(include-book "books/byte-store-keystones")', '(include-book "books/byte-store-observation-scan")',
                  '(include-book "books/codec-attach")', '(include-book "books/store-events")') + m.SERVED_BRIDGE_SETUP:
            b.call(f, timeout=600)
        pre = "(before {}) (before-scan (fn-bs-scan-store before))".format(before)
        binds = m.served_decision_bindings(node.store, CANDIDATE_ID, cand).format(unix_ms=1790272091000)
        q = "(let* ({} {}) (list :cfgrecs (if (equal config-records :bad) :bad (len config-records)) :events (if (equal events :bad) :bad (len events)) :scanrecs (len (fn-bs-scan-records before-scan)) :open (fn-sn-open-kind opened) :replay (fn-replay-result-kind (fn-cpr-replay config-records events)) :agent (fn-oag-agent cfg) :reason (fn-inj-decision-reason decision) :injected (fn-inj-injectedp decision)))".format(pre, binds)
        print(b.value(q, timeout=120)[-3000:])
        b.close()
    finally:
        node.reap()
