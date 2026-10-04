# T5 image verb — brief stub (python-diet-4, 2026-10-04)

An input to a brief, not a design. Row L13 PYTHON-DIET-4 (build/coordinator/COMPLETE-BEFORE-6.6.0.md):
"the T5 image verb so app_journal/consumer_e2/recovery stop using Acl2Session".

## Verdict: not small; not done in python-diet-4
The Python never computes these values today: `tests/native_harness.py` `Acl2Session`
drives `fn acl2 session` (host/native/acl2-session.lisp, developer images only), so ACL2
computes every identity and frame. What T5 removes is a test-side ACL2 REPL, and the
three named modules want five unrelated computations, not one verb:

| module | Acl2Session uses | what it derives |
|---|---|---|
| tests/test_native_app_journal.py:226 | 1 | `bridge.subject(msgid, article)`: `fn-store-subject-id-of-payload` → `fn-store-identity-text`; `fn-bpa-make-request`/`fn-bpa-encode` |
| tests/test_native_consumer_e2.py:328 | 1 | `fn-stxa-decode-exact` → `fn-stmt-value` → `fn-record-decode-exact` of a consumer report (a decoder over a report the node wrote) |
| tests/test_native_recovery.py:26, :117, :327 | 3 | a record transaction (`fn-record-make`, `fn-record-encode`), `fn-sn-sweep-rounds`/`fn-sn-sweep-round` over named orphans, `fn-sxp-manifest-line` |

The same session is used by nine more modules and two tools (count of `Acl2Session(`):
test_bp_node_native 14, test_bp_fragment_node_native 2, tests/bp-dtn7/run_fn_dtn7_app_receipt 2,
test_bp_app_native, test_native_consumer_exchange_two_nodes, test_native_control,
test_native_outcome_algebra, test_native_protected_peering, tools/synth_log_store.py
(+ tools/synth-log-store.lisp), tools/resilience/adapters/bp_node.py.

## What a brief would ask
1. Decide the shape first (ember / integrator): (a) one developer verb family
   `fn derive subject|record|stxa-decode|manifest-line ARGS` declared by `definterface`
   (each a host entry with a keystone subject, octets in and out on stdin/stdout, no REPL),
   or (b) keep `fn acl2 session` as the developer-only oracle and drop the T5 goal for
   tests (the session is not Python deciding a value; AGENTS.md's rule is met).
2. If (a): the recovery sweep-rounds case is a test of `fn-sn-sweep-*` itself and belongs
   in a test book (tests/acl2/), not a verb; consumer_e2's decode is `fn operator ...
   inspect` territory (an existing verb may already print it); app_journal's subject is
   the one genuinely new verb.
3. Owners: host verb = the lane owning host/native/admin.lisp (actors, next wave);
   test edits = testing-setup. Python lines removed: ~60 in the three modules plus,
   only if every user converts, `Acl2Session` itself (~120 in tests/native_harness.py).
   The diet value is small; the value is one fewer REPL dependency in native tests.
