# layer E continuation (the E seat's notebook; rewritten whole after every commit)

## Built (dev)
- E3 (6187c6aa0): fn2/docs/e-surface.md; books/port.lisp, consumer-port.lisp, consumer-model.lisp, owed-consumer.lisp; tests/consumer-mini.lisp, consumer-helm.lisp, port-unit.lisp.
- E3b (5be98c474): books/layout.lisp big-endian kinds :u16be :u32be :u64be (:octets16 n) (:octets32 n) = codes 12-16 (main ruled E builds, B reads the diff; (:fixed n) dropped: the FNCT trailer is computed, not a field; :octets32 added for fn1's kind 6/18 four-octet prefixes); teeth in tests/layout-unit.lisp, layout-roundtrip.lisp campaign rotates a BE layout. books/consumer-codec.lisp (FNCT, fncu v1/v2, k4 codes 0-18, replies 5/6/9/28, items, the code->verb table asserted against port + both carriers). tests/consumer-codec-unit.lisp (fn1's .fncu vectors read from tests/fixtures/consumer-position/, fn1 payloads/refusals, BLAKE3 KAT, served codec agreement). Carriers rebound to port codes (register 14 ... status 18).

## Owners' answers (all in e-surface.md §11): C's fn2-outcome/withdrawals forms; D's block amendment (static :max); D7 rows sent (wait-row, subscription-edge with :esub profile key, new :durable-octets kind); B's record kinds via envelope header.

- §13 peering/BP stated, revised after Astra-2 (lanes/e-quests/astra-2.md; §16); seams sent to main (D :peer-credit, D5 3/n table, exhaustion split, TAKETHIS 400 default + fn-compat; C obligations contract, cancel intent, feed-work, bundle schemas, admission ordinal; B ADU subject, evidence identity across import).

## In flight at 5be98c474
- whole-tree recertify (build/e-seat/cert-all.pid, log cert-all.log) and layout campaign rerun with :octets32 (roundtrip2.pid/.out, expect "LAYOUT ROUNDTRIP ... PASS"). Fix forward if red.

## Next
1. The multi-node reference model (§13.8): nodes, evidence, obligations, feed work, gaps; witness matrix W1-W10, F1-F7; K-P1..K-P6 owed with teeth (owed-peer.lisp), positive fixtures asserting full antecedents.
2. Owed codec pieces with their first sender (served kind): fn1 kind 18 reasoned reply (enum is 1-based there, statuses list in books/native-control.lisp), FNWD/FNRB forms.
3. Served fn2-cns + XFNC rows + edge rows (D8, mine) when D5 2/n and D6 land; K10.

## Pitfalls / commands
- REPL: `python3 tools/acl2 --timeout 400 < build/e-seat/<x>.lsp > build/e-seat/<x>.out 2>&1` (drivers: codec.lsp, cct.lsp, mini2.lsp, helm.lsp).
- Certify: `sh fn2/tools/certify.sh books/consumer-codec.lisp tests/consumer-codec-unit.lisp ...`; whole tree: `sh fn2/tools/certify.sh $(cat build/e-seat/all-certs.txt)` (detached, PID file).
- Layout campaign: `python3 tools/acl2 --timeout 900 < fn2/tests/layout-roundtrip.lsp` (detached; prints LAYOUT ROUNDTRIP ... PASS).
- fn1's ACL2 world does not load in this tree (stale certs); fn1 bytes come from its fixture files and definitions.
- Test dispatchers (fn2-layout-test-dispatch-events) hard-error on an undeclared layout: teeth must use a declared layout.
- must-fail on defport needs :expected :hard; defcarrier refuses soft.
