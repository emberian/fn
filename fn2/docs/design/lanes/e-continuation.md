# layer E continuation (the E seat's notebook; rewritten whole after every commit)

## Built (dev)
- E3 (6187c6aa0): fn2/docs/e-surface.md; books/port.lisp, consumer-port.lisp, consumer-model.lisp, owed-consumer.lisp; tests/consumer-mini.lisp, consumer-helm.lisp, port-unit.lisp.
- E3b (5be98c474): books/layout.lisp big-endian kinds :u16be :u32be :u64be (:octets16 n) (:octets32 n) = codes 12-16 (main ruled E builds, B reads the diff; (:fixed n) dropped: the FNCT trailer is computed, not a field; :octets32 added for fn1's kind 6/18 four-octet prefixes); teeth in tests/layout-unit.lisp, layout-roundtrip.lisp campaign rotates a BE layout. books/consumer-codec.lisp (FNCT, fncu v1/v2, k4 codes 0-18, replies 5/6/9/28, items, the code->verb table asserted against port + both carriers). tests/consumer-codec-unit.lisp (fn1's .fncu vectors read from tests/fixtures/consumer-position/, fn1 payloads/refusals, BLAKE3 KAT, served codec agreement). Carriers rebound to port codes (register 14 ... status 18).

## Owners' answers (all in e-surface.md §11): C's fn2-outcome/withdrawals forms; D's block amendment (static :max); D7 rows sent (wait-row, subscription-edge with :esub profile key, new :durable-octets kind); B's record kinds via envelope header.

- §13 peering/BP stated, revised after Astra-2 (lanes/e-quests/astra-2.md; §16); seams sent to main (D :peer-credit, D5 3/n table, exhaustion split, TAKETHIS 400 default + fn-compat; C obligations contract, cancel intent, feed-work, bundle schemas, admission ordinal; B ADU subject, evidence identity across import).

- E4a (8754482a1): books/peer-model.lisp (8 faults), owed-peer.lisp (K-P1, K-P3a, K-P4, K-P5, K-P6), tests/peer-witnesses.lisp (W1 W2 W3 W7 offer F1 F2); port.lisp registers (:port P) via fn2-declare (declare.lisp: fn2-ports), per the form seat.
- Layout campaign with :octets32: PASS. Whole-tree recert at 5be98c474 stopped on a machines-a hash race (tree moved under the run), not E's change.

## Next
1. Remaining §13.8 matrix as the records land: W4, W5 (authority dependencies), W6 (cancel intent, C), W8-W10, F3-F7.
2. Owed codec pieces with their first sender: fn1 kind 18 (1-based enum), FNWD/FNRB forms; the evidence page codec (§13.4).
3. Served fn2-cns + XFNC rows (D's block declaration landed in grammar.lisp? check) + D8 edge rows (mine, new machine form after P2-P4) when D5 2/n and D6 land; K10; K-P2/K-P3b over D5 3/n.

## Pitfalls / commands
- REPL: `python3 tools/acl2 --timeout 400 < build/e-seat/<x>.lsp > build/e-seat/<x>.out 2>&1` (drivers: codec.lsp, cct.lsp, mini2.lsp, helm.lsp).
- Certify: `sh fn2/tools/certify.sh books/consumer-codec.lisp tests/consumer-codec-unit.lisp ...`; whole tree: `sh fn2/tools/certify.sh $(cat build/e-seat/all-certs.txt)` (detached, PID file).
- Layout campaign: `python3 tools/acl2 --timeout 900 < fn2/tests/layout-roundtrip.lsp` (detached; prints LAYOUT ROUNDTRIP ... PASS).
- fn1's ACL2 world does not load in this tree (stale certs); fn1 bytes come from its fixture files and definitions.
- Test dispatchers (fn2-layout-test-dispatch-events) hard-error on an undeclared layout: teeth must use a declared layout.
- must-fail on defport needs :expected :hard; defcarrier refuses soft.
