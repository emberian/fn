# Synthetic Mini consumer operation fixture

These are public bytes from a separate scratch Mini consumer store, not a live
fn fetch or a private Mini database. The input origin package is the sibling
`../package.bin`; the independent origin pin is `../independent-pin.json`.
The operator selected `operator-policy.json` and a current Mini grant for
subject 7, content target 600, capability 61. The fn source identities and
verdict references in the reports are synthetic trusted-test-adapter fields;
they do not establish fn authorship or Store retention.

`report-first.json` and `report-changed-source-same-prestate.json` name the
same application and operation, with different source identities. Both
yielded `proposed-fresh` before either signed call was submitted. The exact
`signed-first-call.bin` installed the binding and `reply.bin`; the separately
prepared `signed-stale-second-call.bin` was refused. After reopening the
store, `decision-repeat.json` returned the original 181-byte reply. With
current roots, `report-changed-source-current.json` yielded
`decision-conflict.json`; `signed-conflict-call.bin` installed separate
conflict evidence. Another reopen yielded `decision-conflict-repeat.json`
and the same original reply. The signed birth call and consumer genesis are
included to identify the preceding synthetic store history. No private key
or SQLite files are included.

The exact native build, outcome IDs, negative cases, bounds, and limitations
are in [the P1 evidence record](../../../../planning/evidence/dregg-e1-consumer-p1.md).
