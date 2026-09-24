# BP fragment family node cut, 2026-09-23

`fnn-bps-foundation-step` calls `fn-bpnf-fragment-step` in the one FNBS
service handle. Its `:family` proposal uses the principal/coherence C2 query
and exact post-replacement resource budget without changing held rows. Only
an ACL2-authorized, durable kind-18 publication replaces the selected rows
with the reconstructed whole; refusal retains fragments and uncertainty
fences ordinary steps. The same `fn-bpnf-family-apply` rule checks ordered
kind-5/7/18 byte replay. A separate state-owned arrival frontier survives
row retirement and is reconstructed by replay. The whole row retains the
offset-zero source's ingress and age anchor. The A3 Store selector still
rejects every fragment until the whole row is durable.

The focused hbox ACL2 8.7 / SBCL 2.6.8 incremental run
`run-20260923T220418Z-31b7` passed ten requested roots using two jobs and
the exact source digests in
`planning/evidence/manifests/certify-20260923T220426Z-279021.json`. Six
matching roots came from the cache; four current roots were certified in
this run. Tests cover nonzero-offset-first replacement, retained source rows
before publication, exact replay order, wrong bytes/frontier/anchor,
publication refusal, and uncertainty fencing. This is ACL2 behavior evidence,
not a native interrupted-contact verdict. The native fixture is present but
requires a saved image at these source bytes. Fragment-step guard closure,
kind-10 conflicting-fragment deletion, retransmission correlation after
replacement, and proactive forwarding fragmentation were open at that
checkpoint.

The subsequent current-source guard packet closes `fn-bpnf-fragment-step`
and its family plan/apply transition without adding a served-path recognizer.
The fragment guard book's expensive primary shape proof now composes existing
bundle, block, and flag facts; a narrow selector bridge connects the plan's
`car`/`cadr` theorem to the apply guard's total selectors while the plan body
stays closed. On the hbox ACL2 8.7 w28 toolchain, `books/bp-node-fragment-guards`
certified in 10.139 seconds in `run-20260923T234049Z-82be`. The later
[six-root matching-source qualification](manifests/certify-20260923T234638Z-525382.json)
passed the fragment and report guard books and their requested tests with
two jobs and a 180-second per-book bound; the unchanged fragment book and
tests were loaded from matching cache. This proves ACL2 guard compliance at
the current union bytes. Native interrupted-contact, conflicting-fragment
deletion, retransmission correlation, and proactive fragmentation remain open.
