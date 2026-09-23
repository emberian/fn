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
replacement, and proactive forwarding fragmentation remain open.
