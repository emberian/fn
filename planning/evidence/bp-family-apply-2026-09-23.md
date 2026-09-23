# Pure kind-18 application checkpoint

`fn-bpnf-family-apply` recomputes the C2 active set from the current held
list, requires one exact anchor arrival and the caller's expected whole
arrival, compares the protected record's whole wire to the bounded fast
reassembly plan byte for byte, and replaces only that selected set with a
whole held row. The whole row copies the offset-zero fragment's ingress and
age anchor. Tests retain a different principal and a different coherence
family, reject a repeated anchor arrival, a wrong frontier, and altered
whole bytes. This pure rule is not yet a live `fn-bpnf-step` transition or
the native service caller; publication, ordered replay, and a durable
arrival frontier are still required.

ACL2 8.7 on hbox, toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
certified the book and initial test in `run-20260923T213734Z-de2b`, manifest
`planning/evidence/manifests/certify-20260923T213742Z-219152.json`; the
additional duplicate-anchor tooth passed in `run-20260923T213906Z-fba1`,
manifest `planning/evidence/manifests/certify-20260923T213914Z-222089.json`.
`make check` passed. The ready-shape theorem is scoped to the pure rule;
it does not establish byte replay or physical publication.
