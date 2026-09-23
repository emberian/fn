# Finite C2 fragment-family query, 2026-09-23

Source: `implement/fragment-family` from integrated C1/foundation base
`bf132fae`. The changed-book run on persvati was
`run-20260923T165142Z-485b`, jobs 2, with executable
`/home/ember/fn-gates/toolchains/w25/acl2-literal` (ACL2 8.7 / SBCL 2.6.8,
toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`).
It installed 30 matching books from three cache origins and certified the
two affected roots, `bp-node-fragment-family` and its ACL2 test book, in
the incremental run. Both passed; the exact source and dependency digests
are in [`certify-20260923T165148Z-1868140.json`](manifests/certify-20260923T165148Z-1868140.json).
The reachability repair changed only the test book; incremental
`run-20260923T165548Z-b78c` reused 31 matching books and certified that
test at its final bytes. It passed under
[`certify-20260923T165550Z-1905489.json`](manifests/certify-20260923T165550Z-1905489.json).
An earlier discovery run, `run-20260923T164720Z-2c80`, certified the initial
query book and test plus an uncached foundation dependency under
[`certify-20260923T164726Z-1828214.json`](manifests/certify-20260923T164726Z-1828214.json).

`fn-bpnf-active-set` reads `fn-bpnf-held-list` from the finite A1 machine,
requires its anchor to be a current held fragment, and includes only rows
with the same admitted ingress principal, ADU key and primary-header
coherence key. The key includes total ADU length, destination, report-to,
lifetime, CRC type and flags other than the fragment flag. Deleted rows and
rows with the query's `:reassembly-consumed` marker are excluded. The latter
is a convention here, not an A1 transition. The keystone
`fn-bpnf-active-set-members-share-family` proves every selected row meets
those predicates; the test has valid P and Q held records with the same ADU
key, an altered-lifetime P record, and explicit contradictory bytes showing
why dropping principal equality changes a successful cover into
`(:conflict 4)` and dropping coherence changes it into `(:conflict 6)`.
Same-principal conflict rows use distinct RFC bundle IDs, so A1 reception
classifies them `:fresh` rather than refusing an identity conflict. The test
similarly separates deleted and consumed exclusion and refuses a phantom
anchor.

`fn-bpnf-fragment-query` projects those exact held bundles into fragment
cells and calls the proved fast reassembler. Its all-input correspondence
theorem equates it to the reference reassembler over that projection,
including `(:invalid :bounds)`. An active same-principal conflicting row
produces `(:conflict 4)` in the test; compatible overlap succeeds. The
coverage lemmas prove that `:ok` entails a selected offset-zero source, and
the source-member theorem proves that source belongs to the active set and
has offset zero. The reachable N10 fixture places the nonzero-offset row
first in held order and confirms that the later offset-zero row supplies
the source. `fn-bpnf-receive-proposal-preserves-fragment-query` relates the
query to the actual A1 `fn-bpnf-step`: a receive proposal leaves its answer
unchanged until durable publication installs a row; the test takes the
`:persist` branch with a valid bundle and ingress.

This is a read-only contract over the real finite held schema. No host calls
the query yet. A2/A3 must add journalled family replacement, replay,
retirement, versioned waits and final-delivery conservation before a T4
machine theorem or native delivery claim. No native image or deployment was
used for this evidence.
