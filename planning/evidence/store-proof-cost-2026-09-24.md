# Store proof iteration cost, 2026-09-24

This is a proof cost change with unchanged executable definitions, theorem
statements, and tests. In `books/store-node-invariants.lisp`, two consumer
completion proofs now keep the whole Store-state and pending recognizers closed;
their conclusion follows from the completion gate and the consumer event arm.
In `books/store-node-traces.lisp`, a local projection lemma reduces the files of
the host-called `fn-sn-io` to the actual `fn-sn-file-step`, including the derived
event-index update. The existing records-prefix theorem then proves the file
kernel property without opening consumer index insertion or its bounds codec.

The before run is the combined hbox manifest
[`certify-20260924T033144Z-795753.json`](manifests/certify-20260924T033144Z-795753.json)
from source `8c61c098`. The after run is the two-job incremental hbox run
`run-20260924T042327Z-aa3c`, with archived manifest
[`certify-20260924T042336Z-883128.json`](manifests/certify-20260924T042336Z-883128.json).
Both used ACL2 8.7, SBCL 2.6.8 and
`/tank/fn/toolchains/w28/acl2-literal-4g` (qualified identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`).
The 77 source digests in the after run that overlap the before manifest differ
only for these two edited books. The after source digests are
`0b573bcf958aa3f4ebeced9b33fc5e3c3482d38dea0ab2b0449a2be7b5aacb09`
for invariants and
`122adf4b26c399664d3d035d1995272b4995a26b35bcd80f15b803453ee89249`
for traces. This comparison holds toolchain and dependency source constant;
shared-box scheduling and per-process setup can still affect wall time.

| Book | Before wall time | After wall time | Key proof event before → after |
| --- | ---: | ---: | ---: |
| `books/store-node-invariants` | 111.945 s | 86.919 s | consumer idle 15.98 → 6.20 s; replay non-nil 16.88 → 6.69 s |
| `books/store-node-traces` | 77.061 s | 52.013 s | `fn-snt-io-records-prefix` 27.73 → 7.24 s |

The pinned hbox `proof_repl.py` session admitted the new local projection in
0.00 s and the unchanged prefix theorem in 9.40 s. It admitted the two
unchanged consumer theorems in 7.28 s and 7.37 s. Both sessions were stopped
before the farm run. The farm certified both changed books and
`tests/acl2/store-node-tests`, `tests/acl2/store-node-traces-tests`, and
`tests/acl2/store-node-teeth-tests`; all five requested roots passed, as did
two additional needed dependencies. `make check` passed after regenerating the
ledger. This is book and test certification at these bytes, not an integrated
image or runtime qualification.
