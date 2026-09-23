# K0 allocator entry and file-fence prefix

`host/native/io.lisp:1469` calls `fn-store-metadata-frontier-next` and
`fn-store-metadata-frontier-frame` before `fnn-write-staged`, `fnn-replace`,
and the root-directory fsync. `host/store-host.lisp` now routes the frame
and decoder through the public `fn-bs-frontier-encode` and
`fn-bs-frontier-decode` functions. Their concrete byte codec is installed by
the checked `defattach` in `books/byte-store-frame.lisp`; a live ACL2
evaluation returned identical public/concrete octets for frontier 2 and
decoded 2. The host still checks that the result is an octet list before I/O.

`fn-bs-k0-host-frontier-arguments-are-typed-input` derives the input contract
from an ACL2 ready state, a matching current frontier, a non-NIL ACL2
successor, a staging name and the host's checked octet result. The public
codec round-trip constraint supplies the decoder equality. For any byte
state satisfying `fn-bs-statep` and a fresh staging name,
`fn-bs-k0-frontier-file-cut-is-write-fence` identifies actual P-FRONTIER pair
5 with the successful create/write/file-fence transition;
`fn-bs-k0-frontier-file-cut-has-exact-frame` proves that the newly allocated
inode's durable bytes are precisely the supplied frame;
`fn-bs-k0-frontier-file-cut-source-is-new-inode` keeps the staging lookup; and
`fn-bs-k0-frontier-file-cut-kernel-is-file-observation` identifies pair 6's
kernel state. The test runs a second allocation after an acknowledged first
article and checks retained durable records. Occupied staging, wrong
frontier frame and exhausted successor are negative cases.

Selected hbox certification of `books/byte-store-record-provenance` and
`tests/acl2/byte-store-record-provenance-tests` passed under
`run-20260923T231602Z-6abd`; original requested-root results, exact source
and dependency digests and toolchain identity are archived in
`planning/evidence/manifests/certify-20260923T231604Z-451017.json`.
After strengthening the witness with an explicit staging lookup and malformed
frame negative, the unchanged book root was installed from that exact source
cache and the test root recertified under `run-20260923T231721Z-3dbd`, with
original test result in
`planning/evidence/manifests/certify-20260923T231724Z-454308.json`.

The successful root rename/fence transition has not yet been proved to
preserve `fn-bs-store-relation` for arbitrary retained history. An attempted
direct file-cut relation proof expanded the recognizer too early and left a
staging lookup subgoal: it needs a named staged-file shape lemma before
relation assembly. No all-cut K0 or physical power-loss guarantee follows
from this packet. The native wrapper routing will be exercised in a later
combined image, since the frozen image predates this source change.

The next finite packet proves that allocator pair 5 is a well-formed byte
state and has the same byte transition as P-RECORD's successful staging
prefix. It then reuses the already certified old-authority lemmas to show
that every prior inode except the fresh one retains exact durable content,
the durable directory table is unchanged, and the old frontier and config
authority are untouched. The second-allocation witness checks the carried
first article's raw content as well as the config/frontier; a negative case
at the newly allocated inode separates old-content preservation from the
new file. These facts are prerequisites for the complete retained-record
list and root-rename/fence relation, which remain unproved.

Both selected roots passed on hbox under `run-20260923T232425Z-a748`;
original requested-root results and exact source/closure/toolchain digests
are archived in
`planning/evidence/manifests/certify-20260923T232428Z-471521.json`.

The retained-history step is now proved for the complete durable record
list. `fn-bs-k0-frontier-file-cut-keeps-durable-records` derives exact
per-transaction pathname and raw-octet equality under authority-known and
next-ino separation, inducts `fn-bs-txn-prefix-agreesp`, then applies
`fn-bs-read-records-under-agreement`. It does not assume the desired scan
result or the output relation. The prior acknowledged article is present in
the positive fixture. A well-formed byte state with a dangling old
transaction entry aimed at the next inode is a negative witness for the
authority-known relation premise at the raw-content step: the allocator
changes the old path's bytes in that state. The public kernel observation
leaves byte pair 6 identical to pair 5.

Both selected roots passed on hbox under `run-20260923T233152Z-215d`;
original result, source/closure digests and toolchain identity are in
`planning/evidence/manifests/certify-20260923T233154Z-493643.json`.
The root rename, successful directory fence and full reserved-pair relation
are still open.
