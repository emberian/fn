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
