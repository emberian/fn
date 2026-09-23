# BP fragment C1 subset, 2026-09-23

Source: branch `implement/fragment-refinement` from `df5097b6`; certification
manifest [`certify-20260923T142214Z-561566.json`](manifests/certify-20260923T142214Z-561566.json)
captures each source digest. The lane's seven selected roots passed on
persvati under ACL2 8.7 / SBCL 2.6.8, executable
`/home/ember/fn-gates/toolchains/w25/acl2-literal` (SHA-256
`346b7ee183e8c291cb61cf31be75a332caf329fa74b4995921cbb224208f2c08`),
toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`.
Invocation: `python3 tools/farm.py submit persvati --remote-root
/home/ember/fn-gates/takeover-fragment-refinement --acl2
/home/ember/fn-gates/toolchains/w25/acl2-literal --jobs 2` with roots
`books/bp-fragment`, `books/bp-fragment-invariants`,
`books/bp-fragment-fast`, `books/bp-limits`, and their three test books.
Run `run-20260923T142210Z-d01c` installed 69 cached dependencies and
certified seven roots in 6.039 seconds of certificate time. No book exceeded
2.36 seconds. `make check` and `green_check --changed-since df5097b6`
passed after adding the four new roots to the Makefile.

`fn-bpf-fragment-fast-is-fragment` proves total equality for every payload and
boundary list, including `(:invalid :bounds)`. It relates the cursor cutter
to the reference's indexed extents through `fn-bpf-cut-fast-is-cut`. The cutter
traverses each emitted segment once for the prefix and once to advance the
cursor, plus the existing validation of lengths and boundary order; this is a
source-level work bound, not a native timing measurement. The positive three
fragment witness and two malformed-boundary examples are in
`bp-fragment-fast-tests`.

`fn-bpn-limits-compose` proves ADU/reassembly equality at 65538 octets, that
the current image cap leaves 65534 octets beyond an ADU, that the lifecycle
payload cap leaves 3072 beyond an image, and that 64 maximum images fit the
current aggregate byte cap. It does not prove that any actual encoded bundle
fits; the machine checks its length. Explicit header, family stage-slot and
stage-octet fields are not implemented yet, so those planned relationships
remain open. `fn-bpf-refragment-block-unfolds` proves the helper's offset
addition, total preservation and ADU-key copy for all inputs; it is a
definition-level fact, not a keystone with removable hypotheses. The N09
example exercises a valid fragment parent, successful local cut and retained
extent. The impossible whole-parent negative fixture is not used.

The follow-up source certified under
[`certify-20260923T144031Z-727033.json`](manifests/certify-20260923T144031Z-727033.json)
on the same persvati toolchain. `farm.py submit persvati --affected-by
books/bp-fragment.lisp --jobs 2` selected exactly seven affected roots and
run `run-20260923T144024Z-cae4` passed all seven in 7.028 seconds of
certificate time. The longest book took 3.117 seconds. The selected closure
does not contain `bp-node-machine`: that machine has no fragment include yet.

`fn-bpf-reassemble-fast-is-reassemble` proves exact equality for all inputs,
including invalid bounds, least conflict position, first contiguous gap, and
successful bytes. The scanner makes at most three position traversals, each
position probing at most 64 fragments, after input validation; it avoids
canvas allocation for conflict and missing outcomes. Its guard is verified.
`bp-fragment-fast-tests` exercises a complete cover with the nonzero-offset
fragment first, byte-identical overlap through the earlier reference tests,
conflict before gap, a reported gap, total zero, and an extent past total.
This is a source-level work bound and equality proof, not native timing
evidence or the planned sorted-interval implementation.

`fn-bpf-whole-fragment-primaries-restore-parent` is the restoration keystone:
for a valid whole primary, each child made by the primary mapper reconstructs
that primary. The stronger theorem needs only block shape and absence of the
fragment flag. Its test book has a full-antecedent successful-cut witness;
dropping whole-parent uses a valid fragment parent with a retained extent and
fails restoration, while dropping block shape uses a malformed logical value
and also fails. The successful-cut statement
`fn-bpf-whole-parent-fragments-restore-parent` is a corollary of that
keystone. There is no impossible negative fixture for the re-fragmentation
helper's redundant whole-parent exclusion.

The inverse and consumed-fragment agreement extension was certified on the
same persvati ACL2 8.7 / SBCL 2.6.8 toolchain with two affected roots. The
invariant root passed in `run-20260923T145023Z-08fa`; its test root initially
stopped on a negative-index tooth evaluated under `nth`'s guard. After making
that out-of-guard logical test explicit, `run-20260923T145116Z-91e2` passed
the test root. The final manifest is
[`certify-20260923T145120Z-820946.json`](manifests/certify-20260923T145120Z-820946.json),
whose cache provenance identifies the matching invariant certificate; the
first manifest is
[`certify-20260923T145027Z-812592.json`](manifests/certify-20260923T145027Z-812592.json).

`fn-bpf-fragment-then-reassemble-is-identity` states that every successful
fragmentation of an octet payload at valid boundaries reassembles to that
payload, and uses the complete agreeing-cover keystone through proved input
shape and coverage lemmas. The test has a successful three-fragment witness and a
malformed terminal-cut counterexample when success is dropped.
`fn-bpf-reassemble-ok-agrees-with-every-fragment` proves that every byte of
every member fragment equals the corresponding byte of a successful output.
Its proof carries member shape, common total, index bound and octet facts to
the pointwise canvas argument; the test uses an actual overlapping cover and
counterexamples for dropping each of `:ok`, membership, natural index, and
index within the fragment. These are reference-function theorems; the
all-input fast/reference equality transports their results to the fast
implementation.

The host does not call either new fast function. Principal/coherence
active-set partitioning, machine-level N09/N10, and native malformed-input
behavior remain open for C2. This record makes no DTN readiness claim.
