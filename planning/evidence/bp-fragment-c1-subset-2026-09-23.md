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

The host does not call either new helper. A bounded fast reassembler with
all-input reference equality, principal/coherence active-set partitioning,
whole-parent restoration, machine-level N09/N10, and native malformed-input
behavior remain open for C1/C2. This record makes no DTN readiness claim.
