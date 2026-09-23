# Checkpoint auxiliary recovery, E2 and T10 (2026-09-23)

The source packet starts from E2 model commit `9c89c40e`.  The selected
`fn-cc` format-zero pack still stores exact event bytes from dense sequence
zero.  `fnn-pack-recover-records` expands that prefix with the physical suffix
before authoritative Store reopen.  The node-only checkpoint remains a
private diagnostic restore, not a replacement for the live Store.

`books/checkpoint-auxiliary.lisp` adds a version-one recovery-only comparison:
`fn-cpa-auxiliary-of-history` independently replays historical authorship
verdicts, keyring snapshots, completed dense sequence, and the E2 consumer
projection from the reopened Store's exact event list;
`fn-cpa-store-auxiliary-agrees` compares all four with the carried fields.
`host/checkpoint-host.lisp` is the native caller bridge, invoked after the
existing selected-checkpoint node differential in `host/native/checkpoint.lisp`.
Mismatch is corruption.  This check scans the Store only during recovery.
`fn-cpa-rollover-proposal` separately derives the next E2 rollover event's
sequence and transaction coordinates from the recovered Store, accepting only
a bounded caller-supplied fresh incarnation ID.  It is a proposal, not a
durable event or an implemented clone command.

The ACL2 test includes a selected pack with bootstrap, article, snapshot,
and an unbound standalone verdict at sequences 0–3, plus a physical rollover
suffix at sequence 4.  It asserts exact expanded bytes, dense sequence 5,
fresh incarnation, retained snapshot, and that the unbound verdict gains no
historical authority.  A separate packed keyring plus bound hybrid composite
reopens with one historical verdict and its enrolled snapshot; its supplied
`:verified` observations are abstract constructor inputs, not native
cryptographic evidence.  Mutating each of consumer projection, verdict list,
snapshot list, or dense sequence makes the comparison fail.  Same-incarnation
and malformed rollover proposals are refused.

Scoped certification: `python3 tools/farm.py submit persvati --root
/Users/ember/dev/fn/build/lanes/preservation-contract --remote-root
/home/ember/fn-lanes/preservation-contract-e2 --jobs 2
books/checkpoint-auxiliary tests/acl2/checkpoint-auxiliary-tests`, farm run
`run-20260923T194939Z-7b04`.  Archived manifest:
`planning/evidence/manifests/certify-20260923T194947Z-3573782.json`.
ACL2 8.7, SBCL 2.6.8, toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`;
status passed, 52 dependency books installed from two cache origins and 15
books certified in 71.811 seconds, including both requested roots.  Their
source SHA-256 values are `15063462f27dc12c0a1fc2048911174f0ccc870f992c1e97f5546e9d8239818e`
and `2d1ede7780268ea82ae4f773538c7c962b5aa6bc88f0ece5ad247661ebaaa487`;
the manifest records identical before/after digests.  `make check` passed
after the generated ledger refresh.

This is a source-pinned ACL2 reconstruction and native caller change, not a
combined saved-image witness.  It does not prove a general auxiliary
checkpoint-plus-suffix equality theorem; the existing exact-prefix pack
theorem establishes byte preservation, while this packet tests the composed
reopen and checks equality at recovery.  Guard verification for the new
diagnostic functions remains open.  A safe writable clone/restore still needs
the documented pre-open fence, cold copy, durable rollover publication, and
post-reopen verification; no copied directory may be treated as activated.
