# Remote consumer execution handoff

Checkpoint: `7e67fcb59` on `codex/consumer-remainder`, incorporating
origin/dev `82abb52dd`. Exclusive worktree:
`/Users/ember/dev/fn/build/lanes/gpt61-consumer-remainder`.
No implementation WIP or running proof/native jobs remains. The parent
assigns Sol execution; architectural synthesis stays with the designated
Astra reviewer. Full PKT-255/PKT-673 scope remains open.

## Implemented contracts

- `e6d11b780`: distinct FNCR request envelope, all eight operations, explicit
  login/secret, no client authority versions, protected-channel observation.
  Protocol parsing does not establish authentication or TLS.
- `4442f3d23`: CP local8 and remote10 entries. Remote fields8/9 are canonical
  group octet lists/account incarnation. Operation9 is
  `(tag consumer principal query qver view epoch groups account)`.
  Atomic register/rebase retains exact definition and ACK preserves it.
  A metadata change requires explicit rebase/fresh epoch even if opaque query
  ID and version compare equal. CP state remains six fields.
- `fn-cpe-operationp` still refuses remote tags. This is intentional: no
  underfunded durable write is enabled by the logical kernel extension.

See the exact source hashes/checks in
[evidence](evidence/consumer-remote-components-2026-09-30.md). All source ACL2
definitions, guards and theorems of the changed kernel were admitted; codec
22 assertions, remote kernel20 and original kernel88 forms passed. No
certification manifest, native verdict, image or deployment is claimed.
Upstream integration did not alter those five hashed source files.

## First Sol execution increment: durable event and actual charge

The next complete implementation increment spans CPE codec, profile admission,
constructor carries, Store projection and durable host publication. Keep the
outer event5 `(:consumer sequence txid generation operation)` and operation9
above unless architectural review identifies a concrete incompatibility.
Encode immutable groups separately from fixed-width cursor IDs, with exact
versioned decoding and representability checks. Preserve the existing local
codec/profile behavior; a supported profile must fund every admitted query.
Do not replace the old512 reservation with a u32 maximum: wire width and
actual funded publication size are different conditions.

Required event-sensitive gate: an ACL2 constructor returns the proposed event
and its verified wire charge and canonical-tree carry. The group-definition
parser/construction step maintains its child carry within the funded quantum;
there is no second full query/history walk before publication. The gate charges
one history row and the actual publication figure, and proves the existing
retention/release debt headroom still holds after that charge. It runs before
`fnn-advance-frontier` in `fnn-owner-consumer-commit`. A refusal creates no
registration/query/ACK effect; after persistence ambiguity normal recovery
fencing and uncertain outcome apply.

Integration points:

- `books/consumer-store-events.lisp`: fixed512 `fn-cpe-max-octets`, exact event
  grammar, encode/decode and projection step. Keep parsing work bounded.
- `books/store-events.lisp`: current `:consumer` publication ceiling.
- `books/store-profile-carried.lisp`: `fn-pvc-verdict-at` does both admission
  and post-publication `fn-pvc-roomp` with `fn-cvec-debt-step`; actual charge
  must preserve both. Identity statement verdict is a useful existing pattern.
- `host/owner-host.lisp`: a new event-sensitive consumer verdict analogous to
  `fn-owner-identity-publication-verdict`; consume established carries.
- `host/native/owner.lisp`: replace kind-only preflight with that ACL2 verdict,
  preserve the durable prepare/publish/finish boundary and all death cuts.
- `books/store-node.lisp`: existing prepare/finish/replay apply exact consumer
  projection. Coordinate with current owner proof assembler; do not overwrite
  `fn-owner-prepare-consumer` extraction or assume its relation is discharged.

The exact size-carry constructor API and owner allocation remain an integration
dependency, not permission. Size owner previously received the exact schema;
a latest transfer message failed delivery because the agent limit was reached.
Parent should route its current API to the Sol successor.

## Architectural contract requiring cross-owner review

Current account authentication and durable view generation are not implemented.
The following requirements constrain the remaining design; they are not a
claim that a selected producer or proof already exists.

1. Every operation and WAIT resumption resolves the explicitly named current
   account, verifies that account's credential in ACL2 and derives principal
   and account-incarnation binding from committed context. Equal passwords
   on two accounts do not authorize switching the named account's consumer.
   The existing login-derived `fn-acct-local-principal` is insufficient as an
   incarnation. Redeemed account rows carry an invite identity, but an account
   scheme must also cover supported static configuration credentials and
   deletion/recreation. Choose a durable creation identity for each admitted
   account form; do not silently make remote access redeemed-only.
2. The view identity is derived from durable state and changes when visibility,
   group/control policy or account authority can change which old events are
   observable. Ordinary appended article events do not change it. Revocation
   must refuse before article lookup or ACK mutation even while an old WAIT
   remains open. Rebase is explicit and begins scanning at zero; old scope
   tokens fail afterwards. A configuration generation alone omits control/
   withdrawal visibility transitions. Snapshot lease/epoch is not authority.
3. Recommended design shape for review: a scalar view watermark in the carried
   consumer/authority projection, updated atomically by every relevant durable
   Store completion and the corresponding replay fold. It may use a persisted
   publication coordinate only if ordering, representability and uniqueness
   across recovery are proved. Otherwise choose an explicit versioned scalar
   and exhaustion behavior within the supported codec/profile. Enumerate the
   transition cases before choosing; a process-local counter cannot suffice.
4. Recovery/snapshot must preserve exact account/query/view metadata, and
   compaction must retain the existing-prefix position mapping. Restore either
   establishes that mapping or durably changes history/incarnation and forces
   explicit rebase. Never infer missing appended fields as authority. Current
   local8 and remote10 shapes are distinct, not a migration fallback.

Owner/view assembler `/root/astra_owner_view_union` received a review request
for the durable scalar versus existing-coordinate choice. Snapshot/architecture
owners confirmed generic consumer projection tree preservation; complete CP
fold congruence still belongs to the recovery owner. Mandatory article12/held16
binding fields remain owned by the durable binding lane and must be preserved.

## Following execution increments and closure

After the coherent persistence/authority contract, implement the separate TLS
listener and actual host-called wrappers; never forward to owner/admin FNCT.
Derive query versions server-side, use exact immutable group membership, emit
an overlapping crosspost once, and preserve unavailable-gap continuation.
Use resumable concrete cursors with the named refinement and carried invariant.
Run reachable complete-positive/hypothesis-removal teeth at actual host-called
subjects, including account/password alias, revocation, visibility reveal of
old events, stale ACK, restore/compaction and persistence failures.

All six original Q13 rows remain in the lane LANEDUMP. The BP466(c) signed
actual `fn_consumer` composition stays assigned to this lane; no unsigned
fallback. Runner owns narrow matching convergence certification/native/image
evidence. Parent/runner regenerates ledger/current-view for the integrated
source; this lane does not fabricate manifest coordinates.
