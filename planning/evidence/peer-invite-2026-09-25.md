# peer-invite: invitation binding on dev (PRF-097, 2026-09-25)

Dev lane `lane/peer-invite` from `dev` `1b2619ec`, theorem 1 of
[the spike record](spike-peering-2026-09-25.md) ("Invitation binding"),
re-implemented in `:logic` mode with guards. The spike is the specification;
no spike code is carried. Spec: [peering §9](../../specs/peering.md#9-peering-invitations-issue-accept-confirm-prf-097);
requirement NNT-014; scenario SCN-052.

## What was built

- **The invitations slot** (`books/config.lisp`): the configuration value's
  ninth slot, one row per issued invitation keyed on its nonce, never
  removed. Delta kinds `:issue-invitation` (13) and `:consume-invitation`
  (14) (the next free codes after C2's 11 and 12). This replaces the spike's
  `invitations.json`: a row is durable exactly when its configuration record
  is (the assured reconfiguration path) and replay reproduces it. The brief
  asked for "a Store record kind"; the configuration record is the Store's
  own record for operator state, and it gives the confirm path one
  publication with an existing admission, replay and live-completion proof.
  A new `fn-store-event-p` kind was not taken: it would reopen replay's
  dispatch in ~25 books for a record that carries no article.
- **`books/peer-invite.lisp`** (prefix `fn-pinv-`): document rendering; the
  body parser `fn-pinv-field` and its line specification
  `fn-pinv-body-names-p` (`fn-pinv-field-is-a-body-line`); the shared checks
  `fn-pinv-document`; `fn-pinv-issue-plan`; `fn-pinv-accept-plan` and the
  owner's `fn-pinv-accept-step`; `fn-pinv-acceptance-source`;
  `fn-pinv-confirm-plan` and `fn-pinv-confirm-step`; the genesis identity
  `fn-pinv-genesis-principal` (`fn-prin-id` of Ed25519 || ML-DSA-65 and a
  token); the control codec for requests 9, 10, 11.
- **Operator verbs** `peer genesis|invite|accept|confirm`
  (`books/native-operator.lisp` `fn-nop-parse-peering`, native action
  `:peering`), executed by `host/native/peer-invite.lisp`, which does I/O
  only: key files, CSPRNG nonce and token, wall clock, the two primitive
  observations (`fnn-hsig-observe-raw`), signing the preimage ACL2 builds,
  files and the control socket. The owner's three handlers wrap
  `*fnn-hybrid-control-handler*`; `host/native/hybrid-control.lisp` is
  untouched. `host/native/admin.lisp`'s live publication body is now
  `fnn-owner-live-reconfigure-locked`, called by the admin arm and the two
  peering arms (its source test updated to the same event order).
- `fn-hl-next-generation` (`books/hybrid-lifecycle.lisp`) is byte-identical
  to lane/peer-keys' definition, same place and comment.

## Theorems (books/peer-invite.lisp) and the host lines that call the subjects

| keystone | subject | host caller |
| --- | --- | --- |
| `fn-pinv-accept-step-enrols-only-a-bound-invitation` | `fn-pinv-accept-step` | `fnn-pinv-owner-accept` (host/native/peer-invite.lisp) |
| `fn-pinv-issue-plan-records-the-signed-invitation` | `fn-pinv-issue-plan` | `fnn-pinv-owner-issue` |
| `fn-pinv-confirm-consumes-only-a-pending-named-invitation` | `fn-pinv-confirm-plan` | `fnn-pinv-owner-confirm` |
| `fn-pinv-confirm-step-enrols-only-the-consuming-acceptance` | `fn-pinv-confirm-step` | `fnn-pinv-owner-enrol-confirmed` |
| `fn-pinv-confirm-after-its-consumption-enrols` | `fn-pinv-confirm-plan` after `fn-cfg-apply-delta` | the crash point in `fnn-pinv-owner-confirm` |
| `fn-pinv-confirm-step-never-enrols-twice` | `fn-pinv-confirm-step` | `fnn-pinv-owner-enrol-confirmed` |
| `fn-pinv-consumed-stays-consumed-across-replay` | `fn-config-replay-loop` | open (configuration replay) |
| `fn-pinv-consumed-refuses-consumption`, `fn-pinv-consumption-consumes` | `fn-cfg-delta-reason`, `fn-cfg-apply-delta` | `fn-ocfg-step` via `fnn-owner-live-reconfigure-locked` |

Statements, in words (the book has them exactly):

1. **Accept.** An `(:enrol EVENT)` from `fn-pinv-accept-step` has EVENT the
   kind-3 enrolment (`fn-hl-enroll-event`, at `fn-hl-next-generation`) of
   exactly the carrier's principal P and key set K, P not already enrolled
   with K, and `fn-pinv-bound-document-p`: ACL2's `fn-hsig-authorize-at` over
   the carrier decoded from the received octets and the two observations;
   the body has the kind line and the lines naming P and both keys of K; and
   `fn-prin-genesis-bindsp P (Ed25519 || ML-DSA-65) TOKEN`.
2. **Issue.** An issued delta is `fn-cfg-issue-invitation` of the body's
   nonce, the verified principal and the invitation's authored-source
   identity, the nonce keying no row.
3. **Confirm, consumption.** A `(:consume DELTA)` has a bound acceptance,
   the row its nonce keys pending and naming the body's `Inviter-Principal`
   and `Invitation-Source-Id` (both body lines), and DELTA consuming that
   nonce for the acceptor and the acceptance's own source identity.
4. **Confirm, enrolment.** An `(:enrol EVENT)` from `fn-pinv-confirm-step`
   has a bound acceptance, the row consumed (state 1) by exactly its
   principal and source identity, P not enrolled with K, and EVENT the
   enrolment of P and K.
5. **Once only.** A consumed invitation stays consumed through every
   acceptable configuration record (`fn-config-replay-loop`) and refuses
   every `:consume-invitation`; an admitted consumption consumes.
6. **Crash between consumption and enrolment.** After the consuming delta
   is applied and before any enrolment, the same acceptance's plan is
   `:enrol`; once enrolled, the confirm step never enrols again.

"This node's principal" is the principal that signed the invitation this
node recorded (row field b, from the issue plan's verified carrier); the
owner holds no other notion of its own principal.

## Teeth (tests/acl2/peer-invite-tests.lisp)

Witnesses with real rendered carriers, SHA-256 genesis identities and
source identities (crypto-attach, codec-attach), placeholder signatures of
the profile's widths and the observations as inputs:

- accept witness: B's step enrols A at generation 1; the bound predicate holds.
- tampered body (observation `:refused`): refused `unverified`, bound fails.
- body naming another key set: `claimed-keys`, bound fails.
- principal not the genesis identity of the keys: `genesis`, bound fails.
- already enrolled: `already-enrolled`.
- replayed nonce at issue: the plan refuses `invitation-nonce-reused`, and so
  does `fn-cfg-delta-reason` independently.
- confirm witness: `:consume`, the row names inviter and source identity.
- crash point: after the consuming delta, the confirm step enrols B; before
  it, the plan is `:consume` and the step enrols nothing.
- second consumption: `invitation-not-pending`; removal witness: on the
  pending value it is admitted.
- second confirm after enrolment: `already-confirmed`; removal witness for
  "not enrolled": the resumed plan is not `:enrol`.
- replayed nonce by another principal (C): `invitation-consumed`.
- acceptance of another invitation (same nonce, another source identity):
  `another-invitation`, and the row-naming conclusion fails.
- acceptance of another inviter's invitation: `another-inviter`.
- unknown nonce: `no-such-invitation`; an invitation given to confirm:
  `document-kind`.
- control codec round trip, and a wrong kind decodes to nothing.

## Runs

| run | host | scope | result |
| --- | --- | --- | --- |
| `run-20260925T105044Z-4572`, manifest `certify-20260925T105118Z-4150165` | persvati, 2 jobs, 300 s, w25 | `--affected-by` config, hybrid-lifecycle, native-operator, peer-invite: 530 books, 299 certified | 295 passed, 4 failed, none of them this lane's: `books/store-reclaim` (`fn-pb-path-agent` called with one argument, arity changed on dev by the D32 Path change), `tests/acl2/store-reclaim-tests` (its dependent), `books/poster-bytes-buffer` (`fn-pbb-source-index-is-inj-source-of`) and `tests/acl2/octets-stobj-tests`; no changed book is in their include closure's changed set beyond config/lifecycle, and each fails in an event this lane does not touch |

Proof cost at 2 jobs on persvati (same run): `books/peer-invite` 4.6 s,
`tests/acl2/peer-invite-tests` 5.9 s, `books/config` 1.2 s,
`books/config-invariants` 1.0 s, `books/native-operator` 10.1 s (process
wall, 5.5 s of it `include-book native-admin`; a WARNING, not over the
ratchet). The run's other slow books (byte-store-k0*, bp-node-*) are
unchanged by this lane and were measured on a loaded box.


## Not done, and why

- The peer record is still `peer add`: folding it into the consuming
  configuration record (one publication for consume + peer) is open.
- "Acceptance of another invitation" with the same nonce is exercised in
  ACL2 only; natively it cannot be produced without forging a nonce, so the
  native case is an invitation this node never issued (`no-such-invitation`).
- Succession-era invitations (a principal whose current keys are not its
  genesis keys) are refused `genesis`; PRF-098's succession statements are
  the path for those.
- The spike's other deferrals (the `:revoked` token, carried budgets, refusal
  classes, the statement executor, the pull cursor) are other lanes'.
