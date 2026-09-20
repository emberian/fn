# Design summary: the substrate on the wire (wave 7)

Lane `w7/substrate-transport-design`, branched at `72279c8`. Deliverable:
[`specs/substrate-transport.md`](../../specs/substrate-transport.md). No
certification ran; every ACL2 form there is a statement to be proved, using
existing names exactly. It spends the four slots [peering](../../specs/peering.md)
§6 reserved: the `FN-Statement` and `FN-Policy` header fields, the `:statement`
exchange kind, the `(:peer-transit ...)` provenance record, and `(:principal id)`.

## The design in one paragraph

A statement travels as a header field of the article it is about, not as an
article in a reserved group, because RFC 5537 §3.6 protects an unknown header
field through an INN and protects nothing about a separate article — whose
relay depends on a third party's newsfeed configuration, and which can be
dropped, expired or separated from what it signs. `FN-Statement` carries the
base64 of the *detached* encoding (header items plus signature, payload
omitted); the payload is located by the statement's own kind — for `:article`
it is the D01 authored source bytes the receiver projects from the received
octets, for `:policy`/`:succession`/`:receipt` it is the article body. The
canonical octets are exactly `fn-stmt-encode`; the wire adds base64 and folding
above it and changes nothing below it. Acceptance is the one path every article
takes (`fn-peer-transfer` → `fn-node-prepare`/`fn-node-complete`); the statement
layer is a projection recorded in the evidence slot, and the lace is the store
projected, not a second store — so there is nothing to reconcile after a crash.

## The spine: the statement layer never refuses bytes; it refuses authority

An article whose statement is absent, malformed, unverifiable or equivocating
is still accepted, stored byte-exact and relayed unchanged (OBJ-001, D01). What
it loses is every authority-bearing effect: it changes no policy, admits no
post, advances no key, moves no roster. That is what makes the substrate safe
over a transport fn does not control.

## Decisions worth arguing about

- **The lace is derived, not stored.** `fn-stx-lace` projects the accepted
  articles; the bridge lemma `fn-stx-lace-of-accept-is-merge` turns every lace
  keystone into a transit-path corollary. The served path uses an incremental
  index with `fn-stx-index-agrees-with-lace` (D3: never revalidate whole state).
- **Equivocation is accepted, recorded, and refused only as authority.** Both
  forks are kept (`fn-lace-merge-preserves-equivocation`); a durable
  `(:equivocation ...)` evidence value is a *twin* with a proved agreement to
  the derived predicate, never an independent authority; two new typed reasons,
  `:equivocation` and `:authority-equivocation`, join `*fn-peer-reasons*`.
  "Accepted, authority refused" is a fourth log outcome distinct from refused.
- **Policy travels in the group it governs**, so it follows the group's feed
  scope exactly. Successions travel in the one reserved group name,
  `fn.principals` — an ordinary group with no special handling anywhere.
- **fn has no newgroup.** A policy statement cannot create a group; group
  creation is a configuration delta at each node. A group's *authority* is
  local configuration too, so two nodes that configure different authorities
  for one name will admit different sets — a D11 alias disagreement the wire is
  deliberately not allowed to settle.
- **The reader exposes the bytes first, the verdict second.** `HEAD` returns
  `FN-Statement` byte-identical so a client verifies with its own keyring and
  no fn code; the node's own verdict is a new HDR metadata item `:fn-verified`
  rendering three tokens (`verified <id> keyring <n> policy <term>`,
  `unverified <reason> keyring <n>`, `absent <reason>`) — never a boolean, and
  never without the keyring generation, because a verdict whose keyring is
  unstated is not reproducible. `FN-VERIFY` as a command was rejected; the OVER
  extension is costed (it rebuilds the overview theorems) and left to S6.
- **No control messages, signed or not.** RFC 5537 §5 conveys authority by
  content with the verb in the data. pgpverify signs a canonicalised subset of
  an article, has no ordering, no rotation, no revocation, and resolves
  conflicts by arrival — the four things D01, D09, D10 and "preserve
  conflicting evidence" each refuse. Every verb is replaced by a record this
  node holds: configuration deltas for groups, `:policy` statements for
  moderation, nothing at all for cancel (D03).

## Keystones

S1-1 field round-trip and canonicality; S2-1 a `:verified` verdict is grounded
in a named keyring entry, a signature over `fn-stmt-signing-preimage`, and a
`ref` recomputed from the receiver's own projection, plus the
`fn-peer-transfer` equation that makes it a theorem about the function the host
calls; S3-1/2/3 restate `fn-lace-merge-ids-are-union`,
`fn-lace-distinct-same-slot-is-equivocation` and
`fn-lace-reissue-detected-after-merge` over the transit path (with the A-CRYPTO
collision edge kept as an explicit hypothesis, as `lace-tests` exhibits it);
S4-1 restates `fn-pol-current-unchanged-by-foreign-delta` over a peer's contact
batch and names the offending statement when policy does change; S5-1 restates
`fn-me-site-merge-never-revises-admissibility`,
`fn-me-merge-exposes-the-partition` and `fn-me-revoked-refusal-is-monotone` on
the wire, with the new work in the carrier obligation
(`fn-stx-commits-of-batch-are-verified-and-well-formed`) — without it the
restatements would be true of a poisoned delta; S6-1 the reader reports the
recorded verdict, typed. Corollaries are labelled as corollaries; each keystone
ships a non-degenerate witness and one `must-fail` per hypothesis.

## Packets

S0 registry (`fn-stx-`, SUB-001..006) · S1 field codec (subsumes peering K8) ·
S2 verdict and evidence · S3 lace projection, bridge lemma and index · S4
policy on transit · S5 epochs across a partition · S6 reader exposure. S1 and
S2 start against `72279c8` now; S3 needs K1's transit path, S4 needs S3, S5 and
S6 are independent of each other.

## Open

Suites and seam realiser (D09); keyring persistence, distribution and
revocation under partition; whether a group authority may be named on the wire
at all (D11); whether OVER grows a field; the `preds` policy for agents and
what a node does with a dependency-incomplete lace (today: bounded pending
state per REP-002, not a refusal); pruning (D13); a wire form for withdrawal.
