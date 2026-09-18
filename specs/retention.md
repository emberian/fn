# Retention, promises, and reclamation

Status: explicit obligations and indefinite local retention until authorized
release are agreed (D03). Receipt/release details and history/GC policy await
D12 and D13.

## Acceptance is a resource decision

RET-001: an accepted obligation names its subject objects, obligation identity,
responsible node/incarnation, destination or service, terms, release predicate,
and policy/authorization context. Persist it with the content it requires before
emitting its acceptance receipt. An inbound request is not itself an obligation.

RET-002: reserve sufficient capacity before acceptance, accounting for article
bytes, journal/metadata growth, obligations, required evidence, and operational
headroom. Admission also bounds CPU/work and staging. A node may reject new work
when it cannot honor the terms. Indefinite retention plus finite storage implies
eventual refusal under unlimited input; do not hide that tradeoff in GC.

## Receipts and release

RET-003: receipt kinds distinguish transmission, reception, durable object
acceptance, acceptance of onward responsibility, and destination-application
acceptance. None implies human reading. A receipt binds the subject, obligation,
issuer, intended scope, incarnation/nonce as needed, and applicable terms.
Transport ACKs and generic BP status reports are not retention receipts.

RET-004: release is permitted only by the obligation's explicit predicate, based
on authenticated/authorized evidence committed locally. A stale, duplicated,
wrong-subject, wrong-incarnation, unauthorized, or insufficient receipt cannot
discharge it. Record the release decision and evidence before making its objects
eligible for reclamation. Removing one obligation does not remove other pins.

Proposed handoff, assuming cooperative peers:

1. Sender retains under an active obligation.
2. Receiver validates terms, reserves capacity, and commits content plus its own
   matching obligation.
3. Receiver emits its application receipt; it may need to regenerate this after
   a lost reply without accepting a second obligation.
4. Sender verifies and durably records the receipt and discharge decision.
5. Sender may reclaim only if no other roots require that content.

This proves a conditional preservation-of-responsibility property, not that a
signed claim from a dishonest or destroyed peer guarantees delivery. Multiple
replicas and failure-domain requirements need explicit terms.

## Reclamation roots

RET-005: protected roots include unreleased obligations and their evidence,
visible retained articles, local archive policy, unresolved transactions,
in-flight reads/transfers, retained checkpoints, and required identity/history
records. Protect the transitive closure of their object dependencies. Metadata
needed to interpret a promise is part of the promise's retained closure.

Withdrawal, cancellation, visibility, and physical deletion are distinct. A
remote request cannot erase local evidence or discharge unrelated obligations.
An authorized local removal follows explicit policy and records what was removed
and which claims no longer apply. Global erasure cannot be guaranteed while
disconnected replicas retain independent copies.

RET-006: expiry and history pruning must preserve the defined duplicate and
resurrection policy. Dropping a Message-ID tombstone while accepting arbitrarily
old reimports permits resurrection. D13 must choose retained history, admissible
age/epoch bounds, or another explicit rule. Finite metadata budgets apply too.

## Selected local retention policy

Per the user's D03 decision, local acceptance creates a retention pin that lasts
until explicit authorized release, with no automatic expiry. Admission refuses
new obligations when it cannot reserve capacity. Releasing a local archive pin
does not automatically discharge another accepted obligation.

Initially retain duplicate-history entries as well; D13 must settle their later
pruning policy. Until reclamation is implemented and justified, released objects
may remain physically stored. Keeping extra bytes does not license accepting
unaccounted new obligations.
