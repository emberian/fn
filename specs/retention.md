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

## Release of the forwarding obligation (wave 2)

Status: modeled and certified for the sender's node image in
`books/bp-release.lisp` / `books/bp-release-invariants.lisp`; the retention
ledger still compares a string, and the host does not yet call the wrapper.

Before this wave nothing in `fn-bp` called `fn-retain-release`: an authorized
receipt only made a work stop being `fn-bp-work-outstandingp`, and no pin for
the forwarding obligation existed to release. Two decisions now exist, both
total and no-ops on refusal:

- `fn-bprl-undertake` admits the `:forward` pin for a durable outstanding work
  under `fn-bp-work-obligation-id`, with the pin's required evidence rendered
  by ACL2 from the work and the fixed configuration
  (`fn-bprl-required-evidence`: work id, immutable subject, receipt
  authority, policy id, terms id, incarnation). The receipt id is not part of
  it because the pin exists before any receipt does.
- `fn-bprl-release-decision` finds the committed receipt by id in the
  workflow's receipt history, the work it names, and requires: the work
  carries that very receipt; `fn-bp-authorized-receiptp`; the `:forward` pin
  present with the required evidence; no staged archive transaction on the
  node; and a forwarding id that is neither the archive id nor any archive
  binding's id. It builds the typed release evidence
  `(receipt-id work-id subject issuer term incarnation)` with the policy term
  placeholder `(:fn-forward-term policy-id terms-id)`, renders it, and calls
  the node's `fn-retain-release` for exactly that pin.

RET-004, adjective by adjective (each a ground refusal in
`tests/acl2/bp-release-tests.lisp`): stale (receipt prepared but not
committed, or unknown), duplicated (second decision on the same receipt, or
no pin), wrong-subject, wrong-incarnation, unauthorized (issuer), insufficient
(terms), wrong-work (receipt naming another work, or not carried by the work).

Keystones (`books/bp-release-invariants.lisp`):
`fn-bprl-authorized-receipt-evidence-matches-required` (the typed evidence
renders to the pin's required evidence exactly when the receipt is
authorized); `fn-bprl-release-removes-the-forward-pin`;
`fn-bprl-release-preserves-independent-pin` and
`fn-bprl-release-preserves-archive-pin` (`fn-retain-release-preserves-independent-pin`
lifted through the node: the article's archive pin is byte-identical);
`fn-bprl-release-preserves-node-state`, `-state`, `-binding-state` and the
`fn-bprl-undertake-` counterparts; `fn-bprl-undertake-pins-the-forwarding-obligation`
(release is reachable after undertaking);
`fn-bprl-no-receipt-no-release-no-peer-reliance` (A-PEER's constraint: no
receipt, no release, and nothing for `fn-assume-peer-retainsp` to hold of);
`fn-bprl-release-evidence-has-policy-shape` (the decision yields the term and
evidence shapes `fn-assume-policy-authorizedp` consumes; binding the verdict
to that signature is D09).

Workflow journal: `fn-bprl-apply-journal-record` extends the host-called
`fn-bp-apply-journal-record` (`host/workflow-host.lisp:27`, `:40`) with two
proposed FNWF records, `(:undertake work-id charge)` and
`(:release receipt-id work-id subject issuer policy-id terms-id incarnation)`;
`fn-bprl-apply-journal-record-agrees-with-host-on-bp-records` says it equals
the host-called function on every record that function accepts, and a release
record whose evidence fields differ from the decision ACL2 recomputes is
refused (`fn-bprl-release-record-replays-decision-by-definition`). The host
wrapper. These records remain workflow history and are not Store release
authority.

The authoritative retention mutation is a variant of the Store's single
immutable transaction history (`books/store-events.lisp`). Existing article
transactions retain their exact `fn-r` schema-0 encoding. A disjoint `fn-e`
version-0 envelope carries `:undertake` and `:release` events with the same
contiguous sequence, transaction-id allocation, link-and-directory durability
barrier, completion gate, and recovery order as article transactions. Ordinary
Store and configured-owner recovery decode that event sum and replay retention
events between articles in filename order. A later article transaction
therefore starts from the released ledger; reopening without a workflow option
cannot resurrect the pin.

The native `bp-obligation` owner path publishes the canonical Store event and
then synchronizes the workflow node image from that owner. A committed receipt
outcome precedes release publication. Process death in that interval retains
the forwarding pin, rather than treating a transport acknowledgement or an
unsigned receipt as authority. Automatic reconciliation of that retained,
committed receipt after such a cut remains open, as do D09 signature authority,
certification of the widened Store proof cluster, and replacing the ledger's
string comparison with the typed structure (C2-10).

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

RET-007: the provenance of an accepted obligation is a typed value with a
named kind and typed fields, not a rendered string. The ledger's evidence slot
admits a provenance (`fn-provp`, `books/provenance.lisp`), whose kinds are
`:post` (principal, injection generation), `:peer-transit` (peer name, transit
command, Path diagnostic, configuration generation), `:bp-receive` (node id,
bundle identity, ingress label), `:local` (reason) and `:legacy` --- and
`:legacy` is EVERY STRING, verbatim, so an obligation written before the typed
value existed stays admissible with the bytes it already has. Each kind renders
to exactly the string its writer produced before the widening, so no CLI line,
log line or stored byte changes meaning; the lossless form is the canonical
wire string (`books/provenance-codec.lisp`), which rides in the existing
`release-evidence` field and reads back as the record it encodes. A writer
decides its provenance in ACL2; a host renders it and marshals octets.

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
