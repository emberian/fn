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

## Finite identities for maintenance

RET-010 (fn guarantee, full implementation open): persistent transaction IDs and
process-local read IDs are separate finite resources in R of alpha=(L,R).
Capacity admission and no-wrap arithmetic alone do not establish maintenance
headroom. ACL2 derives maintenance purpose from the actual admitted operation
and reserves its identity demand together with its other resources. Ordinary
reservation refuses before consuming that protected demand, including paths
whose later semantic preparation refuses after a reservation.

The quota comes from the actual bounded maintenance publication/read trace
and the selected codecs' representable domains. A caller-supplied maintenance
flag, memory margin, object count, or guessed multiple of a page count is not
an authority or a request census. Current compact/reclaim publication writes a
checkpoint and consumes no Store journal transaction ID; an authorized Store
release writes one. Current forward-undertaking debt names required releases,
and the persistent source gate below connects that debt to live reservation.
The authenticated reader's per-selection request bound is not yet a complete
producer trace bound across source passes, staged digest and cache dispatch.

Each grant owns its exact identities. Concurrent grants cannot double-spend or
steal each other's interval. Live consumed identities never roll back or recycle within their owner
lifetime after refusal, cancellation, uncertain persistence or a stale callback.
Logged/fenced Store identities retain the existing durable issuance guarantee;
neverlogged FNFD correlation metadata follows the reconciliation rule below. Persistent grants require replay and snapshot representation when
they cross a durable boundary. Profile validation, current format and runtime
representation must agree; no old-format inference supplies a missing grant.

The guarantee is conditional on the finite domain and an admitted bounded
trace. Exhaustion is an explicit named refusal, never wrapping or an unlimited
lifetime claim. Maintenance may consume R while preserving promised L on
common-admitted continuations; resource refusals stay observable. PRF-1134 and
SCN-1040 track the actual allocator, host writer, continuation, crash and
recovery obligations. Existing PRF-1110 proves saturation of the current
unprotected allocator and supplies the motivating counterexample, not this
new guarantee.

The persistent source component `books/store-identity-reserve.lisp` now gates
the native log reservation through the owner or standalone Store entry. It
protects exactly one release ID per carried open forward undertaking. New
undertaking admission prepays its own release; ordinary requests stop before
spending the protected demand, including a later semantic refusal. A retention
publication's purpose comes from its canonical event and current replay and
consumer eligibility. The owner also applies its existing publication resource
verdict. Its exact event/frontier grant is consumed on the first prepare attempt,
including failure; a changed operation or another reservation cannot steal it.
Checkpoint publication consumes zero journal IDs. No guessed extra identity is
assigned to the byte/count vector's separate maintenance-record reserve.

The existing issuance definition remains in force (`number-durability.lisp`,
PRF-269): a Store transaction identity is issued when its record is logged and
fenced. An unlogged speculative number in a durable FNFD intent is correlation
metadata, not an issued transaction identity. The intent's complete key is
peer, Message-ID, content obligation identity, evidence, generation, txid and
tick; every pending intent is reconciled before serving, and reconciliation
does not decide from its txid. Such a speculative number may be reused after
crash. This change adds no durable allocator frontier, format field or floor
at the feed journals' metadata. Live consumed grants and speculative numbers
never roll back within the owner lifetime. The grant must be cleared at owner
reinstallation; stale callbacks cannot claim a later grant. Complete joins to
that isolation and the existing logged-prefix recovery proof remain open.

The protected ordinary-refusal trace reference (`identity-reserve-trace.lisp`)
composes the actual reservation gate with the actual reserve/refuse functions.
From a ready Store whose promised release IDs are already funded, every bounded
trace retains readiness and that headroom; records, groups and capacity stay
unchanged. Its reachable twenty-refusal witness reaches the protected boundary
and still admits the exact release. The reference driver is not a served or
guard-verified implementation and does not establish callback or crash isolation.

If a release reservation fails before durable publication, its debt stays open
while its live ID is spent; another grant requires enough remaining identities
and other resources. Finite one-ID-per-release funding cannot promise eventual
success under arbitrarily many post-reservation failures. Local producer read
census, protected read grants and full W8 continuation equivalence remain open.

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

Current authority and historical evidence are separate. A new signed receipt
is checked using the Store's current principal snapshot inside the serialized
owner operation (`fnn-bpnode-receipt-result`); a primitive signature observation
computed earlier is insufficient after a durable `fn-hl-revoke-event`.
`books/receipt-revocation.lisp` (PRF-1118, SCN-1024) develops the composition
from actual `fn-sn-finish` to the host-called receipt gate and record selector.
Revocation must retain historical key snapshots, article verdicts, obligations
and their evidence. A previously committed intent remains historical replay
evidence for that decision; it grants no authority to accept another receipt.
The full owner/reclamation refinement and matching native evidence remain open.

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

Workflow journal: the release-aware layer uses `fn-bprl-apply-journal-record`
and `fn-bprl-replay-journal` for preflight, durable apply and recovery. They
extend the earlier `fn-bp-*` workflow interpreter with two append-only FNWF
records, `(:undertake work-id charge)` and
`(:release receipt-id work-id subject issuer policy-id terms-id incarnation)`;
`fn-bprl-apply-journal-record-agrees-with-host-on-bp-records` says it equals
the earlier interpreter on every record that function accepts, and a release
record whose evidence fields differ from the decision ACL2 recomputes is
refused (`fn-bprl-release-record-replays-decision-by-definition`). FNWF codes
8 and 9 encode these records; codes 1 through 7 retain their existing wire
values. `books/bp-workflow-constructors.lisp` parses the exact canonical
receipt ADU, requires the explicitly selected trusted-local observation,
and returns intent or release records only after ACL2 preflight in the current
state. These records remain workflow history and are not Store release
authority. The configured owner's separate Store release event remains the
authoritative retention mutation.

On a successful reopen, `fn-bprl-replay-work-status-is-durable-status-restarted`
equates the work status installed by the release-aware replay with
one restart of the status obtained by folding its exact durable records through
the same ACL2 interpreter. The witness includes undertaking and release; a
malformed suffix is refused and shows why the successful-replay premise is
needed. This is status correspondence, not physical filesystem durability.
The current offline workflow host wraps this language in
`fn-bpiw-replay-journal` for ION route/observation records. Its full mixed-stream
work-status correspondence remains open (PRF-034); single-record projections
do not establish that whole-replay result.

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

The protected ordinary-refusal reference trace also preserves a named complete
immutable Store-field frame, including acceptance, full retention and bindings,
consumer/topic, configuration, keyring evidence and indexes. Its spent file
frontier and node next-txid remain resource effects outside that frame. This
partial frame does not establish full reclaim/recovery alpha(L,R), stale host
callback exclusion, arena relocation or retirement-debt discharge.

PRF-1143 / SCN-1049 specify the exclusive incoming octet holder for yielded
POST identity queries. Its typed fixed-shape token uses the same process-local
resource namespace and charge as reads. A carried exclusive slot permits only
owned setup, then sealed readonly access; cancellation retains ownership until
query return and last-alias clearing. Ordinary receive service needs a distinct
funded congruent buffer at the existing connection read quantum. These source
components remain unactivated pending actual readonly dispatch, all native and
concrete mutation hooks, constructor census and complete startup/runtime funding.

The shared pool is one three-field stobj (ledger data, lifecycle mode, incoming
slot), declared in `books/page-read-pool-state.lisp`; extraction does not reset
its shared NEXT. Actual wrapper sequences reject spent input tokens both while
unheld and after fresh readmission. Repeated cancellation retains the same row.
A receive append's no-resize theorem requires actual installed physical capacity
and room within the existing read quantum. Matching source admission establishes
these boundaries; the changed pool layout still needs its own startup baseline
and qualified image, and incoming capture requires actual incremental resident
constructor/retention demand above the retained packed/open connection charge.

The concrete input reserve census relates `fn-octets$c-reserve`, called by
native fill, to max(requested capacity, old physical capacity). Keep old backing
and conditional replacement backing charged simultaneously until definite
replacement and retired alias joins; source-vector retention is a separate
component. The native pending job retains the sampled old backing before fill
can throw. Scalar layout components require actual operational provenance and
selected-runtime constructor/frame evidence before admission authority. Whole
reserve/allocation and whole REPLACE remain D27 obstructions until bounded setup
or funded profile-backed preallocation is joined; a holder alone does not make
those operations bounded.

The selected incoming setup controller carries a fixed token, total, installed
capacity, existing connection quantum, offset, pending flag/range and phase.
The operational capacity descriptor remains in the shared pool's third-field
carrier and survives holder release. A NIL descriptor is uninitialized, never
an inferred zero capacity. Installation promotes its current reserved claim
C to retained U atomically; uncertain installation retains the old descriptor
and all overlap/debt. Supplied source fixtures do not establish the actual
constructor charge or the raw backing/descriptor observation relation.

The paired start/next/ack/stop boundary associates one fixed controller with
the current pool row and protected token. Next returns scalar word/start/count/end;
repeated next before acknowledgement repeats the same range. A matching copied
acknowledgement advances the fixed offset. Ambiguous copying cancels and retains
charge and aliases. Completion seals the row, and settlement requires exact
joins and cleared aliases. The logical list-plan cursor remains a diagnostic
reference, not the selected served implementation. Native callbacks must use
the guarded compiled scalar-MV entries directly, bypassing list dispatchers.

Source admission of this controller does not authorize activation. Remaining
joins include full paired output/effect refinement teeth, exact raw source and
backing identity across all yield intervals, operational vector-domain carry,
constructor/frame/allocator/GC/startup funding, and immutable core context
registration/clear ordering. Ordinary command traffic uses a separately funded
congruent RX backing; it may not overwrite the held incoming backing. RX bulk
fill needs its own core-issued bounded range and complete effect boundary.

The unactivated RX source adapter uses one `fn-rx-provider` containing the
congruent `fn-rxp-octets` child and the three-field `fn-rxp-carry` child.
NIL carry means uninitialized. Shared-pool reservation precedes its constructor;
the current reserved row is checked before reserve, retained capacity promotion
commits before publishing token/instance/capacity carry, capacity last. Unknown
outcome fences the instance and retains charge; duplicate installation does not
reserve or rebind. This sequence still requires the actual factory/fault boundary.
`fn-rxp-fill-range` checks the maintained token and instance, installed4096 chunk
capacity, supported connection quantum and primitive fuel. It returns scalar
word/start/end/remaining fuel without changing either child or scanning ledger.
4096 bounds a chunk, never total input; exhaustion retains the source cursor.
The reference-only list fill records complete bytes/carry/fuel effects for the
native primitive refinement target. It does not qualify REPLACE/set-fill.
Native object association, full boundary teeth, constructor/frame/allocator/GC
and startup funding remain open; this adapter is not activated.

On uncertain RX copy, `fn-rxp-fence` is core-authorized by the exact current
token and clears only capacity. Issued token/instance, bytes and physical object
remain; the shared pool U charge is untouched. Repeated fencing is idempotent,
a foreign token cannot affect the current instance, and later range/consumer
readiness must refuse. The native `fnn-owner-receiver-fill` handler must fence
before extent unlock or any consumer after partial/unknown primitive failure.
This actual ordering and primitive behavior remain runtime/native obligations.
A controlled same-object reset belongs to the installed pool bridge and requires
definite alias/turn joins; no host Boolean, refund, constructor or reallocation
can re-enable the fenced instance.

`fn-rxp-child-corr` names the proof-only selected child relationship using the
existing registered `fn-octets$corr`. The provider reference fill preserves this
relationship through `fn-octets-from-list{correspondence}` with a valid byte list
and completed range permission. This relation does not admit a separately
supplied physical child or establish a raw pointer association. The actual
`fnn-owner-receiver-fill` uses the sanctioned SAME-provider projection and the
central selected array-copy semantic contract; concrete object association,
primitive failure and the composed outer service recovery fence remain required.

The RX array semantic join is conditional on A-RX-ARRAY-COPY. The actual
subject is `fnn-owner-receiver-fill`; the named core theorem
`fn-rxp-assumed-array-copy-refines-reference` connects a successful primitive
observation at the completed core-issued range to the registered concrete
child abstraction and complete provider reference result. Literal model
witnesses do not qualify Common Lisp REPLACE. Raw immutable issued identity
association, installed backing/pool authority, and an effective provider or
whole-service quarantine on every primitive/callback escape remain separate
requirements. Controlled same-object reset is unavailable until the actual
receiver turn and all escaped aliases have definitely joined; capacity NIL
or a supplied joined flag cannot authorize it. Permanent U remains charged.

The separate receiver-turn controller has six fixed fields: ticket, maintained
source association, phase, remaining demand, retained-job reference, and
receipt. Its internal begin transition uses the existing shared PRS issuer
and PRL NEXT, storing `(:receiver-source (:receiver-turn oldNEXT)
receiver-capacity-token actual-provider-instance)` from the actual provider.
A live turn cannot be overwritten. The connection publication/view holder
is a different authority and cannot stand in for this custody ticket.

This source begin is internal and unactivated. Before a public begin, the
actual installation receipt must bind this exact provider/token/instance to
the SAME pool; provider currentp alone does not establish that relation.
Constructor and operation demand must be canonical and qualified. The
request receipt must store the actual registered receiver-source association
before any custody transfer. Completion requires the actual core-produced
result/retained-job receipt and final alias settlement; CID, step equality,
lexical STATE return, STOPPING or a supplied joined flag are insufficient.
No return/reset API exists while that association and receipt are absent.

The begin gate now requires the bounded installation receipt shape/tag/token/
instance and keeps it unchanged; it does not allocate a comparison tuple.
The paired installation subject `fn-owner-rx-capacity-install-turn` writes
`(:receiver-install actual-provider-token actual-instance)` only after the
real reserved-to-installed transition. A duplicate installed row cannot bind
a second fresh controller. Raw constructor/object association, startup
precharge and failure/recovery cuts still require matching evidence. Every
fill needs the actual admitted turn ticket; the capacity-only child range
helper is not authority to overwrite a transferred receiver source.

The paired scalar range subject is `fn-owner-rx-turn-fill-range`: exact turn
ticket, source vector length, limits, fuel, provider, turn and SAME pool;
it returns word/start/end/remaining fuel/provider/turn/pool. It checks the
maintained live current slot, immutable installation anchor, spent pool nonce
and current charged contribution before delegating the private capacity range.
Refusal preserves all stobjs and fuel. `fn-owner-rx-turn-start` returns a ticket
only for a newly admitted turn; busy callers receive NIL, never the retained
request's ticket. These guarded source boundaries do not acknowledge a raw
copy, authorize consumer sequencing or establish custody transfer/settlement.
Canonical demand and the actual backing association remain activation gates.

The selected copy sequence now has a fixed pending range in the existing turn
job field. `fn-owner-rx-turn-copy-next` fences provider readiness before it
returns endpoints, marks the turn `:copy-issued`, and stores start/end/left
once. Repeated NEXT returns that same range without another fuel charge.
`fn-owner-rx-turn-copy-ack` accepts exact ticket/pending endpoints and the
named native copy primitive's outcome. Success requires actual child fill=end,
marks `:filled`, then publishes capacity4096 last. Uncertainty keeps readiness
revoked, pending tuple and charge retained, with phase `:cancelled`. All
consumers must use the exact filled-turn `fn-owner-rx-turn-consumablep` gate;
its companion source getter derives the retained association. This is neither
alias settlement nor re-enable after an uncertain turn. The fixed pending
allocation, primitive callback overlap and actual array observation binding
remain part of canonical runtime demand/refinement. No return/reset exists.

The receiver's unread suffix is retained with the exact committed recipient.
The internal pending bridge reads that recipient's current receipt once and
projects source plus consumed from its SAME saved step, rejecting malformed
scalar consumption before any transfer. The named scalar/step equality is
conditional on the producer's carried step domain; a committed phase alone
cannot validate a corrupted full step. The bridge's function guard and custody
preservation theorem have passed a confined matching-source replay; the actual
serialized producer's step-domain establishment and reachable positive witness
remain open. This is not an activated transfer path.

The query context extension reserves field9 for the fixed custody row, keeping
payload5/effects6/origin7/receipt8 unchanged. Its source projection stores the
original range, bounded unread offset/end, exact recipient and actual actor
holder-root references. Empty unregistered fields are not terminal authority.
The actual query/render/response/cold/worker acquisition and return protocols
must preserve each holder identity and phase, including simultaneous aliases.
Terminal source publication must precede clearing query inputs. Only that real
all-alias disposition may resume the same immutable input at its saved suffix;
query completion, lexical return, STOPPING, counts or a joined flag may not.

The original request recipient remains immutable provenance in custody field2.
Adoption binds query-holder field7 to the actual selected generation token,
preserving the shared issued nonce/address and the unread suffix. Repeated
binding preserves the current row. The RH acquisition is one-shot for that
selected token: its producer projects the actual six RH references into the
render root before installation and records `:render-owned`. A returned actor
cannot be rearmed with the same query token. Worker borrows within the actor
require their own exact registered identities and final epilogue receipts.

The freshness publication reader uses the actual registered query capture and
current registered publication. CatalogC and StoreF remain separate scalar
coordinates; generation binds the key, and table/row identities bind the roots.
It compares no opaque key or retained graph. A stale result requests recapture
of the same input and intent without a new frontier allocation. Publication
freshness alone grants no current authority: the owner must retain and recheck
its actual epoch, configuration generation and canonical account publication
namespace/revision under owner exclusion. The durable Store-to-publication
correspondence and operation-derived funding are separate activation gates.

SCN-1049 also covers ordinary noquery parser lifetime. Before parse, the actual
serialized STATE producer acquires a parser actor retaining current preOC/wire
with RC NIL and the exact filled source range. Progress is derived from the
same produced served-step and retains actual RC/wire even at the range end;
it is not a detachment or refill receipt. A response commit records an issued
(:receiver-response lifetime-ticket episode) token, including zero-consumed
terminal close/exposure-close responses. The maintained episode increases on
each commit, so stale callbacks cannot settle a later response. The per-filled
span bound is derived from the admitted receive quantum, not stored-data size.
A zero nonclosing response is refused and the actual postSTATE RC/wire/step
must be fenced and retained in parser recovery before exposure. Real IRQ
transfer retains both the parser root and SAME committed receipt actor root.
Connection/RX factory association, ordinary parser detachment, actual response
return and all-alias terminal producers remain activation prerequisites.

The recorded response chooses the next range from its own consumed scalar and
close/exposure-close fields. That decision is separate from permission to use
the range: :same-input-remainder cannot rearm until the actual response episode
and every retained actor have returned. A source terminal receipt must be
emitted by the real registered protocols before destructive query input clear.
The planned :source-returnable custody phase has no current emitter; NIL actor
fields, :done, STOPPING and caller joined words cannot create it. Ordinary
receiver roots and completed incoming POST roots have distinct source/range
kinds; receiver-only shape checks never impose 4096 on the stored input.

The actual parser evaluator leaves STATE unchanged. Before any install write,
its SAME RC is recorded in the existing parser root and the phase becomes
`:parser-installing`; provider capacity is then revoked. The installer reads
that recorded RC, and finish derives its result from the root rather than a
caller RC. An escape during cache, credits, owner or exposure publication
retains the RC/source/claim. Progress records its cursor before publishing
capacity last; the intervening cut refuses every public consumer. Response
completion retains revoked capacity until real custody return. Staging adds
root allocation and old/new overlap to the epoch allocation census; it does
not create a release, refill, rollback or reclaim receipt.

Ordinary nonquery output remains owned by the actual receiver response episode.
The receiver controller appends one NIL-default output-bundle field after its
original six fields; its parser job remains the original root11. The retained
bundle contains that parser root, no IRQ actor, and the actual outgoing job.
The episode-qualified output getter checks the current ticket/source/episode;
field presence does not establish storage admission or terminal return. Begin,
fill, copy ACK and parser reacquisition refuse while this bundle remains. The
current query transfer also refuses a retained ordinary output bundle until a
real typed custody transfer preserves it. No clear/reset/return setter exists.
The former six-field constructor measurement is historical. New default/factory
objects, bundle allocation, storage overlap and epoch-A charges need matching
selected-runtime qualification before activation.
