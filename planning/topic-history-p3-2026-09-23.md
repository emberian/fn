# P3: independently governed topic histories

Status: reviewable implementation proposal, 2026-09-23, at fn `de305073`.
Independently governed topic histories are part of the
[active goal](now.md); they are authorized work, not an optional future goal.
The concrete wire grammar and first policy profile below are proposals.
Portable controller succession, delegation, legitimate governance forks and
cross-store consensus remain distinct product choices. This packet adds no
approval queue and changes no live service, requirement or proof status.

The [OS integration study](dregg-os-integration-2026-09-23.md) provides the
cross-repository context. This packet makes its P3 small enough to implement:
**a public, fixed-controller, explicitly anchored topic whose bounded author
roster changes through exact-source signed control records, with durable local
topic admissions and separate current-policy status.** Two such topics can
have different controllers and rosters. Mini continues to evaluate application
resource law. fn does not evaluate Mini predicates or run its operations.

## What existing code permits, and what it does not

| Source | Reusable boundary | Limit relevant to P3 |
| --- | --- | --- |
| [identity](../books/identity.lisp), `fn-id-subject-of-payload` | ACL2 owns exact source identity, including its label/version/algorithm container. | A subject identity is currently **48 octets**, not a bare 32-octet digest. Do not replace it with a Mini digest or Message-ID. |
| [hybrid-store](../books/hybrid-store.lisp), `fn-hsig-authorized-carried-submission-event` and snapshot binding | Accepted exact source, received carrier and historical key context join one durable article event. | A `:verified` token by itself is insufficient: [stx-evidence-records](../books/stx-evidence-records.lisp) returns `:requires-binding`, not application authority. |
| [config](../books/config.lisp), [node-config](../books/node-config.lisp) | Historical group creation/retirement, local policy-ID labels and current served groups. | `fn-cfg-group-policy-id` is not a verified portable governance program. The live-name table is not a topic history. |
| [policy](../books/policy.lisp), [stx-policy](../books/stx-policy.lisp) | Authority confinement, explicit equivocating policy evidence, historical policy terms. | Uses legacy statement/keyring semantics and latest `(incarnation,sequence)` candidates. The book explicitly says `fn-peer-decide-transfer` does not call its gate; its whole-lace walk cannot become a served admission path unchanged. |
| [membership-epochs](../books/membership-epochs.lisp) | Distinguishes evidence merge from adopted chain and records forks. | It is a policy model without authenticated commits. Its no-readmission rule and late-epoch window are not silently selected for P3. |
| [consumer progress](../specs/consumer-progress.md) | Store-scoped durable position and explicit rebase under changed selection/visibility. | Group aliases, topic IDs and application operation IDs are separate. The first poll is still an active implementation join. |
| Mini [ResourceTransaction](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Kernel/ResourceTransaction.lean#L143) | Operation identity binds domain, semantics, subject and nonce independently of payload. | fn must not calculate this marker or consider it an article dedup key. |
| Mini [CausalVersionDag](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Theory/CausalVersionDag.lean#L258) | Generic admitted-parent validity is separate from `currentTips` policy. | fn's typed parent links are a communication history, not proof that a Mini application event satisfies its semantic family. |
| Mini [policy registry](https://github.com/emberian/minidregg/blob/dd1360d774e802900e3063e397ee29af073994b2/Compiler/CredentialAuthorityPolicyRegistry.lean#L88) | Existing grants face current policy revision; revision and revocation differ. | A historical fn signer or topic roster entry cannot bypass current Mini grants. |
| Bread [mailbox](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/dregg-sdk-net/src/mailbox.rs#L416) and [execution cursor](https://github.com/emberian/breadstuffs/blob/c93404d81c013d4c5b304a852d26f190d0aab19f/node/src/execution_cursor.rs#L59) | Distinguishes message delivery from normal turn submission and durable terminal execution. | Topic admission may never auto-sign an action with recipient-owner authority or count as blocklace finalization. |

P3 should reuse T10's exact-source bindings and the existing Store publisher,
not make legacy `FN-Statement` policy signatures a second way to satisfy the
selected dual-signature profile. `FN-Policy` is presently a reserved/rejected
name in the [hybrid carrier](../books/hybrid-carrier.lisp); repurposing it would
be a carrier contract change. The proposed new `FN-Topic` field below is signed
authored content, never a mutable projection.

## First profile: clear semantics without a governance language

The experiment's profile is `fn-topic-public-roster-v1`:

* A local authenticated administrator anchors an exact, already accepted root
  source to a topic budget. Root authorship must bind to its declared controller.
  Receiving a root article alone does not install it or reserve resources.
* The topic ID is the exact source identity of that root. The root does not
  contain its own topic ID, avoiding a hash self-reference. It contains a fresh
  opaque nonce so deliberately distinct topics need not share an identity.
* The controller principal and ordered hybrid keyset are declared in the root's
  signed metadata, matched to its bound verification context, and fixed for
  this profile. Only that controller's
  bound hybrid-authored control sources can propose a roster successor. The
  controller is not implicitly a report author; include it in the roster when
  desired. No delegation, recovery-key bypass or controller succession is
  encoded in v1.
* A control successor names the exact previous policy source and replaces a
  bounded roster. It never selects a predecessor by wall clock or arrival rank.
  A site explicitly and durably installs an eligible successor; mere evidence
  collection changes no selected policy.
* New report admission requires the currently installed uncontested policy,
  a bound native author in that policy's roster, and already admitted same-topic
  parents. It never invokes Mini. Application bytes stay opaque.
* A retained historical admission remains a fact about its own policy and local
  committed prefix. A later policy can prevent new admissions without erasing
  that fact or reclassifying its old signer as unauthenticated.
* Two verified distinct controls with the same predecessor are retained as
  governance-conflict evidence. In this experimental profile, knowledge of such
  a conflict anywhere on the selected lineage blocks new report/control
  admissions. Historical facts survive. No later sequence number automatically
  heals the fork. Selecting a legitimate continuation is a later explicit
  governance contract, not “first seen wins.”

Local adoption means two disconnected sites can temporarily have different
current policy tips. Both expose their selected tip and conflict status. There
is no assertion that either site has the globally freshest policy. This is
independently governed local use with portable evidence, not invented consensus.

The flat roster is a deliberately small fn communication policy. Distinct
Mini resource policies can make two consumers react differently even to the
same admitted report. That difference stays in Lean; P3 does not need an ACL2
predicate language for application execution.

## Proposed exact logical values and portable bytes

New names use proposed prefix `fn-th-`; reserve it in `docs/prefixes.md` when
the first book lands. These shapes are a proposed interface, not admitted ACL2
definitions. All lists are proper, all integer fields are unsigned 32-bit,
and constructors/decoders reject unknown versions and duplicate set members.

| Type | Exact logical fields and recognizers |
| --- | --- |
| `source-id` | Existing `fn-id-subjectp` octets, currently 48 bytes. Never strip the label or algorithm. |
| `principal-id` | The existing hybrid profile's exact 32-byte principal field. Do not derive it through legacy `fn-prin-id` as a second algorithm. |
| `keyset-id` | Existing `fn-id-subject-of-payload` over the exact canonical `fn-hsig-keyring-snapshot(principal, ordered-keys)` bytes, computed in ACL2. This is a typed evidence-content identity, not an article identity or Store generation. |
| `author-ref` | `(principal-id keyset-id)`. Both must match the completed article's bound verification context. A local enrollment under the same principal but different keys is insufficient. |
| `topic-id`, `policy-ref`, `parent-ref` | Typed uses of `source-id`; topic root, control source and report source respectively. Their grammar is shared but table role checks differ. |
| `app-domain` | Nonempty opaque octets, at most 64. It identifies the consumer protocol namespace, not a Mini digest or fn principal. The Mini consumer checks its own domain/profile pins independently. |
| `root` | `(:root nonce controller controller-keyset-id app-domain authors)`; nonce 32 octets; authors a canonical byte-lexicographic strictly increasing list of at most 16 `author-ref` pairs. Root identity and initial policy identity are its enclosing authored-source ID; declared controller/keyset must match that source's verified carrier. |
| `control` | `(:control topic previous authors)`; topic and previous are full source IDs; authors has the root's roster grammar. A control cannot change controller/app-domain. |
| `report` | `(:report topic policy parents)`; at most 8 distinct same-topic report-source parents in byte-lexicographic order. An empty parent set is allowed. No self ID or application operation ID appears here. |
| `auth-ref` | Local `(article-sequence article-txid source-id verdict-sequence keyring-generation profile)` resolved by the owner to a completed T10 event/snapshot; profile must be `fn-hybrid-v1`. These local coordinates never travel as portable authority. |
| `anchor` | `(topic controller controller-keyset-id app-domain root-auth-ref quota-id)` with a locally authorized finite reservation. Immutable semantic identity; local routing aliases live separately. |
| `current` | `(topic selected-policy local-adoption-generation status)`; status `:active` or `:contested`. Generation is local, never a portable ordering claim. |
| `admission` | `(topic report-source policy-ref source-auth-ref committed-admission-sequence)`; immutable once committed, with report parents recoverable from exact retained metadata. |
| `operation-ref` | Remains entirely in E1/Mini payload and consumer operation index. P3 neither creates it nor proves its relationship to a report. |

Portable field value proposal: `FN-Topic: v1 <base64>`, exactly one occurrence.
After unfolding through the existing bounded article parser, require one ASCII
space after `v1`, standard padded base64 without internal whitespace, and exact
consumption. Physical folding remains governed by ordinary article parsing;
the signature binds the actual authored folding and source bytes. Do not
normalize/rewrite the original article during projection.

The decoded payload is a restricted canonical CBOR item sequence using the
existing byte-string/unsigned-integer primitives, with no maps, floating values,
indefinite lengths, strings or executable forms. Logical encodings are:

```text
root    = uint(1), uint(0), bstr(nonce), bstr(controller),
          bstr(controller-keyset-id), bstr(app-domain), uint(author-count),
          (bstr(principal), bstr(keyset-id))*
control = uint(1), uint(1), bstr(topic), bstr(previous),
          uint(author-count), (bstr(principal), bstr(keyset-id))*
report  = uint(1), uint(2), bstr(topic), bstr(policy),
          uint(parent-count), bstr(parent)*
```

The item decoder is capped at 39 items, binary at 1536 octets and base64 at
2048 octets; it checks each length/count before allocating or traversing that
field. The first implementation must derive and prove constructor length
bounds instead of hand-copying this cap into hosts. Canonical encoding and
exact decoder equality refuse alternative encodings. Duplicate/malformed/
unsupported topic metadata yields `:unsupported`/`:invalid` topic projection,
never a topic authority. The underlying article may still be retained/served
as ordinary public evidence under normal fn rules.

The decoder only examines this signed field. It does not parse a Mini prefix,
trust a JSON `verified` flag, inspect application operations, or chase payload
dependencies. The new source ID is calculated after its header/body exist;
typed parent references name earlier source IDs. Cross-topic application
dependencies remain inside the E1 envelope and are verified by the consumer.

## Proposed local events and actual receiving boundary

Keep article acceptance and topic admission separate. A new topic event refers
only to an already committed exact source, so article arrival can succeed while
topic participation is pending/refused. This preserves D03 and avoids changing
the atomic kind-4 article grammar for an experimental projection.

Proposed event wrapper:
`(:topic-event version sequence txid configuration-generation operation body)`.
It occupies the existing global Store sequence/transaction namespace, with a
distinct versioned magic chosen at integration, not a second journal. Do not
reserve a numeric kind until coordination with the active consumer/BP Store
event extensions; their unmerged values cannot be inferred from this base.

| Operation | Request and commit checks | Durable projection |
| --- | --- | --- |
| `:anchor` | Authenticated local administrator, exact completed root `auth-ref`, root controller equals bound signer, unused topic identity, finite quota available. | Install immutable anchor, root policy metadata and selected root; charge the topic reservation. |
| `:observe-control` | Topic anchored; exact completed source; source metadata matches this topic; signer and exact keyset equal fixed controller context; predecessor is retained or explicit `:missing-parent`; budget available. | Retain validated control metadata/edge and verification reference. Unknown predecessors remain bounded pending evidence. Conflicting children update lineage conflict status atomically with this event. No tip adoption. |
| `:install-control` | Authenticated local topic manager as installed by the anchor's local admin binding; candidate is a verified retained child of the selected policy; selected lineage uncontested; exact expected prior tip and local adoption generation. | Select candidate, increment local adoption generation, and advance relevant durable consumer query/view version. No article or grant rewrite. |
| `:admit-report` | Exact completed source, valid report field, anchored topic, active current state, report names current policy, signer/keyset pair in roster, all same-topic parents have earlier committed topic admission, limits/charge satisfied. | Append one immutable topic admission and update bounded parent/admission indexes. Repeating exact tuple returns prior acceptance; incompatible binding is refused/preserved as evidence. |
| `:bind-alias` | Authenticated local admin; existing group and topic; expected alias generation matches. | Versioned local group-to-topic projection. It cannot alter topic identity/controller or previous admission records. |

`observe-control` must detect a conflict on any selected ancestor, including
when a competing older branch arrives after descendants were installed. A
bounded child-edge index plus selected-lineage flags is sufficient in this
small profile. It must not call `fn-pol-current` over all retained articles.
Appending an unrelated report/control must preserve another topic's projection.
An unknown predecessor cannot be classified as a valid adopted successor until
the typed edge resolves; resolution is a bounded explicit operation/commit,
not background unbounded closure discovery hidden in poll.

Manager authority is a **local configuration binding** for install/bind actions,
not an alternative portable controller. The manager cannot install an unsigned
policy, change a roster, resolve a governance fork or change the controller.
Another administrative domain can anchor the same root and choose when to
adopt eligible successors independently. Removing a local alias does not revoke
the portable topic or permit recycling its NNTP numbering.

Proposed host-called subject:
`fn-owner-topic-step(owner, authenticated-caller, bounded-request)` in
`host/owner-host.lisp`, entering an ACL2 `fn-th-prepare` over carried projections.
The native owner transports bounded bytes and invokes the existing prepared
publication gate. The acceptance theorem must be over this wrapper or have a
named equation to `fn-th-prepare`; an orphan `fn-th-authorizedp` is insufficient.
Inputs are resolved from pinned completed Store/identity/configuration views;
the caller cannot supply a principal/verdict Boolean or policy table.

A local alias binding does not rewrite signed `Newsgroups`. The first scenario
uses matching configured group names at both sites, as the current submission
binding requires source fields and article memberships to agree. Arbitrary
cross-site alias translation would require a separate projection/routing
correspondence; it is not obtained by adding this table. P3's portable identity
is useful even while this transport compatibility restriction remains.

Only matching committed completion updates visible topic state. Publication
returns `accepted`, `refused` or `uncertain`; an ambiguous write fences
mutations until recovery. The two-stage cut after article commit but before
topic event simply leaves preserved source without topic admission. Replaying
the original source does not invent an admission. An interrupted install leaves
either the old or new complete topic/view generation after verified recovery.

## Historical truth, current authority and consumer scope

The historical claim is deliberately precise: **at local Store prefix S, this
node admitted this exact report under this exact policy and bound author
context**. It is not a claim that a report was authored before a revocation,
that all sites adopted that policy, or that a Mini operation was legal.

Exact lookup/retry of an already committed admission returns its historical
record before asking whether a *new* admission is currently allowed. It is
reported as `accepted, replayed-historical` with a separate current-policy
status and creates no new event. Otherwise revocation would destroy retry
recovery. The exact stored source/context binding still must match: possession
of a prior report ID is not enough to submit altered bytes.

Pinning author keysets makes portable authority explicit without selecting key
succession. A controller can replace a report author's `(principal,keyset)` pair
through ordinary roster revision. That does not make the old key historically
invalid. Replacing the controller keyset, including a locally re-enrolled
principal under new keys, cannot authorize a v1 control successor. It requires
the later explicit succession contract or a distinctly identified new topic.

A report newly received after policy P1 replaces P0 cannot obtain historical
P0 admission by claiming P0 or supplying an old Date. It remains preserved
evidence, and the current-profile topic admission refuses `:stale-policy`.
An already committed P0 admission remains historical after P1. A consumer may
verify foreign historical Mini evidence while independently refusing a new
action under its current resource policy. Exact Mini historical receipt lookup
is not authorization to execute the operation again.

The active Mini P0 codec carries claimed domain/semantics/genesis pins, exact
signed call, original receipt and a bounded first-event prefix. It deliberately
carries neither fn source identity nor application operation ID. The consumer
therefore binds three explicit layers: fn source/verdict provenance, E1 stable
application operation/correlation, and Mini's verified native request/receipt.
P3 adds topic/policy/parent provenance without calculating a fourth operation
identity. A duplicate report in another topic does not automatically become
another Mini application operation; the consumer's selected namespace decides
that, with a source-independent unique operation binding.

The consumer lane confirms that any policy/alias/query change affecting selected
membership, visibility or source trust requires a new durable query/view version
and explicit rebase with a new registration epoch. V1 can conservatively rebase
on every install/conflict/alias change affecting its query. A later optimization
may retain scope only with a proof of selection equivalence. A query selecting
immutable historical admissions can retain old admissions after a policy update,
while a current-authorized-report query changes its view. These are distinct
named query semantics, never a client flag that reinterprets an old cursor.

For the first experiment, keep the existing public-group poll as transport and
let the consumer inspect topic status. Do not silently add topic filtering to
E2 v1. A future `topic-admitted-v1` query must be separately versioned and joined
to scan accounting so control/nonarticle records and empty pages advance
correctly. A denied topic projection is not a confidentiality boundary: this
profile's ordinary public archive may still expose the source.

## Migration, retention and bounds

Start with at most 16 anchored topics, 16 authors per policy, 8 parents per
report, 64 retained controls per topic and a separately charged bound on report
admissions. Use at most 16 dependency resolutions per explicit work request.
These are proposed measured-experiment limits, not universal format ceilings.
No overflow, wrapping generation or table exhaustion implicitly evicts evidence:
refuse before reservation/commit and retain the current state. Keep an explicit
lower configurable admission quota so the capacity tooth is cheap to exercise.

Anchoring authorizes only the named finite metadata/dependency budget. Incoming
articles cannot reserve arbitrary storage merely by declaring themselves topic
controls. Adopted root/control source and evidence must remain available while
current descendants or retained admission records depend on them. Charge and
create explicit owner-authorized dependency pins through existing retention
events; preserving a decoded roster without its verification context is not
enough. Release follows the existing authorized dependency-closure rules and
never follows fn consumer ack. Report availability remains subject to its own
article pins; an unavailable admitted report is an explicit E2 gap.

Legacy stores reopen with **no topic anchors/admissions**. Existing groups,
opaque policy labels and old `FN-Statement` records do not migrate into portable
topic authority. Explicit anchoring and a bounded scan may project old source
as evidence, but new admission is evaluated now, not backdated. A checkpoint
schema migration adds topic tables and their exact event-prefix relation.
Unknown topic-event versions fail replay rather than being skipped. Export/
import carries signed source; local adoption generations, article numbers,
Store positions and local administrator bindings are reconstructed locally.

All semantic values, codecs, index updates, event charges and bounds are
ACL2-owned. A carried invariant and correspondence theorem relate bounded
indexes to committed topic events. Full-store recognition is limited to open,
recovery and qualification, never per article, command or byte.

## Proof targets with discriminating counterexamples

These are proposed obligations, not theorem events or registry completion.
Implementation must attach each to the host-called subject, certify the changed
books/test closure, and add the appropriate stable requirement/proof/scenario
registry entries at contract adoption. Existing OBJ-003/006/007, REP-002 and
retention/consumer obligations are relevant but do not automatically prove P3.

| Proposed keystone | Property and necessary hypotheses | Nondegenerate witness / negative case |
| --- | --- | --- |
| Bound source projection | Successful topic extraction and accepted T10 binding refer to the exact same authored source and declared controller/keyset; assumes completed event/snapshot correspondence and the selected identity binding premise. | Valid signed root plus report; substitute metadata, received carrier, source, keyset or historical snapshot independently. In particular, the same principal with another enrolled keyset must fail. |
| Isolated topic authority | A committed event for topic A preserves B's anchor, selected policy, admissions and charged reservation when A and B have distinct topic identities and quotas. | Two active topics, different controllers and nonempty report histories; remove distinctness and show the shared topic changes. No empty-table proof. |
| Grounded fresh admission | Every new committed report admission resolves a current uncontested policy whose declared signer/keyset pair is in the roster and whose parents were admitted earlier in the same topic; assumes prepared/committed correspondence. | A real multi-parent report succeeds. Remove each of current-tip, active-lineage, keyset, same-topic, earlier-parent and matching-completion premises in separate `must-fail` witnesses. |
| Historical replay stability | After an authorized policy update removes its author, exact lookup/retry returns the identical prior admission without a new allocation, charge or report transition; assumes the exact source/context match. | Admit W under P0, install P1 excluding W, recover P0 admission. Alter one source byte or bind another source under the old lookup key and the stability conclusion no longer follows. |
| Evidence is not adoption | Observing a verified nonconflicting child changes the evidence index but not the selected policy; unverified sources cannot enter the verified edge index. | Root with two report authors, observed child changes roster, current admissions still use root until install. Matching install is the separating operation. |
| Known-fork exclusion | Once two verified distinct children of a selected lineage node are committed as evidence, no new report or successor install is accepted until a separately specified resolution transition exists; historical records remain unchanged. | Adopt P1 then P2, later learn sibling P1b at root; new report under P2 refuses. Removing distinct-child or selected-ancestor premise gives an unrelated/nonconflicting accepted case. |
| Ordered event refinement | Carried topic tables and charged dependency reservations equal replay of the completed mixed Store prefix under the maintained Store/owner relation. | Article committed without topic event, install interrupted at publication cuts, second crash during reopen. A merely prepared event must not change visible state. |
| Consumer scope preservation | Any new query/view generation refuses old-scope ack while exact historical source and application operation binding remain unchanged; assumes scope change is committed with the selection change. | Policy update between poll and ack, alias move making an old report newly selected, restore with new incarnation; omission of version/epoch checks must expose an advancing stale ack. |
| Bounded codec and work | Encoder/decoder round trip, exact canonical re-encoding, resource bound before nested parse, and per-operation cost independent of unrelated Store history under bounded indexes. | Maximum roster/parents, one-over-limit, duplicate pair, malformed length, unsupported version, two FN-Topic fields and trailing bytes. Cost test grows unrelated article history while fixed topic input remains fixed. |

The cryptographic condition is the existing selected hybrid verification
boundary plus content-identity collision resistance, not a new theorem that
Ed25519, ML-DSA-65 or a local enrollment administrator is honest. Two distinct
exact source histories hashing alike remain an explicit collision premise.
Compare exact bytes when resolving retained IDs, preserving conflicting
evidence rather than silently overwriting a dictionary entry.

## One public synthetic end-to-end scenario

This scenario extends the real P0/P1 route. Its independent observations are
the two fn stores' committed topic events and positions plus the two Mini
consumer databases. It is not satisfied by article arrival or a CLI success.

1. Create three synthetic hybrid identities: controllers A and B, and reporter
   W. Create roots TA and TB in A's fn store. TA's roster permits A and W;
   TB's permits B only. Each roster entry includes its keyset-context ID.
   Independent local administrators anchor both exact roots in both stores
   under finite budgets, with local aliases `test.topic.a` and `test.topic.b`.
   The roots can travel as ordinary fn evidence before those anchors exist.
2. W authors RA under TA's root policy carrying the actual bounded Mini P0
   first-event prefix/receipt package. RA has no report parents. A's node
   accepts the article and then commits TA admission. W authors RB under TB;
   the ordinary source is retained but TB admission refuses `:not-author`.
   No fn rejection is reported as a Mini verifier result.
3. B's consumer sleeps. The exact reports/carriers cross native peering/BP.
   B's fn node independently admits RA under its selected TA root and refuses
   topic admission of RB. Local article numbers and topic-admission Store
   sequences differ from A's. Exact source and topic/policy references agree.
4. Controller A publishes P1, a child of TA root removing W. Both stores retain
   the verified control and install it through explicit local adoption. TB's
   policy/admissions remain byte-identical. Changing alias or installing policy
   advances any affected topic-query view; an old cursor cannot silently ack
   under the new scope.
5. B wakes. It verifies RA's historical topic admission, fn source/authorship
   and Mini package with independently pinned Mini genesis/profile. In a native
   Mini transaction it records provenance, one stable application-operation
   binding and immutable reply payload Q. It uses its *current* grants for any
   local resource change. The Mini receipt must not be accepted merely because
   fn admitted TA. Q is authored by B under TB, referring to RA's exact source
   and E1 operation in its opaque payload; no cross-topic parent is claimed in
   FN-Topic. The durable signed Q posting artifact precedes its first post.
6. Kill B after Mini commit but before fn ack, reopen, and redeliver RA. It
   recovers the same Mini result/outbox and historic P0 admission, with no second
   effect. Its current-policy status separately says W is no longer permitted
   to make a fresh report. A newly arriving W report naming P0 is retained but
   receives `:stale-policy`; an old Date cannot change that result.
7. A consumes Q and verifies author/topic/correlation and its Mini/application
   result independently. Deliver a same-operation/different-source RA variant:
   the consumer retains conflict evidence without another effect or Q. No ack
   or Q releases an unrelated fn archive pin.
8. Finally publish A-signed P1b, a distinct child of the TA root, after P1 and
   a later descendant P2 have been adopted. Observation marks TA contested on
   both sites after receipt, preserves all historical records, and refuses new
   TA admission even under P2. TB still admits B's report. The test does not
   select a winning governance branch or pretend the stores agreed while one
   lacked the conflict evidence.

Repeat the article/topic-event and control-install boundaries with the existing
named publication/recovery cuts; an uncertain completion must fence further
mutation, and recovered topic/view state must be one complete committed prefix.
Record source, image, codec limits, exact receipt bytes and outcome classes.
Remeasure the actual P0 article after FN-Topic is added: its previously measured
carrier size is not a guarantee that this larger article fits every boundary.

## Work packets and consequential choices

The first implementation can proceed under the explicit experimental profile
without deciding general topic governance. Keep it coherent with active T10,
consumer and Store work rather than adding an unused policy API:

1. **Codec and source projection:** proposed `books/topic-metadata.lisp`, its
   invariant/test books, and exact-source fixtures. Reuse `identity`, CBOR,
   article parsing and T10 accessors. Prove bounded extraction and keyset/source
   binding; no served topic claim yet. Reserve `fn-th-` and update the E1 byte
   budget. This is the cheapest executable first slice.
2. **Indexed decisions and Store projection:** proposed `books/topic-history.lisp`,
   `books/topic-events.lisp`, invariant/test books, then existing `store-events`,
   `replay`, `store-node` and checkpoint families. Land carried-state/refinement,
   charging, uncertainty and source/dependency retention together. Coordinate
   event grammar and checkpoint version with the consumer lane.
3. **Called native boundary:** bounded `fn-owner-topic-step` and native request
   framing through existing owner publication. Add explicit lookup so uncertain
   install/admit settles by identity and expected pre-state. Exercise the actual
   wrapper with the scenario, not just constructor evaluation.
4. **Consumer integration:** retain existing public-group poll initially; extend
   P1 provenance with topic/admission/policy references. Join a separately named
   topic query only with durable query/view generation and scan proofs. Keep
   Mini's verifier/current-action admission and operation namespace in Lean.

No runtime prototype is committed with this design note: the useful first slice
must include the new field grammar's exact-source binding and codec proofs,
and those depend on the active T10/Store convergence. An uncalled Boolean policy
toy would add no evidence. The packet is concrete enough for that first slice
to start; this is sequencing, not a request for permission.

Only the following choices require a broader product decision when their
behavior is actually introduced:

* **Succession/delegation:** who may replace a controller keyset, attenuate
  governance authority, or recover a lost controller? V1 provides none; local
  administrator enrollment does not impersonate portable succession.
* **Legitimate forks:** whether a governance fork forms a new topic, is resolved
  by a named authority/quorum, or intentionally supports several branches.
  V1 preserves it and blocks new admissions on the contested lineage.
* **Disconnected current authority:** whether some topics require externally
  evidenced freshness/consensus before a new action. V1 states the locally
  selected policy and makes no global freshness promise. Mini may impose a
  stronger rule independently.
* **Late participation policy:** whether a previously unseen old-policy report
  should later enter a topic as historically authorized, and what trustworthy
  evidence establishes that time/epoch. V1 does not infer it from a timestamp
  or old signature; already committed historical admissions remain usable.

These choices do not prevent different independently governed topics today:
the bounded experimental roots, separate controller keysets, separate rosters,
explicit policy lineage and durable admission context already discriminate
their behavior while preserving fn's and Mini's semantic ownership.


## Validation and handoff

`make check` passed on the isolated `design/topic-history` lane based on
`de305073`, at documentation checkpoint `ac631e5d`; its output is retained
locally at `build/topic-p3-make-check.log`. This is scaffolding validation,
not certification of any proposed topic behavior. `git diff --check` passed.
Every linked external source file was compared against `git show` at its
pinned revision and matched the inspected bytes. A direct CBOR length
calculation gives proposed maximum root/control/report payloads of
1531/1447/503 bytes under the stated field limits; that arithmetic is a design
check, not an ACL2 codec theorem. No executable codec, native topic API, new
proof event, external-repository edit or live-service change is claimed.

The useful next implementation is packet 1's bounded source-owned codec and
T10 binding, followed by the actual Store/owner join. Mini and consumer lanes
confirmed that topic/policy provenance may extend their records without
changing the stable application operation key or treating fn acknowledgement
as application verification. No registry status or milestone completion is
advanced by this proposal.
