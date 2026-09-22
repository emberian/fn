# fn BP node: follow-up to the revised contract (gpt-6, 2026-09-22)

Supplied by ember on 2026-09-22 from gpt-6's second static review, of
`specs/bp-node-machine.md` as revised (`dev` 4e5e853e) and of the
coordinator's dialogue `design-dialogue-2026-09-22-bp.md`. Kept verbatim as
the record the next revision of the spec answers. Its N01 to N18 join
BP-R01 to BP-R24 as the traces the slices must pass. Its answers to the four
questions of the dialogue are the decisions unless ember says otherwise:
rotation with a publication protocol (Q1); the address-bound peer with an
explicit, boundary-naming network-trust profile and the announced EID as a
consistency check only (Q2); T4 owns Store event order and A3 the release
joins, with the dependency stated as a contract (Q3); requester-owned
receipt retry with a stable application identity and a durable outbox
disposition (Q4).

---

Review target: `emberian/fn` at `4e5e853e1d4afebbbe5f25ddade0715b6a93e080`.
Date: 2026-09-22.
Basis: the coordinator's feedback, the revised `specs/bp-node-machine.md`, the source files named below, ACL2's documentation and upstream example, RFC 9174, RFC 9172, and CCSDS 734.3-B-1.

**Scope:** static source/design review and proposed proof/test contracts. No new ACL2 certification, native-image build, platform qualification, or process-death campaign was run. New function names below are proposals, not existing certified definitions. GitHub did not resolve `w25/bp-obligation-vertical`, `d9816877`, `c6270e3e`, or `faf16519`; consequently the exact Store-commit dependency requested in Q3 remains unverified. Their existence on a developer's local repository is not disputed.

## 0. Summary

The revision materially repairs the first design. In particular, the combined slice-A gate explicitly waits for A2 and A3 and checks the actual owner Store rather than a workflow projection. Keep that integration structure.

The next corrections are primarily about three things:

1. A carrier binding now serves as idempotence evidence, outbox handoff evidence, and report-correlation metadata. Those are not all evictable caches.
2. A deterministic oldest-first selector is not necessarily a progress-making selector. Blocked entries can monopolize the progress branch.
3. Abstract codec proofs, executed attachments, and exact wire-format conformance are distinct assurance subjects.

Before certifying the proposed statements verbatim, repair the re-fragmentation theorem, the administrative-reception precondition, the single-epoch replay domain, the ambiguous-publication history, the progress assumptions, the K6 arity mismatch, and the TCPCL final-ACK statement. Before accepting the round-trip gate, exercise lost receipts with a delivered report present, history eviction, an older blocked entry, and an uncertainty callback delivered before restart.

## 1. Answers to the four decisions

### Q1. Journal lifetime: narrow rotation, but with a publication protocol

Choose the narrow operator-controlled rotation. Do not describe it as only one checkpoint record and one projection theorem. Projection equality is the semantic half; selecting the new generation durably and recovering every publication cut is the other half.

For a v0 version, quiesce the service, drain or cancel outstanding operations, finish known publications, and recover any uncertainty before taking a checkpoint. Fix a particular logical frontier. Write a complete checkpoint into a new generation using bounded chunks or immutable referenced objects plus a manifest. Barrier the objects and their namespace, then publish and barrier the authoritative generation selection. Only after that may the old generation cease to be recovery authority.

Recovery must distinguish incomplete staging, a complete but unselected new generation, a selected complete new generation, and ambiguous or damaged authority. It must not silently fall back to an older apparently valid generation after a newer generation could have acknowledged operations.

The checkpoint needs every fact necessary to continue and interpret operations: live entries; stable allocation frontiers; submission outcomes and receipt-handoff dispositions; carrier correlation retained by policy; open fragment plans and remaining reservations; durable age evidence; and configuration/policy provenance needed by the chosen projection. Volatile sessions and delivery markers are not historical authority.

Two concrete implementation constraints follow from the current representation:

- One ordinary lifecycle frame is bounded to 134,144 payload octets, while multiple permitted held bundles already exceed that. A single logical checkpoint need not be a single physical frame. Merely increasing the parser's bound would require a separate resource argument.
- Do not reset logical arrival/operation identities when a physical segment rotates. New entries must not sort ahead of old entries because a local file index returned to zero, and old completions must not match newly allocated operations. Keep globally monotone logical frontiers; count records per physical generation separately. The creation-sequence allocator remains a distinct non-reuse frontier.

The proof obligations are: exact checkpoint projection, recoverable generation selection, preservation of acknowledged history, continuation reconstruction, non-reuse of logical identifiers, and affordability of rotation for every admitted state. These can reuse the existing publication/byte-store infrastructure; they do not require general compaction or changing retention policy.

The generation switch should be a small extension of T6 and the publication model, with a cut table, not a second storage system.

### Q2. Authenticating a BP principal: use the address-bound mechanism with an explicit network-trust profile

Use option (c)'s concrete mechanism under option (b)'s explicit trust declaration. In a controlled v0 deployment, the configured channel/address selects a candidate peer principal; the announced EID is checked for agreement with that peer. It does not select the principal and does not grant additional authority.

Conceptually:

```
observed socket/channel -> configured peer -> allowed EID check -> admitted principal
```

not:

```
announced EID -> privileged peer lookup
```

The assumption must describe the actual boundary: listener/interface or network namespace, allowed peer address, proxy/NAT behavior where relevant, and which other processes can originate connections through that boundary. Loopback alone does not distinguish two mutually untrusted local processes. A configuration row saying only `bp-trust network` is underspecified unless it names that boundary.

This is the same kind of trust statement as NNTP source-address admission if the observed path, peer selection, and adversary assumptions really are the same. TCPCL's extra EID does not weaken it when used only as a consistency check. It does weaken it if an unverified announcement is allowed to override the configured peer identity. RFC 9174 section 4.6 specifically cautions against using unauthenticated node IDs for discovery or routing.

Use this explicit profile for the controlled two-process gate. Do not infer cryptographic origin authentication from it. An authenticated hop is also not evidence that the peer will keep its promises, nor that the bundle's original source or receipt issuer is that hop.

### Q3. Store event-order commits: retain T4 ownership, expose the dependency as a contract

T4 should own Store event-order changes; A3 should own the release joins. That ownership split does not eliminate a dependency. A3's native gate needs a Store contract that guarantees that a retention event is ordered against the right accepted transaction, completed against the exact pending operation, applied to the authoritative owner Store, and recovered in the same order.

The needed consequence is a commutative statement: the retention state obtained by successful live completion of the release event agrees with the retention state recovered from its committed ordered history, with the article/index/configuration deltas appropriate to that event arm. The independent archive pin remains.

The source evidence available here does not identify which of the eight branch commits establishes that consequence. GitHub returned "Branch not found" for `w25/bp-obligation-vertical`, and "No commit found" for the sampled IDs `d9816877`, `c6270e3e`, and the release-join source `faf16519`. Do not mark any of them unnecessary or integrated based on this review.

The missing input for an exact commit answer is the branch/patch series. Until then: A3 can develop its definitions and tests against the stated Store interface; its integration evidence depends on the T4 interface theorem and the actual owner-path test, not on a guessed commit number.

### Q4. Expired receipt carriers: requester-owned retry, with stable application identity

Agree with requester-owned retry. The receiver should not infer that an expired receipt carrier remains wanted. But distinguish the unchanged application request from the new delivery/transport attempt that triggers another reply.

`books/bp-adu.lisp` defines the request using work ID, subject, source/destination, policy, incarnation, authorization context, terms, and article bytes. `fn-bpaj-request-status` looks up existing state by work ID and rejects a different request under that work ID before reaching its committed-receipt branch. Therefore the new request ID in the receipt-submission key must be an explicitly defined carrier/attempt identity, not an arbitrary change to the application request.

The desired trace is: same authorized application request, new incoming attempt identity, same committed receipt fact, new receipt-carrier submission. No second article acceptance or pin allocation occurs.

There is also a representation problem to repair first: the outbox currently defines a receipt as owed whenever its carrier binding is absent. History-pressure eviction removes that binding. On the next recovery the receiver reauthors the old receipt, contrary to requester-only retry. A durable outbox handoff disposition must survive independently of the evictable report index.

Finally, a receipt-wait timer bounds the next local retry opportunity, not delivery time across arbitrary disconnected links. Any finite completion bound needs forward and return service opportunities and resource assumptions.

## 2. Highest-priority amendments to the current contract

### 2.1 Binding retirement currently changes authoritative behavior

Sections 2.4, 4.4, and 9.4 use the same carrier table for three purposes:

- interpreting a report after payload discard;
- answering repeated submissions from a persisted result;
- deciding whether a committed receipt still needs an FNBS handoff.

Section 2.4 says history-pressure removal loses only report interpretation. That is false for the stated consumers. Removing a binding can turn a previously completed submission into a new one and a completed receipt handoff into owed output.

A minimal separation is logical, not another machine:

```
Submission outcome: authoritative; stable submission, destination,
                    request/content binding, chosen bundle ID/sequence, result.
Receipt handoff:     authoritative; reply trigger and handed-off disposition.
Report correlation: bounded observational index from carrier IDs to attempts.
```

An authoritative outcome can eventually be compacted into a safe generation watermark or another closed-operation summary. It cannot be evicted as an ordinary cache while callers still distinguish "completed" from "never happened" by its presence. State the idempotency window and stale-operation behavior explicitly if the guarantee is bounded.

The current carrier record also lacks fields for several specified post-discard decisions: destination, full immutable bundle projection or its supported commitment, and the arrival/expiry evidence used for pressure retirement. An ADU content ID is not the whole immutable bundle projection. Add the compact authoritative fields, or name a proved bounded lookup of them. Do not put a full historical-journal rescan into a served decision. Hash-based comparison must retain its explicit collision assumption rather than silently become an exact-byte theorem.

### 2.2 Oldest-first selection can block unrelated useful work

Section 4.2 chooses the oldest undispatched entry before asking whether it has a route. With an older unroutable transit entry and a later local deliverable entry, each progress event selects the former, emits `:no-known-route`, and never reaches the delivery branch. The later entry and even discardable entries can remain blocked indefinitely. Timer-triggered re-entry and a bounded yield do not fix the selection rule.

The same issue occurs within forwarding when the oldest candidate has an infeasible MRU and a later smaller candidate fits; delivery can also repeatedly select a busy older item.

Select among **enabled candidates**. A blocked candidate should have a dependency-specific wait condition: a route-generation change, a suitable session/MRU change, owner availability, or a missing-fragment update. It should not be reconsidered ahead of everything else on every unrelated tick.

Retain arrival order among eligible candidates, but give cleanup and other ready action classes bounded service as well. This changes the FIFO statement to the property the service actually needs: least arrival among eligible candidates, not least arrival regardless of whether an action can run.

### 2.3 A delivered report can disable the proposed receipt-loss retry

Section 9.6 names `:forwarded`, `:attempted`, and `:bundle-created` as overdue-retry statuses. It does not name `:delivered`. Section 7.6 delivers report observations into the workflow, whose transport lifecycle can advance to `:delivered`.

Counterexample: the destination accepts the request, its delivery report reaches the requester, and its application receipt does not. The work remains outstanding, as T5 correctly requires, but it is no longer in the proposed overdue predicate's domain. This failure does not require a dishonest peer.

The simplest repair is to define receipt overdue over unresolved work and its stable retry terms, not a whitelist of remote transport statuses. Receiving a report must not silently postpone that deadline. Alternatively, keep remote reports in a diagnostic state separate from the local attempt state.

A proof that a run progresses with every report dropped does not prove that a run cannot be stopped by a report that arrives.

### 2.4 Cleanup reserve must be an invariant over all record transitions

The rule "leave cleanup-reserve plus two tokens per live entry" is a useful starting potential, not yet a preservation argument. Failed forwarding result records consume journal space but do not retire a carrier. They are currently exempt from the reserve.

For example, let the available budget before an attempt be `C + 2N + 1`. Spending one token on the attempt can leave the stated `C + 2N` reserve. An exempt failed-result record then leaves `C + 2N - 1`, with the same N live entries still needing retirement.

Define cleanup debt `D(s)` and preserve:

```
remaining_records(s) >= D(s) + rotation_control_reserve(s)
```

Every transition either spends free credit, decreases the debt by at least its cost, or reserves the cost of its later mandatory completion. Failed outcomes need reserved completion credit; so do family materialization and retirement. Headroom used by a report must not consume the last credit needed to close accepted work.

## 3. Review of the theorem groups

### T1: useful target, but its expiry claim is epistemic

The new T1 binds a delivery effect to a pre-existing held bundle, its dispatch token, payload, class, ingress, and non-administrative/whole status. This is a substantially better subject than a purely typed output.

Its lifetime conclusion is `expiry != :expired`, not `expiry == :live`, and certainly not a statement that the true physical age is within lifetime. Name that scope consistently. An uncertain observation is permitted by the stated branch.

Also state that the delivered ADU class is one of the supported request/receipt classes, rather than merely equal to an unconstrained classifier result. Specify the durable disposition of a whole local bundle whose ADU class is unsupported; it must not disappear into an unmodeled callback refusal.

### T2 and T3: constructor repairs are good; the teeth still need exact logical checks

Under the enumerated transition cases, the whole-bundle and fragment distinction removes the previous obvious conflict. Discard and deletion now have distinct subjects. The uncertainty theorem appropriately constrains expiry evidence rather than requiring the outer event to be `:clock`.

Some listed negative examples are not counterexamples to the stated implication. A delivered entry being discarded does not refute a theorem whose antecedent requires a proposed deletion record. Likewise, dropping one hypothesis does not permit dropping other retained hypotheses at the same time.

For each negative tooth assert every retained hypothesis, the failure of the omitted one where relevant, and the negation of the conclusion. If no such state exists because the hypothesis is redundant, remove it. For arbitrary-event theorems, include invalid and stale completion events as their own boundary tests.

### T4: the primary restoration theorem still permits an already-fragmented parent

`fn-bpf-fragmentablep` tests that fragmentation is not forbidden. It does not require a whole parent. Consequently the proposed theorem permits an already-fragmented primary p, while concluding that clearing a child's fragment flag and fragment fields returns p. That cannot recover a p whose fragment flag was already set.

Separate the contracts:

- Whole-parent fragmentation: require a whole parent, the appropriate nonempty payload/total contract, and a successful plan. Unfragmentation restores that whole primary.
- Re-fragmentation: preserve the original ADU key and total, and compose offsets relative to the parent's original offset. Do not claim that unfragmenting restores a fragment primary.

The fast reassembler equivalence is only conditional on `fn-bpf-inputsp`. That does not cover invalid-input behavior. Either prove equality for all inputs, including `:invalid :bounds`, or make the native caller's validation boundary explicit and prove it.

The reassembly theorem also needs an explicit offset-zero witness and a header/total coherence predicate. Section 7.2 uses the offset-zero fragment's metadata, while the theorem uses the first ID and the prose orders active fragments by arrival. Do not silently identify first arrival with offset zero. Payload agreement alone does not establish all primary/extension metadata coherence.

### T5: distinguish an administrative input from reaching the administrative branch

The received-administrative theorem currently promises only observations and unchanged state from a `decodes-to-local-administrative` predicate. Reception checks flags, unsupported blocks, and duplicate conflicts before administrative dispatch. A decodable local administrative bundle with a conflicting immutable projection can therefore take the conflict branch and propose kind 14.

If the predicate is intended to include all earlier admission checks and absence of conflict, define that explicitly. Otherwise weaken the effect-class statement to include the actual refusals/conflict diagnostics while retaining the important semantic prohibition: no application delivery, receipt authority, or obligation release.

The corrected transport theorem does establish that no transport event closes any work. It does not establish that observations preserve retry eligibility or deadlines; the delivered-report counterexample above is a separate required property.

### T6: a running epoch is not an arbitrary event list

The confirmed-journal theorem permits any `fn-bpn-machine-event-listp`, including restart events. Restart clears forwarding attempts and reanchors held records, while a confirmed journal collects only successful persistence callbacks. A trace containing restart can therefore change retained fields of the durable projection without adding a confirmed record.

State the live/confirmed-journal equation over one running epoch, whose base has already been recovered. State recovery as the bridge between epochs. Alternatively, make restart a first-class history transition and include it in the semantics being replayed. Do not let a type recognizer stand in for the execution protocol.

There is also a missing ambiguous-publication case. `fn-bpn-observed-journal-p` currently allows the confirmed journal, or that journal plus the record pending at trace end. But the existing `fn-bpn-persist-result-step` clears the pending proposal when it fences for uncertainty. A file may be visible in the authoritative namespace, the uncertainty callback may already have run, and only then may the process die. The pending-at-end record is then absent from machine state even though recovery can find the file.

Track the issued-but-unresolved publication independently of the volatile pending field, or retain an explicit ambiguous publication in the fenced state. The observed-journal relation must depend on issued operations and the physical cut, not only successful callbacks and a surviving pending slot.

Two-sided normalization is useful only together with a fixed-point property for the actual recovery result. Otherwise it can erase the very bad anchors or inflight markers the recovery implementation forgot to clear. Prefer either:

```
recovered_state = normalize(expected_cut_state, observation)
```

or the two-sided equation plus `normalize(recovered_state, observation) = recovered_state` over the claimed projection. Clearing attempts must hold for unanchored entries too; the current reanchoring theorem puts `consp anchor` in the antecedent of its `null attempt` conclusion.

Finally, the queue-acceptance theorem should expose the exact submission/request binding, not merely the presence of some carrier and its returned bundle ID/sequence. Bind destination and ADU identity, answer submission, and the matching persistence token in the statement the registry cites.

### K6: one definite arity error, and a peer-identifier ambiguity

The proposed `fn-bpaj-bind-is-the-exact-accepted-record` calls `fn-bpaj-record-matches-requestp` with two arguments. The definition at the reviewed commit takes three:

```
(fn-bpaj-record-matches-requestp store record request)
```

The missing Store argument is substantive: that predicate uses it to establish accepted-record membership.

Also clarify `fn-bpaj-ingress-peer`: its prose says it returns a configured peer record, but the shared `fn-peer-decide-transfer` uses its peer argument as the key passed to `fn-cfg-peer-find`. Return the expected peer identifier, or explicitly project it. The two objects should not share an ambiguously named formal.

### Section 5.7: the current assumptions do not imply the stated progress conclusion

Several independent problems need resolution:

- Track a stable obligation identity and look it up in each future state. The description `owedp h st` begins with whether the supplied h is retained; an immutable old record does not become unretained when its current replacement changes.
- `A-BP-OWNER` allows any response other than `:busy`. An owner returning `:uncertain` indefinitely satisfies those words but never permits terminal delivery. Require a definitive response, with a separate bounded recovery premise if uncertainty is allowed.
- `A-BP-PEER` promises completion of some attempt in a session, not service of the target's eligible queue prefix. That is insufficient for a per-carrier bound.
- A retained fragment waiting for missing data has no assumption that the missing material ever arrives. A route-less entry has no assumption that a usable route appears. A general owed-state theorem cannot silently treat either as forward-pending.
- A rank among carriers for one next hop does not bound time consumed by a global dispatch queue, owner delivery, persistence, or fragments unless the service loop gives each class a bound.

Prove separate route-waiting, forwardable, locally deliverable, incomplete-family, and requester-retry lemmas. Compose them under the dependencies each actually needs. The safety theorem should still hold when those environmental progress premises fail.

## 4. The codec boundary: answers to section 3.1

### Guard facts: yes, as logical interface properties

A caller's guard proof must be derivable from the exported logical interface. The constrained decoder's input guard does not, by itself, prove that its output is a record suitable for the next function. Export success-implies-record, projection type facts, consumed-length bounds, and any other facts downstream guards genuinely use.

For an ordinary checked `defattach`, the implementation is guard-verified, the interface guard must imply the implementation guard, and the implementation must satisfy the abstract constraints. Do not use trust-tagged skip-checks to compensate for an interface that failed to state its contract.

### Ground vectors: both surfaces, with different claims

Keep three small families of checks:

1. Abstract proof books: derive protocol/state properties from the seam's constraints, without depending on which attachment executes.
2. Concrete codec books: exact wire-vector and grammar/conformance facts about the concrete functions.
3. Attachment/image smoke tests: execute the public functions through the actual production attachment and compare their results with the concrete functions on the same vectors.

ACL2's upstream `books/misc/defattach-example.lisp` explicitly distinguishes an `assert-event` computation through an attachment from a theorem of the ordinary logical theory. An executable attachment does not let the theorem prover replace the constrained function with its target when simplifying a ground conjecture. Exact-byte facts needed as logical premises must come from the concrete definitions or from deliberately exported constraints/refinement instances, not from a passing attached evaluation.

Record the production attachment configuration in the image evidence. Reattachment is a behavioral change even if all abstract interface theorems remain true.

### Round trips and canonicality do not identify this wire language

Let E and D be a codec and let pi be a length-preserving permutation of its accepted encodings. Then

```
E'(x) = pi(E(x))
D'(b) = D(pi^{-1}(b))
```

has the same inverse laws and can have the same canonicality and size bounds. It need not use the required kind byte, field order, or wire representation.

Therefore retain protocol-specific concrete conformance facts and a named refinement/functional-instantiation route for the claims that depend on those facts. Abstract inverse-law proofs alone establish a family of acceptable codecs, not RFC conformance or compatibility between independently selected attachments.

### Streaming facts: primitive contracts below, composition above

Export the properties of primitive steps that composition needs: accepted result types, consumed-prefix bounds, remaining-budget monotonicity, positive consumption where a loop relies on it, and exact residual-input behavior. Prove bounded carry, partition independence, and aggregate work in a streaming-invariants book above those primitives.

An output-size bound does not prove a work or allocation bound. A decoder that repeatedly rescans a prefix can produce a bounded result with quadratic work. Use an explicit cost model for the executable path and a refinement from the logical parser, then measure the image. Do not hide the entire streaming algorithm behind a constraint that merely assumes the desired complexity result.

Before widening T1 across the tree, certify one representative mini-closure containing a guarded downstream consumer, a concrete vector theorem, an attached `assert-event`, and a streaming split-input test. This is a bounded compatibility experiment, not a new serial review gate for every subsequent book.

## 5. Authority beyond the network profile: section 3.2

Do not replace the ingress principal with the author principal. Preserve separate roles:

- the neighboring node admitted to hand this node work;
- the signer/original author of the application statement;
- the authority allowed to issue the receipt that releases this particular obligation.

A relay can be the first, carry a statement signed by the second, and be unauthorized to act as the third. BPSec likewise distinguishes a security source from the bundle source; the roles coincide only in particular uses.

A small bridge can use the existing keyring/statement machinery: locally authorized bindings from stable principal to permitted EID/keyset and role, plus signed immutable application statements whose subject includes the claimed principal, context/epoch, application content identity, destination where relevant, and purpose/domain. A receipt needs its own issuer authorization and exact work/subject/requester/policy/terms binding. An article-author signature is not a receipt signature.

The v0 signature work should settle these subjects and preserve the identity slots, while claiming only the profiles actually verified on the image. The network-trust profile may remain an explicitly weaker admission profile for the controlled gate. Offline revocation/freshness must have an explicit known-epoch or freshness policy; transport authentication does not solve it.

## 6. Durable projection and physical cuts: section 3.3

The "confirmed prefix plus possibly one issued record" result is plausible for a serial immutable publisher, but only after relating the actual publisher to the byte model. It is a conclusion of ordering and isolation, not a complete environmental axiom by itself.

For a record published as write -> successful file barrier -> link -> authoritative-directory barrier, the model can leave a torn private staging file before the file barrier. Once the complete immutable file was successfully fenced, a crash can leave its unbarriered public name absent or present with the fenced contents. A failed staging flush must never be followed by publication. Later writes to the same inode must be excluded. A failed directory barrier may leave a complete visible record whose durability was not acknowledged.

Those are model-level conclusions under the relevant relation and I/O assumptions, not an unqualified assertion about all Linux storage devices or later media corruption. A malformed or torn authoritative record outside the supported relation must fence recovery; it is not automatically an absent transaction.

The repository's `fn-bs-store-recovery-is-a-kernel-crash` and `fn-bs-acknowledged-record-survives-byte-crash` explicitly assume `fn-bs-store-relation` and a byte crash image; the latter also uses `fn-snt-relation`. The documented K0 general preservation gap is precisely why quoting K1-K4 does not establish that every native FNBS publisher execution produces a related state.

Name the FNBS publisher's relation and show how its actual operation sequence preserves it, including the cut after an uncertainty callback. Recovery needs a case for an issued publication whose volatile pending field has already been cleared. Use that physical-to-observed-journal theorem as T6's premise; do not substitute an assumption that the directory atomically contains a finished logical record.

## 7. Fragment families and budgets: section 3.4

Replace a broad complete/live/retired disjunction with a conservation invariant over the planned child set. For a fixed plan P, partition its children into unmaterialized, materialized-live, and terminal-with-an-outcome. These sets are disjoint and their union is the exact planned set. Every live child has the planned identity, subrange, ADU key, total, and lineage; every terminal child has an explicit result, not an unexplained absence.

Separate three facts:

1. Materialization completed: every child was durably created or explicitly terminated under a permitted cancellation/expiry disposition.
2. Parent replacement completed: no parent bytes are still required to complete any unmaterialized child.
3. Forwarding succeeded: every required child has a qualifying successful forwarding outcome.

Finishing (1) is not proof of (3). After all children are materialized, the parent can disappear even if children later expire; the family outcome records that failure and the application retry policy remains responsible for the work. A parent expiring before materialization completes must have a defined transactionally safe way to terminate the unmaterialized suffix and release reservations.

Reservations must cover live plus committed future allocations, not just an independent staging counter. Preserve both slot and byte inequalities across conversion of reserved children into live children. Journal debt includes materialization, result, and retirement records. A useful internal rank is the number of unresolved materialization slots; forwarding progress is a separate rank under its service assumptions.

Reassembly is the receiving node's local active-set decision, not an interpretation of the sender's private family plan. Exclude locally consumed/deleted entries from active covers; do not globally blacklist an ADU because one local copy was retired. Check identity, total/header compatibility, and admitted-principal compatibility before combining fragments. Retransmitted fragments after successful reassembly also need an explicit duplicate/disposition path rather than an impossible second insertion of the same whole-bundle ID.

Check actual forwarding-image size again at send time. An image that fits at plan time may grow when its age encoding crosses a CBOR width boundary. Either reserve a proved worst-case mutable-header envelope or allow a specified re-plan/re-fragment path; this is another reason the re-fragmentation theorem must be distinct.

## 8. Observable conditional progress: section 3.5

Keep logical service turns for an internal proof, but do not present them as a deployment timing guarantee without a relation to elapsed time and service capacity.

CCSDS 734.3-B-1, Schedule-Aware Bundle Routing (July 2019), provides a useful vocabulary: directed contacts with start/end times, sender/receiver identities, and an expected data rate, together with range intervals and route timing. This supplies a planning model, not a promise that the scheduled contact will actually work. Reuse the vocabulary without importing unrelated custody assumptions from that older document.

For a deployable profile, describe an opportunity as a session/contact interval with a usable byte budget after overhead, MTU/MRU limits, and observed completion latency. A session opening briefly is not necessarily a transfer opportunity for this bundle. A return route in a table is not a future return contact with enough capacity.

Monitor each premise with an operational witness:

| Premise | Useful observation |
| --- | --- |
| contact service | expected versus actual start/end; usable duration; bytes offered and completed; largest missed opportunity |
| persistence | operation ID, issued/barrier/result timestamps, definitive versus uncertain outcomes, longest outstanding publication |
| peer service | per-eligible-carrier waiting age, refusal codes, completed-byte budget; not merely some unrelated successful attempt |
| owner service | busy intervals, definitive responses, uncertainty/recovery intervals |
| journal service | free records minus cleanup debt and rotation reserve |
| return service | feasible timed route and eligible receipt progress, not only an EID route entry |

A monitor can establish compliance on an observed finite prefix and detect violations; it cannot prove that future contacts will occur. Preserve that difference in the node's page.

An `encapsulate` with a local witness proves consistency of a constrained interface. It does not by itself connect a boolean assumption to the actual environment consumed by `fn-bps-run`. The predicates/constraints must relate the same trace, operation IDs, target carrier, and time/service index used in the conclusion.

## 9. What reports are for: section 3.6

Reports remain useful for explaining where progress stopped, identifying a peer's stated refusal/deletion reason, comparing observed and planned routes, and diagnosing interoperability. Independent vectors prove the codec portion, not the entire value of the facility.

For v0, use reports as labeled remote observations, not release authority or a prerequisite for retry. Separate them from local carrier-completion facts. A report that says delivered must not disable the receipt timer, a replayed report must not move the deadline, and a stale attempt's report must not affect a newer attempt.

Authenticated reports could later influence bounded scheduling preferences or operator decisions. Such an optimization needs its own authority, staleness, and resource policy; it must not silently become part of the safety or progress premise. Bound report parsing/logging/correlation work so diagnostic traffic does not consume the service budget needed by accepted work.

## 10. What A1's gate should add

The combined slice-A gate already waits for A2/A3 and checks owner-Store pin state. Keep it. Strengthen it in three ways.

First, identify the objects and authority, not only their counts. Match work ID, request bytes/content subject, accepted Store transaction, receipt issuer/context, and the exact forwarding pin released. Keep a second control work whose pin must remain; an implementation releasing the wrong pin can otherwise preserve the aggregate count.

Second, land the minimal service-loop reducer and its correlation invariant with A1. The brief currently places the minimal loop in the native host while the full loop book is new in B. It is fine for B to add contact scheduling and richer fairness, but the A1 proof boundary must already cover the semantics that decide which completion releases which ACK/effect. Do not prove a pending-record machine while its actual callback/queue policy exists only in raw host code.

Third, distinguish partial ACKs from the withheld successful final ACK. Section 9.2's proposed TCPCL keystone says no XFER_ACK for a refused transfer. A multi-segment transfer can already have valid partial acknowledgments before its END disposition refuses capacity. The meaningful theorem is that this late-refused transfer does not receive a successful final END acknowledgment from this path. The sender must not infer whole-bundle completion from acknowledged prefixes.

There is a planning dependency to fix: B's report-present relay gate needs deletion-report generation, while D2 assigns generation/demultiplexing after B and C2. D1's codec alone cannot produce the report. Move the minimal generation/consumption behavior before that B gate; leave broader foreign vectors and the rest of D2's conformance matrix later.

### New counterexample/gate traces

These are review labels, not newly allocated repository requirement IDs.

| Label | Trace | Required observation |
| --- | --- | --- |
| N01 | Store receipt carrier; discard; evict only report history; recover | old handed-off receipt does not become newly owed |
| N02 | Same unresolved work; delivered report arrives; application receipt is lost | retry eligibility/deadline remain effective |
| N03 | Old route-less carrier plus newer locally deliverable carrier | newer work delivers; old work retains its named route wakeup |
| N04 | Old infeasible-MRU carrier plus newer fitting carrier | fitting carrier progresses without discarding the old one |
| N05 | Repeated failed forwarding results near reserve threshold | every admitted terminal/cleanup obligation retains its credits |
| N06 | Publish canonical file; deliver uncertainty callback; then kill/recover | visible issued record is admitted by the cut model, without fabricated confirmation |
| N07 | Durable attempt; restart with a different monotonic origin | single-epoch replay and recovery statements each apply to their proper domain |
| N08 | Unanchored entry with inflight forwarding; restart | attempt cleared despite nil age anchor |
| N09 | Fragment an already-fragmented parent | composed offsets preserved; whole-parent restoration theorem does not apply |
| N10 | Nonzero-offset fragment arrives before offset-zero fragment | reassembled primary/blocks come from the designated coherent offset-zero input |
| N11 | Structurally decodable local admin bundle conflicts with a held identity | actual refusal/conflict effects match the theorem's domain |
| N12 | Multi-segment transfer with partial ACKs, then late END capacity refusal | no successful final END ACK; partial ACK history is not misclassified |
| N13 | Retry identical application request with a fresh incoming carrier ID | same receipt fact, new reply submission, no new article allocation |
| N14 | Two independent works; receipt for only the first | exactly the first forwarding pin changes; archive pins and second work remain |
| N15 | Network peer address matches, announced EID mismatches | no admission under the announced identity |
| N16 | Rotation at every publication/selection cut, then new work and stale completion | one recovery authority; no identifier reuse; arrival ordering preserved |
| N17 | Attached codec passes vectors; logical theorem requires exact encoding | test evidence and logical conformance obligations remain distinct |
| N18 | Owner repeatedly returns uncertain rather than busy | progress premise is reported violated or bounded recovery is exercised, not falsely declared satisfied |

## 11. Source ledger

Repository sources below were read at `4e5e853e1d4afebbbe5f25ddade0715b6a93e080` unless another revision is stated. Section references are useful even when line numbers move.

- Coordinator feedback: `planning/design-dialogue-2026-09-22-bp.md`, dated 2026-09-22, especially questions 1 to 4, sections 3.1 to 3.6, and next-review priorities.
- `specs/bp-node-machine.md`: sections 2.1 to 2.7, 3.1 to 3.5, 4.1 to 4.5, T1 to T6 and 5.7, K6, sections 7.1 to 7.6, 8, 9.1 to 9.7, and slice A to E briefs. File blob: `a5b06e1a8397387a9f1d272cfbbe7e414103df1e`.
- `books/bp-node-machine.lisp:494-521`: uncertainty clears pending and fences.
- `books/bp-native-app.lisp:207-239`: request status compares the full request under an existing work ID before returning committed.
- `books/bp-native-app.lisp:347-411`: three-argument exact Store match, lookup, dispatcher, stable receipt ID.
- `books/bp-adu.lisp:44-87`: request and receipt field definitions.
- `books/peer-inbound.lisp:254-273`: shared transfer decision looks up the peer argument through `fn-cfg-peer-find`.
- `books/byte-store-keystones.lisp:30-119`: K3/K4 assumptions and subjects.
- `specs/crash-model-v2.md`: model definition and section 7's later implementation/status account; the design's opening historical status is not the current certification state.
- `planning/plan-2026-09-22-trajectory.md`: T12 integration/slice update in commit `4e5e853e`.
- ACL2 upstream `books/misc/defattach-example.lisp` at `aff7e2718fdaa45e29b7c1843ce14aeca1d22b98`: abstract proofs, functional instantiation, attachment evaluation, and the explicit distinction between an attached assertion and a logical theorem.
- ACL2 manual, DEFATTACH, version 6.2: checked attachment requirements, guard implication, proof/evaluation distinction, and attachment restrictions. The current-manual URLs did not render through the available web tool; no version-specific ACL2 8.7 experiment was run here.
- RFC 9174, sections 4.6, 5.2.3 to 5.2.4: announced node IDs, partial acknowledgment, and late refusal.
- RFC 9172, sections 1.2, 2.2, 3.1: distinct security roles and sources.
- CCSDS 734.3-B-1, July 2019, sections 2.3 to 2.4: contacts, data volumes, range intervals, and timed routes. Pages 2-4 and 2-5 were inspected as rendered PDF pages. This is a cited routing model, not a claim that it is the latest edition or that it proves delivery in an arbitrary deployment.

## Closing direction

Keep the architecture and the A1/A2/A3 combined gate. The next unit of work should be a contract patch plus its small counterexample suite, followed by implementation against those contracts, not another broad redesign. The important separation is durable authority versus discardable observation, and enabled progress versus merely ordered work. Once those are explicit, the rotation, retry, codec, and family proofs have much cleaner subjects.
