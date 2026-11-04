I would keep main’s central direction—merge evidence, preserve local acceptance, make serving policy explicit—but **I would not adopt R1–R5 as written**. T4’s “signature wins” is unsafe without a prior authority binding; T5’s cap is incompatible with unrestricted union; T8 conflates an identity namespace with a commit domain. T2 also attributes capabilities to the existing catch-up protocol that it does not have.

More fundamentally, the current implementation mixes portable evidence with local acceptance state. That is the seam I would fix before migrating `fn2-txn`. It lets us preserve the useful engine without making E4 responsible for repairing its ontology.

This is a read-only review. The recommendations below are mine, rather than additional rulings attributed to ember.

**First, what the built keystone actually establishes.**

Main correctly identifies the first-arrival premise, but “the engine implements UC’s union exactly” is too generous. UC separates a set of validated facts from local acceptance outcomes and serving choices. The implementation instead stores `:accepted` or `:conflict` as an unqualified value under `(Message-ID, content)`. Its convergence premise requires equality of those already-computed states. The statement also limits each offer sequence to forty offers and requires the content bound; those restrictions belong in any precise account of its scope. [UNIVERSAL-CONSTRUCTIONS.md:181](/Users/ember/dev/fn/build/coordinator/fn2/UNIVERSAL-CONSTRUCTIONS.md:181), [identity.lisp:16](/Users/ember/dev/fn/fn2/books/identity.lisp:16), [identity.lisp:776](/Users/ember/dev/fn/fn2/books/identity.lisp:776).

Consider:

```text
A receives: (m,a), (m,b)       B receives: (m,b), (m,a)

A records: a accepted         B records: a conflict
           b conflict                   b accepted
```

There are two perfectly compatible historical facts here: “A accepted a” and “B accepted b.” They become contradictory only because the record has erased the subject of “accepted.” The existing negative witness correctly exposes the different local results. It does not establish that those results cannot coexist in a convergent evidence structure. [identity-unit.lisp:55](/Users/ember/dev/fn/fn2/tests/identity-unit.lisp:55).

I would distinguish these subjects:

| Subject | Example | How it combines |
|---|---|---|
| Content or authored-object identity | “These immutable bytes have this name.” | Content addressing under the declared cryptographic assumption |
| Binding evidence | “This signed statement binds namespace N, name m, and content c.” | Union of identified evidence |
| Acceptance receipt | “Domain D accepted c as m at position p under revision r.” | Union of attributed historical statements |
| Local selection | “At this view, this node serves c for m.” | The domain’s declared decision/fold |
| Availability and custody | “The body is present”; “this holder owes delivery.” | Their own state machines and obligations |

These can share the ordered-run machinery. They must not share an unqualified `accepted` bit.

There is a more immediate implementation issue: `fn2-txn-decide` routes a new `:conflict` and already-known `:evidence` directly to `:refused`. Its finish path sends the response and releases the successor. That path does not commit the new conflict evidence. The identity engine can record conflicts when invoked through its recording operation, but the ordinary transaction path currently takes the very “refuse and record nothing” route that UC uses as its negative example. [txn.lisp:347](/Users/ember/dev/fn/fn2/books/txn.lisp:347), [txn.lisp:378](/Users/ember/dev/fn/fn2/books/txn.lisp:378), [txn.lisp:689](/Users/ember/dev/fn/fn2/books/txn.lisp:689), [UNIVERSAL-CONSTRUCTIONS.md:186](/Users/ember/dev/fn/build/coordinator/fn2/UNIVERSAL-CONSTRUCTIONS.md:186).

That is a pre-migration semantic defect, not an E4 transport detail.

**T1 — Local acceptance is the right base contract; “cannot be otherwise” is too broad.**

I agree that an independently operating node must be able to durably accept local work while disconnected. That is explicit in the architecture, and BP is an actual product requirement. [architecture.md:8](/Users/ember/dev/fn/docs/architecture.md:8), [EMBER.md:626](/Users/ember/dev/fn/build/coordinator/EMBER.md:626).

What is impossible under the proposed general conditions is more specific: two disconnected nodes cannot both offer unrestricted local acceptance while guaranteeing that their irrevocable choices of one content for an arbitrary shared name agree. One can instead restrict writers, preallocate authority, use content-derived names, defer acceptance, or distinguish provisional custody from authoritative acceptance. Those are meaningful profiles, not violations of disconnected operation.

Main’s options also combine two questions:

- What did this node durably accept?
- What should this node serve after learning more?

The first is historical. The second can change under an explicit policy. A later selection of another content must not rewrite a previous acceptance receipt, cancel its obligations, or turn a genuine success into “that never happened.” UC already separates merge, admission, retry identity, and outcome evidence; that separation should survive this discussion. [UNIVERSAL-CONSTRUCTIONS.md:205](/Users/ember/dev/fn/build/coordinator/fn2/UNIVERSAL-CONSTRUCTIONS.md:205).

My recommendation is therefore **T1(a) for ordinary NNTP admission, with attributed receipts and an explicit selection policy**. I also want author-controlled and application-controlled profiles, but those require the authority contract described under T4. I would not make a content-hash tie-break the general protocol rule: it gives arbitrary bytes an authority they do not possess, permits grinding for a preferred rank, and changes the referent of a familiar name as evidence arrives. It can still be a legitimate application choice.

There is another missing input to main’s convergence formula. A first-arrival serving policy cannot be computed from an unordered Binding alone. It needs the local acceptance receipt or local history. The honest equation is approximately:

```text
served = Select(
    named policy,
    pinned local decisions,
    binding evidence,
    resolution statements,
    reader authority
)
```

Equal evidence does not imply equal local decisions. Equal evidence **and equal interpretation inputs** should imply equal interpretation.

Finally, “validated facts” needs care. UC requires validation to be deterministic in a fact and its dependencies, rather than arrival order. Current enrollment, current quota, and current local policy are not immutable properties of a fact. Preserve “this signature verified under this named key state” as historical evidence; derive “this is currently admissible/authorized here” separately. Otherwise a delayed key rotation or revocation makes the supposed grow-only set shrink or depend on delivery order. [UNIVERSAL-CONSTRUCTIONS.md:186](/Users/ember/dev/fn/build/coordinator/fn2/UNIVERSAL-CONSTRUCTIONS.md:186).

**T2 — Keep the legacy offer semantics, but build a real evidence protocol.**

Main is right about the information deficit: a Message-ID-only offer cannot distinguish identical content from conflicting content. But “have it” overstates the wire promise. `CHECK`’s 438 means the article is not wanted; having a copy is one example. `TAKETHIS`’s 439 rejects the transfer and tells the sender not to retry. Neither is a portable assertion that the receiver possesses the exact offered content. [RFC 4644 §§2.4–2.5](https://www.rfc-editor.org/rfc/rfc4644.html#section-2.4).

I would preserve Message-ID-only suppression for legacy `CHECK` and `IHAVE`. That is a deliberate information loss at the legacy port. It means we cannot promise discovery of all name conflicts through ordinary legacy feeds.

For a fully received `TAKETHIS`, I agree with recording an admissible new conflict and refusing article acceptance. But replace **“always”** with a specified evidence-admission path:

1. Establish the article’s framing, identity subject, and evidence class.
2. Reserve the work and permanent metadata charge.
3. Commit the new evidence without creating article membership or an article-retention promise.
4. Return the conflict response with precisely the evidence semantics that committed.

An invalid signature, an out-of-scope object, and a valid competing binding are not interchangeable conflict evidence. Already-retained evidence should not incur a new permanent charge merely because it arrived through another connection.

The catch-up recommendation needs substantial correction. Existing `XFNCATCHUP`:

- Sends a Message-ID and article lines, with a batch chain—not a digest-bearing inventory negotiation.
- Serves only what `ARTICLE <mid>` would retrieve; withdrawn and reclaimed entries are excluded.
- Replays each verified record through local `IHAVE`, sending its body only after 335.
- Has a chain computed from the requester’s supplied prior chain.
- Explicitly documents possible undetected skips when the reader view changes.

Those facts are in [peering.md:379](/Users/ember/dev/fn/specs/peering.md:379), [peering.md:398](/Users/ember/dev/fn/specs/peering.md:398), [peering.md:412](/Users/ember/dev/fn/specs/peering.md:412), [peering.md:463](/Users/ember/dev/fn/specs/peering.md:463), and [peering.md:487](/Users/ember/dev/fn/specs/peering.md:487).

Consequently, routing conflicts “over the catch-up chain” does not solve the problem. The sender may omit the evidence entirely; the receiver may suppress the body by Message-ID; the chain authenticates neither the sender’s authority nor completeness relative to some independently committed inventory.

For fn2 peers, I recommend a distinct logical evidence stream, even if it shares framing and transport machinery with article catch-up. It should carry:

- Namespace, exact name, typed content identity, and evidence identity.
- Issuer and validation dependencies.
- Attributed acceptance or resolution statements where applicable.
- Coverage tied to an identified history, revision, scope, and cut.
- Separate availability information for bodies and dependencies.

Evidence import must not be implemented as replaying an article through a port that intentionally rejects known Message-IDs before inspecting the evidence.

There is also a durability subtlety that affects `fn2-txn` now. **Article refusal and evidence persistence are separate outcomes.** The article may be definitely refused while the evidence commit is uncertain. A response claiming “conflict recorded” must wait for that commit; a lost response must not double-charge on replay. For streaming NNTP, temporary inability to process has a 400-and-close path; one cannot simply reuse POST’s numeric outcome mapping. [RFC 4644 §2.5.2](https://www.rfc-editor.org/rfc/rfc4644.html#section-2.5.2). The local POST contract already treats durable completion and uncertainty carefully, but its existing “refusal” machinery was written around article acceptance, not a refusal that commits another kind of event. [nntp.md:734](/Users/ember/dev/fn/specs/nntp.md:734).

**T3 — Pin selection, but distinguish identity, visibility, availability, and permission.**

I agree with stable selection within a valid view. I disagree with the implication that resolution automatically means “old view keeps the old content.”

The storage decision promises stable selection and identity, while explicitly allowing named availability and authorization-change outcomes. A pin is not a body-retention obligation. A BODY response acquires a lease before promising success. [STORAGE-DESIGN.md:22](/Users/ember/dev/fn/build/coordinator/fn2/STORAGE-DESIGN.md:22), [STORAGE-DESIGN.md:33](/Users/ember/dev/fn/build/coordinator/fn2/STORAGE-DESIGN.md:33).

The useful promise is:

> A valid view does not silently substitute different content for the selected identity. It may report that the selected content is unavailable or no longer authorized under the declared read contract.

That accommodates both erasure and access tightening without pretending a connection pin preserves bytes forever.

We also need a distinction between lookup by Message-ID and lookup by local article number. If an operator explicitly selects another candidate for a Message-ID, an already-allocated article number must not silently begin naming the replacement. Otherwise old overview results, cursors, and references change their subject. A superseding article ordinarily gets its own identity and membership; the old article becomes withdrawn, rather than changing its bytes in place.

I support identity metadata, but I would not freeze main’s proposed `:fn-identity` value yet:

- `contents count` means **locally known, disclosed candidates at this cut**, not a global cardinality.
- `conflicted` must say which evidence class qualifies.
- `accepted-by` must identify the issuer and receipt, not suggest that a remote node’s assertion is an independently verified fact.
- Saturation or incomplete synchronization must be visible.
- “No conflict known” must not become “this name is globally unambiguous.”

UC itself says a node cannot certify global absence of conflict from its local section. [UNIVERSAL-CONSTRUCTIONS.md:231](/Users/ember/dev/fn/build/coordinator/fn2/UNIVERSAL-CONSTRUCTIONS.md:231).

There is a disclosure issue too. Existing identity-related HDR metadata is generally available only for an article the pinned view serves. A new identity query that reveals hidden candidates, private-group membership, or retained tombstones would expand that boundary. [peering.md:2104](/Users/ember/dev/fn/specs/peering.md:2104). Even a count can reveal that someone else submitted a private competing object.

My recommendation: settle the typed read result now—selection, evidence status, availability, coverage, authorization—and implement the precise HDR syntax with the reader surface. **An HDR feature is not a prerequisite for migrating the transaction machine; the facts it will eventually report are.**

**T4 — The attack is real; “the signature wins” is not a defense as stated.**

This is my strongest disagreement after T8.

Suppose Mallory sees unsigned `<m@example>` and signs different content under Mallory’s perfectly valid key. Nothing about that signature establishes ownership of `<m@example>`. If a signature outranks an unsigned arrival merely because it verifies, Mallory has gained a name-hijacking operation.

The necessary chain is:

```text
signature valid
    + signer authorized for this namespace/name/operation
    + relevant grant/key state established
    + competing-authority/equivocation policy
    ⇒ eligible authoritative decision
```

These are distinct checks.

The sealed-stream decision says the signature authenticates the immutable envelope and ciphertext. It expressly separates node acceptance from recipient acceptance and says endorsement of bytes does not establish correct encryption. It does not say every signer owns every Message-ID it signs. [STORAGE-DESIGN.md:39](/Users/ember/dev/fn/build/coordinator/fn2/STORAGE-DESIGN.md:39).

Nor does D23 authorize adopting a trusted carrier’s first arrival as the truth about the author. D23 says the receiver verifies against the author’s own enrollment; an intermediary unable to verify may carry and forward with a verdict that says so. The peering specification is particularly direct: the allowlist admits the item and does not vouch for it. [decisions.md:1087](/Users/ember/dev/fn/planning/decisions.md:1087), [peering.md:172](/Users/ember/dev/fn/specs/peering.md:172).

I would distinguish three attacks:

- **Name squatting:** another party binds an existing free-form name to different bytes.
- **Authority equivocation:** an authorized signer makes incompatible statements under a rule that forbids both.
- **Evidence poisoning:** an attacker causes false, weak, or irrelevant assertions to consume storage or influence selection.

A Binding can represent all three, but the predicates and consequences differ. “Two content identities under one Message-ID” does not prove signer misconduct.

For native streams, stronger alternatives are available: names scoped by an established stream authority, self-certifying author namespaces, or identifiers whose binding to an authority is established at genesis. The same authority may still equivocate. A signature then makes the equivocation attributable; it does not choose the correct branch.

For unsigned NNTP, I accept first admissible local arrival as the default. Conflict visibility is useful, but only under an explicit dissemination contract. An eclipsed node, a legacy-only feed, or a saturated evidence store may never learn of the competing content. “Union makes it visible everywhere” is conditional on the very availability and admission questions still being designed.

DTN sharpens this. A bundle can arrive before its signer enrollment, chain predecessor, grant, or revocation evidence. Such an object may be carried or held pending, but must not be silently promoted to authoritative content. A later dependency should be able to add a new validation fact without rewriting the historical carriage verdict. The existing enrollment metadata already separates historical verification, current enrollment, historical acceptance, and current administrative authority; fn2 should preserve that discipline. [peering.md:2124](/Users/ember/dev/fn/specs/peering.md:2124).

**T5 — Two quotas are useful, but they do not repair the algebra or prevent poisoning.**

Main correctly sees permanent evidence as a resource obligation. The recommendation does not follow from that observation.

Let two nodes each have a valid four-content state:

```text
A(m) = {a,b,c,d}
B(m) = {a,e,f,g}
```

Their union has seven contents. The set of states satisfying “at most four contents per Message-ID” is not closed under union.

The current implementation makes this a semantic boundary: additional conflicting offers are recorded nowhere, and the decision scan is cut short using a constant derived from the four-content limit. [identity.lisp:22](/Users/ember/dev/fn/fn2/books/identity.lisp:22), [identity.lisp:151](/Users/ember/dev/fn/fn2/books/identity.lisp:151).

Adding a per-offerer window does not fix this. An attacker can consume the shared slots before an honest origin arrives, distribute offers across principals or carriers, or slowly accumulate permanent state across many windows. Conversely, an honest relay may deliver a burst of previously disconnected evidence. Exhausting its budget is not evidence that its “standing” should fall.

We need to choose among genuinely different contracts:

1. **Exact union of retained facts, with resource admission and explicit incomplete synchronization.** The data structure has no semantic four-entry ceiling; the operator’s supported profile and sponsor reservations determine what can currently be admitted. Refusal leaves coverage incomplete.
2. **A bounded convergent abstraction.** For example, a separately defined saturated-conflict state can preserve “a conflict exists” while ceasing to enumerate all candidates. This changes the observations we promise. It cannot silently retain exact-count and arbitrary-candidate duplicate claims.
3. **A globally bounded exact candidate set.** This needs a coordinated allocation rule or a declared replacement rule. First-arrival admission at each replica does not produce it.

I recommend **option 1**. Keep permanent accepted identity metadata and admitted evidence; make missing evidence explicit; reserve resources before accepting the obligation. If a later product needs option 2, give it its own summary theorem and user-visible loss contract.

That does not require unbounded work for a lookup. I would restructure the index around an exact `(namespace, Message-ID, content)` lookup plus a per-name summary and a separately pageable evidence cursor. An admission query needs to know whether this content exists, whether another exists, and what local acceptance says. It does not inherently need to walk every competing content. This fits the existing law that served paths carry preserved invariants rather than repeatedly reconstructing them.

The accounting should distinguish:

- Work spent parsing, hashing, checking signatures, and fetching dependencies.
- Outstanding permanent evidence storage.
- Article-body retention.
- Sender, author, sponsor, and relay liability.

A rate window addresses the first category imperfectly and the second not at all. Existing storage policy already says obligations survive account deletion and permanent identity metadata must be separately observable. [STORAGE-DESIGN.md:35](/Users/ember/dev/fn/build/coordinator/fn2/STORAGE-DESIGN.md:35).

I would also count **evidence**, not just contents. A single content can accumulate many signatures, receipts, or validation dependencies. The current schema has one `binding` and `principal` value per content, and duplicate/evidence reoffers record nothing. That is insufficient if new testimony about the same content is meant to propagate. [identity.lisp:16](/Users/ember/dev/fn/fn2/books/identity.lisp:16), [identity.lisp:500](/Users/ember/dev/fn/fn2/books/identity.lisp:500).

The quota ruling must precede the transaction migration because it determines reservations, terminal outcomes, and the evidence record’s shape. Exact default values can wait.

**T6 — Preserve identity after erasure; expand the state model beyond “have it.”**

I agree with the permanent exact-Message-ID ruling. Ember’s instruction is clear, and the storage decision explicitly retains content identity, acceptance binding, and conflict state. [EMBER.md:459](/Users/ember/dev/fn/build/coordinator/EMBER.md:459), [STORAGE-DESIGN.md:41](/Users/ember/dev/fn/build/coordinator/fn2/STORAGE-DESIGN.md:41).

But one retention test is not enough. At least these conditions must remain distinct:

- Accepted locally; body available.
- Accepted locally; body reclaimed.
- Known only as conflict evidence.
- Withdrawn from current serving.
- Held under an outstanding custody or forwarding obligation.
- Known through a foreign receipt, without local acceptance.

A retry of a locally accepted `(name, content)` whose body was reclaimed must not allocate a new article or restart its old obligations. An object known only as conflict evidence must not become “already stored here”; the current identity engine deliberately distinguishes `:evidence` from `:duplicate`. [identity.lisp:43](/Users/ember/dev/fn/fn2/books/identity.lisp:43).

An authorized **repair or rehydration** operation is another matter. Restoring the bytes for an existing identity can be useful without treating them as a new publication, allocating another article number, or undoing a withdrawal. “Never reaccept as new” should not accidentally mean “never repair availability.”

Across peers, a node’s reclamation decision is not a global erasure order. Likewise, another node’s retained identity does not prove that it still holds the body. This matters acutely for BP: a duplicate/history response must not discharge a custody obligation that requires actual retention evidence. The current peering contract already distinguishes NNTP transmission receipts from BP’s application evidence and forwarding-release decisions. [peering.md:603](/Users/ember/dev/fn/specs/peering.md:603).

There is a deeper preservation requirement: **what lets a new peer validate the binding after the body has gone?**

A content digest and local event pointer may preserve the local duplicate decision while being insufficient for independent verification elsewhere. Depending on the signature construction, the verifier may need the signed envelope, source bytes, a specified proof, or an attestation from an authority it trusts. A local pointer into discarded history is not portable evidence. UC §4.5’s rule—retain sufficient dependency evidence for each promised operation—applies directly. [UNIVERSAL-CONSTRUCTIONS.md:196](/Users/ember/dev/fn/build/coordinator/fn2/UNIVERSAL-CONSTRUCTIONS.md:196).

For unsigned material, a node can attest that it observed particular bytes. That establishes an attributed observation, not original authorship. We should say so.

Finally, permanent identity is deliberately a limit on erasure. Message-IDs, content commitments, signatures, and relationships may remain identifying even when ciphertext keys disappear. The sealed-stream and integrity decisions already reject the inference that deleting keys erases previously disclosed associations. [STORAGE-DESIGN.md:37](/Users/ember/dev/fn/build/coordinator/fn2/STORAGE-DESIGN.md:37).

My recommendation is T6’s permanence rule plus explicit availability, withdrawal, repair, and custody transitions, with evidence-retention obligations included in compaction.

**T7 — Share event machinery; do not collapse cancel, supersede, approval, and equivocation into one semantic operation.**

I agree that control actions should be events and should not erase the historical evidence they act upon. A shared envelope and common authorization framework are useful.

But these actions have different subjects:

- A cancel withdraws a target under some authority and scope.
- A supersede publishes a new article and requests withdrawal of an older one.
- Approval authorizes an article’s treatment in a moderated context.
- An identity-resolution statement selects among competing bindings.

In particular, supersession is not ordinarily mutation of the old Message-ID’s bytes. The Netnews definition treats it as cancellation of the named article followed by a new article. [RFC 5536 §3.2.12](https://www.rfc-editor.org/rfc/rfc5536.html#section-3.2.12).

I would use one typed event family with distinct operations, rather than one resolution kind whose sub-kinds quietly inherit the wrong semantics. An approval must bind the exact article and relevant group or stream; approving a free-form name while its content can change is an authorization bug.

Main also overstates equivocation. Two different cancels are not inherently incompatible. Two superseding articles may be an explicit branching history. A signer issuing two children of the same previous head is equivocation only if the declared chain contract permits one successor. UC explicitly says Message-ID conflict and signer equivocation share implementation while keeping validation and key rules distinct. [UNIVERSAL-CONSTRUCTIONS.md:189](/Users/ember/dev/fn/build/coordinator/fn2/UNIVERSAL-CONSTRUCTIONS.md:189).

For chain evidence I would include the chain or stream identity and relevant authority context, not assume `(signer, previous-head)` is sufficient for every application. One key can operate several independent streams.

The essential DTN case is **cancel before target**, including a crash between them. A cancellation must either carry sufficient authority for its target scope or wait for the target-dependent checks. It must not become effective merely because a remote node says it executed it. The existing design already models cancel-before-target, freezes the local authorization decision under its historical configuration, and has each receiving node decide under its own grants. [peering.md:1948](/Users/ember/dev/fn/specs/peering.md:1948), [peering.md:1962](/Users/ember/dev/fn/specs/peering.md:1962), [peering.md:2141](/Users/ember/dev/fn/specs/peering.md:2141).

Two more qualifications:

- `control-not-filed` is a filing refusal, not a general statement that a cancellation lacks authority. Do not reuse it for authorization failures.
- “Unsigned cancels are local policy” leaves out Cancel-Lock/Cancel-Key as a possible legacy authorization mechanism. It need not be fn2’s initial profile, but it is not equivalent to unauthenticated `From` matching. Conversely, Cancel-Key authorizes withdrawal without authenticating all replacement bytes; RFC 8315 explicitly distinguishes those properties. [RFC 8315 §7](https://www.rfc-editor.org/rfc/rfc8315.html#section-7).

The common event/authority boundary should be fixed now. Full supersession, moderation, key succession, and conflict-resolution UX can wait for their respective layers.

**T8 — Add domain context, but reject “identity is per commit domain” as the universal rule.**

A commit domain answers **which changes are ordered and atomic together**. An identity namespace answers **which names are meant to designate the same thing**. A world or lineage answers **what continues through transport and revision**. These need relationships, not equality.

WIDEST explicitly permits a forest of commit domains, makes occurrence identity distinct from content identity, and requires transport to preserve observations while changing node, revision, and incarnation. None of that establishes that every Message-ID namespace is one commit domain. [WIDEST-ROLE.md:21](/Users/ember/dev/fn/build/coordinator/fn2/WIDEST-ROLE.md:21), [WIDEST-ROLE.md:26](/Users/ember/dev/fn/build/coordinator/fn2/WIDEST-ROLE.md:26), [WIDEST-ROLE.md:39](/Users/ember/dev/fn/build/coordinator/fn2/WIDEST-ROLE.md:39).

Ordinary Netnews is the immediate counterexample. Message-IDs are intended to be globally unique across Netnews and email, not unique only within one server’s transaction log. Different content under the same Message-ID is a collision in that namespace even when the copies reside in different commit domains. [RFC 5536 §3.1.3](https://www.rfc-editor.org/rfc/rfc5536.html#section-3.1.3).

Conversely, a private application may deliberately use names local to a world. That does not require putting every mutation in that world into one atomic domain.

My recommendation is:

```text
Binding key:       (identity namespace, exact external name)

Acceptance origin: (lineage, commit domain, incarnation, position)

Content identity:  (subject/profile, hash algorithm, digest)

Occurrence:        its own stable event identity
```

The exact representation can use references and inherited context. These are logical distinctions, not a demand to repeat every field in every physical record.

For the initial NNTP port, use an explicit Netnews namespace and preserve the exact Message-ID. Native applications can use explicitly scoped namespaces. Federation declares whether it preserves that namespace or translates into another one; translation must preserve provenance and declare its loss. Automatically prefixing every imported name with the receiving commit domain would defeat duplicate detection and make routing change identity.

Likewise, **replication is not universally Binding union**. Union is appropriate for evidence and other declared join structures. Replicating the state of an ordered transactional domain must also preserve its accepted history, obligations, decisions, and writer authority. Two disconnected writers cannot independently mutate arbitrary balances or claims and then call the union a replica of one ordered world. UC already reserves these non-merge choices for Decide. [UNIVERSAL-CONSTRUCTIONS.md:221](/Users/ember/dev/fn/build/coordinator/fn2/UNIVERSAL-CONSTRUCTIONS.md:221).

Transport makes the distinction operational. Moving a world should preserve its identity namespace and historical acceptance receipts while changing its executing location and incarnation. An old incarnation’s late writes can be retained as observations without being accepted as current authoritative decisions—the WIDEST design expressly calls for that. [WIDEST-ROLE.md:31](/Users/ember/dev/fn/build/coordinator/fn2/WIDEST-ROLE.md:31).

Forking needs a separate rule. Shared prefix identities remain the same historical objects. New branch-local occurrences are new occurrences. External effects and inherited obligations need a disposition; duplicating the Binding does not duplicate the right to discharge or spend a promise.

So I agree that the event context must bind a domain now. I disagree that R5 should establish commit-domain-scoped identity. **Settle the distinction now, then encode it.**

**The largest unnamed thorn: which bytes are being identified?**

I would call this **T0**, because every other recommendation depends on it.

Main starts with “content identity is BLAKE3 of the bytes.” Which bytes?

- Poster-supplied source?
- Injected stored article?
- Native signed source?
- Immutable envelope plus ciphertext?
- Ciphertext alone?
- A legacy relay projection?
- The event occurrence that carries any of these?

D25 makes poster bytes the duplicate/conflict subject. The existing implementation recovers source through a specified injection inverse and falls back to exact octets where that inverse cannot safely recover it. It does not permit arbitrary normalization of a relayed article. [decisions.md:1105](/Users/ember/dev/fn/planning/decisions.md:1105), [nntp.md:748](/Users/ember/dev/fn/specs/nntp.md:748).

The spec also has a versioned `relay-v1` subject for Path/Xref variants, but explicitly says that it does not yet change duplicate/conflict binding semantics. [peering.md:3240](/Users/ember/dev/fn/specs/peering.md:3240).

That matters enormously to T2. If every fully received routed variant is now recorded as a conflict, hashing the stored transit bytes can convert ordinary propagation into permanent conflict accumulation. A feature meant to expose attacks can fill its own four slots with benign route variants.

I would require a named identity-subject profile with a precise extraction and validation rule. Preserve separate names for the stored wire object and the authored object where they differ. Never infer that arbitrary removed fields were unauthored merely because familiar header names occur.

For signed material, the rule must also say whether additional signatures are evidence about the same object or part of a new signed object. For sealed streams, re-encrypting identical plaintext normally produces a different ciphertext identity; plaintext equality is unavailable to the node and must not be guessed. If the application wants those ciphertexts treated as revisions of one logical message, that relationship needs an authenticated statement.

This ruling is required before migration because `fn2-txn-offer` consumes the upload’s digest as the content identity. A vague subject here becomes durable identity metadata immediately. [txn.lisp:352](/Users/ember/dev/fn/fn2/books/txn.lisp:352).

**Other thorns main did not name explicitly.**

**Validation dependencies and policy disagreement.** A node can have an authentic signed assertion without the dependencies needed to authorize it. Another node can have those dependencies and still decline it under local policy. Separate received, structurally valid, cryptographically verified, authority-qualified, locally admitted, and currently selected facts. A raw union does not make these judgments equal. The common convergence theorem must name the namespace, fact interpretation, and dependency closure.

**Evidence arrival after duplicate content.** A duplicate article body may arrive with a new signature, acceptance receipt, cancellation authorization, or previously missing chain evidence. Early duplicate suppression must not discard those independent additions. Conversely, merely wrapping the same evidence in another carrier must not generate another permanent fact or another charge.

**Operation identity versus object identity.** A retry, a rehydration, a second observation of identical sensor bytes, and a newly authorized obligation are different operations. Content equality cannot decide which happened. WIDEST already distinguishes occurrence identity, while the storage decision requires stable operation outcomes and guards against contradictory operation-ID reuse. [WIDEST-ROLE.md:21](/Users/ember/dev/fn/build/coordinator/fn2/WIDEST-ROLE.md:21), [STORAGE-DESIGN.md:31](/Users/ember/dev/fn/build/coordinator/fn2/STORAGE-DESIGN.md:31).

**Cross-posting and the owner of uniqueness.** If identity is shared across several commit domains, which domain owns the local acceptance decision? Can one article atomically gain membership in groups owned by different domains? Existing NNTP promises atomic local cross-posting; storage says one atomic mutation belongs to one domain. That needs an explicit initial placement rule or an explicit multi-domain protocol, not an implicit global identity write hidden inside every transaction. [nntp.md:702](/Users/ember/dev/fn/specs/nntp.md:702), [STORAGE-DESIGN.md:31](/Users/ember/dev/fn/build/coordinator/fn2/STORAGE-DESIGN.md:31).

**Completeness, suppression, and selective disclosure.** An authentic Merkle root proves a commitment to some history. It does not prove that a peer disclosed every competing binding, every revocation, or every authorized article. Evidence may be intentionally scoped to a reader. We need coverage and disclosure semantics before calling a peer “caught up.”

**Semantic effects of imports.** Importing “A accepted this” must not grant the importer’s local article numbers, debit its accounts, execute control, or adopt A’s custody obligations. Importing a receipt is learning about a decision; adopting an obligation is another decision. This is the practical consequence of the widest-role model, not merely a tidy taxonomy.

**What the papers support—and what they leave us to design.**

Mimram and Di Giusto support the valuable move from “a conflict prevents composition” to “a conflict is representable state that later composition can operate on.” Their construction is a conservative finite cocompletion; the concrete model retains labeled elements and relations, with partial maps when deletions are included. It is not a theorem that fn2’s particular four-entry map is closed under merge, nor that a conflict representation selects the authoritative result. [mimram-digiusto2013-categorical-theory-of-patches.txt:312](/Users/ember/paperbin/mimram-digiusto2013-categorical-theory-of-patches.txt:312), [same paper:935](/Users/ember/paperbin/mimram-digiusto2013-categorical-theory-of-patches.txt:935).

The useful design lesson is to retain enough structure to distinguish **incompatible assertions about the same subject** from **compatible assertions about different local decisions**. “A accepted a” and “B accepted b” should compose without losing their subjects. The unresolved question is then explicit: what selection or authority statement, if any, relates them?

Sanjuán et al. support content-addressed causal histories and head-set synchronization. But their system model assumes a DAG-Syncer that can fetch the referenced nodes; recovery depends on another replica retaining the needed state. Their payloads must themselves be convergent. The DAG does not make an arbitrary transaction or first-arrival register convergent. [sanjuan2020-merkle-crdts.txt:455](/Users/ember/paperbin/sanjuan2020-merkle-crdts.txt:455), [same paper:696](/Users/ember/paperbin/sanjuan2020-merkle-crdts.txt:696).

Their limitations are particularly relevant here: causal history grows, thin histories can require slow sequential retrieval, and compaction/garbage collection is left as future work with additional assumptions. [same paper:826](/Users/ember/paperbin/sanjuan2020-merkle-crdts.txt:826), [same paper:955](/Users/ember/paperbin/sanjuan2020-merkle-crdts.txt:955).

For fn2 that implies three concrete design obligations:

- A known head with missing dependencies is pending knowledge, not a completed cut.
- BP transfer should support useful self-contained segments and dependency bundles; one round trip per predecessor is a poor disconnected protocol.
- Erasure and compaction need a summary/bootstrap contract that preserves promised identity and authorization observations without pretending the old DAG remains fetchable.

I also would not take the paper’s optional suggestion of authenticating broadcasts instead of retaining payload signatures as our default. Evidence must remain verifiable after an intermediary stores it, the original connection disappears, and the origin is offline. [same paper:930](/Users/ember/paperbin/sanjuan2020-merkle-crdts.txt:930).

UC §4.4’s vector/head-set analogy remains useful, but its interpretation assumes a common underlying causal history. A per-domain height is insufficient to distinguish two forks at the same height. Origin, incarnation, and a commitment to the relevant prefix must participate in cross-peer comparison.

**What must be ruled before `fn2-txn` migrates.**

The machine-form document explicitly makes this identity discussion a prerequisite. It also describes migration as preserving machine behavior. Those goals need reconciling: the missing evidence commit is an intentional semantic correction, not something to preserve because an old scenario expects a refusal with no write. [MACHINE-FORM-20261030.md:38](/Users/ember/dev/fn/build/coordinator/fn2/MACHINE-FORM-20261030.md:38), [MACHINE-FORM-20261030.md:41](/Users/ember/dev/fn/build/coordinator/fn2/MACHINE-FORM-20261030.md:41).

I would make these rulings now:

| Ruling | My recommendation | Why it affects the transaction machine |
|---|---|---|
| Identity subject | Name the exact authored/stored/sealed subject and its profile; keep distinct identities where needed. | Determines what the lookup and durable binding mean. |
| Namespace versus commit origin | Separate them; use an explicit Netnews namespace for the initial port. | Determines keys, claims, receipts, and cross-domain ownership. |
| Portable facts versus local decisions | Preserve attributed evidence and immutable local acceptance receipts separately from serving selection. | Determines record shape and whether peer facts can be imported safely. |
| New conflict transition | A new admissible conflict takes a reserved evidence commit path; known evidence remains idempotent. | Changes phases, holds, effects, and completion handling. |
| Outcome semantics | Separate article refusal from evidence-recording success/uncertainty. | Prevents false durable claims and incorrect retry/cleanup behavior. |
| Resource contract | No universal four-entry union claim; use funded admission and explicit incomplete coverage. | Determines reservations, bound handling, and lookup design. |
| Authority boundary | A valid signature alone cannot seize a name; carriage is not verification or authorization. | Determines what may affect acceptance and selection. |
| Retained observations | Preserve exact accepted identity, conflict knowledge, evidence dependencies, and retry meaning through reclamation. | Determines durable fields and compaction obligations. |
| Initial atomicity placement | State which domain owns local NNTP identity and cross-post membership. | Prevents an undeclared multi-domain transaction. |

The new form should be able to express an **evidence-only committed transaction with an article-refusal reply**. It should also express pending dependencies and named resource refusal without collapsing either into invalid content. Those are the important capabilities; the exact phase names are an implementation choice.

I would not require the full E4 protocol, generalized resolution machinery, or HDR presentation before migrating. Nor would I freeze every future authority scheme. The initial machine can support a deliberately narrow profile, provided its records preserve the distinctions and its unsupported cases are explicit.

**What can wait for E4—and what E4 must prove.**

E4 can choose the inventory protocol, head exchange, segmentation, dependency packing, anti-entropy scheduling, BP contact policy, and exact wire encodings. It can implement evidence propagation independently of article availability. The detailed fork/federation/transport protocols can follow their own milestones, with namespace and origin distinctions already represented.

Before E4 claims peer identity convergence, I would require these concrete witnesses:

1. Opposite first arrivals produce equal portable evidence after exchange while preserving different, correctly attributed local acceptance receipts.
2. Two individually full candidate sets meet; the result is a valid merge or an explicit incomplete/refused state, never silent truncation or a false caught-up claim.
3. Identical content arrives with new evidence; the evidence is learned without a new article allocation or duplicate permanent charge.
4. A forged arbitrary-key signature cannot replace an unsigned article merely by verifying.
5. A carried object arrives before its authority dependencies; later verification does not rewrite its historical receipt.
6. A cancel precedes its target, including a crash between them; it acts only under the receiver’s applicable authority rule.
7. A body is reclaimed while identity and required evidence survive; a reoffer does not resurrect publication, and a duplicate response does not discharge an unrelated custody obligation.
8. Evidence commit crashes before persistence, after persistence, and before reply; recovery preserves the correct outcome and accounting.
9. The same authored article arrives through different routing projections; the declared identity profile distinguishes route variation from authored conflict.
10. A transported domain rejects old-incarnation decisions while retaining attributable late observations and preserving its namespace.

I would restate the principal peer claim as:

> Within a named identity namespace and fact interpretation, replicas that have durably incorporated the same eligible evidence and its required dependencies have equal evidence Bindings and equal conflict predicates. Local acceptance receipts remain attributed historical facts. Serving choices agree only when the relevant policy and decision inputs also agree. Eventual incorporation is a separate claim with explicit connectivity, availability, authorization, and resource assumptions.

That gives us a useful destination. The immediate work is to make the transaction machine record the right facts, under the right names, with the right durability and resource consequences. E4 can then transport those facts instead of discovering that “identity” encoded a local decision it cannot safely merge.