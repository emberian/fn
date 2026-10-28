**Keep decision 4; reject the chapter’s amendment as written.** Its useful proposals need sharper contracts. Several claimed guarantees do not follow from the cited mechanisms.

1. **Fatal — tradeoff 1 is useful, but the verdict makes the checkpoint self-referential.**

   The verdict logs a claim containing the event root *before computing that root*. Its descriptor commitment can introduce another cycle through the checkpoint batch seal. My format §E explicitly avoids this.

   Log a statement about an **already determined predecessor cut**: `(k, root_k, fold-id, summary, identity, descriptor_k, …)`. Append it at `k+1`; authenticate it through an inclusion proof under the enclosing checkpoint. Define its effect on folds and event numbering. `eijdenberg2015-verifiable-data-structures.txt` logs map heads in a **separate log**; it does not justify this circular construction.

   Also, my ruling never prescribed extension lines. “Wrong in form as stated” attacks an invented encoding. Avoiding extensions is a sound interoperability choice, not a refutation of typed claims. ([`c2sp2026-docs-tlog-checkpoint.md`](https://c2sp.org/tlog-checkpoint@v1.1.0))

2. **Fatal — tradeoff 2 omits the condition that makes a quorum safe.**

   A quorum *policy* alone proves nothing about agreement. `sigsum2026-docs-policy.md` permits `any` and even `none`. Two disjoint sets of honest witnesses can cosign incompatible branches.

   Require **honest intersection between every pair of accepted quorums**, including across policy changes. For uniform `q`-of-`N` with at most `f` Byzantine witnesses, `2q > N+f` suffices. Witness persistence must itself resist the rollback covered by the threat model.

   Keeping local commits independent of cosigning is reasonable, but then their acknowledgements lack quorum protection until covered. CAP does not turn prefix consistency into linearizable, fresh reads. `gilbert2002-brewers-conjecture-cap.txt` concerns an available atomic read/write object; identify the corresponding fn2 operation before invoking its theorem.

3. **Material — tradeoff 3 identifies real work but supplies no executable rotation protocol.**

   A signed-note key ID is a **32-bit lookup identifier**, explicitly not a cryptographic commitment. Security comes from configured public keys and algorithms. (`c2sp2026-docs-signed-note.md`.)

   Standard witnesses check configured log keys and Merkle consistency; they do not interpret fn2’s logged key epoch. Logging “new key authorized” therefore does not update witness trust automatically. Specify activation, overlapping keys, revocation and policy distribution.

   After compromise, witnesses cannot simply recosign the operator’s preferred branch if it conflicts with their previous signatures. That violates their consistency obligation. Recovery authority and append-only evidence are different things.

4. **Fatal — tradeoff 4 cannot authorize an inconsistent continuation under the same origin.**

   An incarnation-change leaf cannot make an incompatible tree consistent. Standard C2SP witnesses must refuse it regardless of the operator’s explanation. A new origin can establish a new log, but acceptance of its relationship to the old history requires an explicit lineage policy.

   Restore-and-replay to the established frontier need not create a new incarnation. Irrecoverable loss requires a declared discontinuity preserving old receipts, identities and obligations—not laundering them through a higher counter.

   `ctpolicy2017-venafi-inconsistent-sths.txt` supports preventing premature signing after restore. Venafi reported no lost certificate data and restored the correct state; the violation was nevertheless an inconsistent published view. It does not support “every backup restore starts a new history.”

5. **Material — tradeoff 5 confuses publication cadence with receipt availability.**

   An event committed after the latest cadence checkpoint cannot have an inclusion proof under that checkpoint. Either wait for a covering checkpoint, return a local durable acknowledgement with proof pending, or define another receipt contract.

   Keeping per-request timestamps out of the body is sensible. But a timestamp chosen **once for a shared checkpoint** does not prevent signature merging; C2SP cosignatures already carry their own signed timestamps. Reuse published checkpoint/signature artifacts to reduce marking.

   `rfc9162-certificate-transparency-v2.txt` also requires freshness, including fresh timestamps during inactivity. Cadence needs both a publication rule and an explicit coverage-delay contract. Aviator’s lesson is backlog control, not merely choosing a timer (`ctpolicy2016-google-aviator-incident.txt`).

6. **Fatal to the erasure claim — tradeoff 6’s salt must remain secret.**

   EDPB ¶52 requires the salt and original data to remain confidential off-chain; its unlinkability conclusion assumes neither leaked. An ordinary public opening of `H(salt || record)` reveals the salt. Deleting fn2’s copy cannot erase recipients’ openings, backups or cached proofs. Moreover, semantic records can outlive their payloads.

   Sealed content does not solve this for a leaf that also commits to the public Message-ID, signer and envelope. Destroying a content key leaves those associations.

   A confidential opening store is a possible **restricted proof contract**, not cheap universal erasure. The guidelines also require considering other identifying information; permanent exact identities remain part of that analysis. Finck presents conditional alternatives, not blanket approval. ([`edpb2026-guidelines-022025-blockchain-v2.txt`](https://www.edpb.europa.eu/system/files/2026-07/edpb_guidelines_202502_blockchain_v2_en.pdf), ¶¶51–54, 103–104; `finck2019-blockchain-gdpr-european-parliament.txt`, §7.3.2.)

7. **Material — tradeoff 7 duplicates witnessing and overstates the evidence.**

   Two signed roots of different sizes are not, by themselves, a publicly checkable proof of equivocation. Failure to obtain a consistency proof is not proof that none exists. Same-size different roots, or conflicting authenticated openings at the same position, provide concrete evidence.

   Cox’s “keep up the lie” depends on clients retaining heads and checking every accepted extension; signatures alone do not enforce that discipline. (`cox2019-transparent-logs-skeptical-clients.txt`.)

   Mutual witnessing is useful but optional infrastructure. A peer checking consistency does not thereby attest that it stores the articles or accepts custody obligations. Those require separate statements.

8. **Material — tradeoff 8’s permanent-leaf rule is a policy, not a lower bound.**

   Dropping a subtree’s leaves while retaining its root preserves proofs for leaves outside that subtree. It sacrifices openings *inside* it. Retaining every leaf is one implementation of perpetual arbitrary proof service; it is not necessary for all useful inclusion and consistency contracts.

   State which events and historical cuts remain provable, who retains openings, and which subtree hashes support them. Cox’s “permanent hashes” means completed-subtree hashes never change—not that every installation must retain every hash forever. The chapter conflates structural permanence with retention obligations.

9. **Material — §4.1 and the proposed experiment regress the adopted recovery rules.**

   My format uses **two anchor banks**, not quorum voting. A newer singleton matters. An older anchor plus a valid journal suffix may recover beyond the witness head; “anchors behind witness ⇒ damaged” is therefore wrong.

   Compare independent evidence with the **reconstructed compatible frontier**, as §I.8 already requires. No witness ahead does not establish `intact`; corruption and ambiguous terminal writes remain possible. Nor does normal open verify every reachable page: cold pages are checked on access or scrub.

   Finally, witnesses of event roots do not automatically cover maintenance-only commits. The physical commit identity and descriptor binding must carry that evidence. This is precisely why corrections 2 and 3 retained separate integrity subjects.

10. **Material — “a signed root does not prove a query answer” needs a narrower conclusion.**

    Correct: a signature authenticates a commitment; inclusion and consistency require additional proofs. A map proof authenticates an answer **relative to that map root**. It does not establish correct folding, authorization, freshness or correspondence to the event history.

    `eijdenberg2015-verifiable-data-structures.txt` explicitly assigns correct map evolution to full audit. Logging a dishonest map head makes the dishonesty auditable, not correct.

    Consequently, membership/non-membership interfaces for every summary are not implied by decision 4. Choose interfaces from promised queries. For exact identity, a SHA-256-keyed sparse map also needs exact-key collision handling; hashing cannot replace fn2’s identity comparison.

11. **Material — the theoretical optimum has a wrong formula and mixed cost models.**

    Tamassia’s bound is **`Ω(log(n/k))`**, not `Ω((log n)/k)`, in its hash-DAG authenticated-dictionary model. It is not a universal bound on every commitment scheme or specifically on log consistency proofs. (`tamassia2005-computational-bounds-hierarchical-data-processing.txt`, Theorems 3 and 6.)

    “Twenty hashes at one million events” is a useful binary inclusion estimate, not a bound covering every cited proof encoding. Cox’s permanent-node-only representation permits larger proofs.

    An MMR storage layout need not force an incompatible root: tree hashing and peak aggregation determine compatibility. Its completed forest has `n − popcount(n)` interior nodes; `n−1` describes a completed single tree including peak combination. The OpenTimestamps note’s illustrated append order is postorder despite its “breadth first” wording. (`opentimestamps2026-docs-merkle-mountain-range.md`.)

12. **Material — Memoir and ROTE do not establish “scalable rollback protection must be distributed.”**

    Memoir’s central contribution is **avoiding monotonic counters**, using deterministic replay and only two NVRAM writes per boot. Calling its proof “one monotonic-counter protocol” reverses the paper. (`parno2011-memoir-state-continuity.txt`.)

    ROTE’s `f+1` construction relies on enclaves and a particular adversary model; its guarantee permits resetting the whole protection group. Its 1–2 ms measurements do not price a generic durable witness service. (`matetic2017-rote-rollback-protection.txt`.)

    Neither paper’s theorem count predicts fn2’s incarnation-proof cost.

13. **Material — §4.5 supplies proof vocabulary, not the claimed top-level theorem.**

    Grove’s lower bound denotes an actual abstract-list prefix. A signed `(size, root)` becomes evidence for it only after proving the cryptographic interpretation, witness transition and durable-state invariant. Assigning incompatible witness observations one global append-only resource would assume the agreement being proved. Incarnation changes are not automatically Grove epoch transitions. (`sharma2023-grove-separation-logic-distributed-systems.txt`.)

    Durable linearizability is appropriate for witness check/persist/reply. Calling fn2’s checkpoint “buffered durable” is misleading: acknowledged commits remain durable through checkpoint **plus journal**; checkpoint lag does not license losing completed operations. (`izraelevitz2016-durable-linearizability.txt`.)

    Fork consistency concerns completed client operations and their legal views, not just comparable log roots. SUNDR supplies a client protocol; fn2 still needs response-to-history binding. Cachin’s Theorem 1 rules out even obstruction freedom under its Byzantine-register emulation requirements; Theorem 4 likewise has that model and liveness context. Neither establishes an unconditional ceiling for any signed-root system. (`mazieres2002-secure-filesystems-byzantine-storage.txt`; `li2004-sundr-secure-untrusted-data-repository.txt`; `cachin2007-fork-linearizable-untrusted-memory.txt`.)

14. **Material — the deployment evidence needs its actual qualifications.**

    CT v2 extensions are authenticated but semantically ignorable; that differs from ML-DSA-44 checkpoint cosignatures not covering extensions. Chrome describes incident removal as discretionary and inconsistent heads as typically removal-worthy, not an exceptionless “fatal” rule. An expired gossip draft establishes no standardization outcome beyond its status, and Sigsum’s 2023 deployment observation needs its date. (`rfc9162-certificate-transparency-v2.txt`; `chromect2026-docs-log-policy.md`; `nordberg2018-draft-ietf-trans-gossip-05.txt`; `moller2023-sigsum-design-cats.txt`.)

    The io_uring reports principally demonstrate **application completion-accounting errors**. Mooncake overwrote byte counts and misattributed stale CQEs; NIXL ignored short completions; liburing documented submission-boundary semantics. Check request identity, exact completed length and outstanding borrows before fencing or reusing memory. A short completion is not full success, but can sometimes be continued safely. These reports do not themselves prove kernel corruption or mandate epoll. (`mooncake2026-issue-3066-io-uring-silent-corruption-5-15.txt`; `nixl2026-issue-1696-io-uring-enospc-short-writes.txt`; `liburing2022-issue-510-io-link-out-of-order.txt`.)

**My amended wording**

> **Integrity:** retain parent-held physical hashes binding allocation context, explicit predecessor commit/seal links including maintenance batches, and a domain-separated append-only Merkle event log with pageable frontier and proof material.
>
> Authenticate a versioned typed checkpoint statement binding history/incarnation, an explicit event cut and root, fold/schema identity, summary and exact-identity commitments, an acyclic checkpoint descriptor, and authorized signing keys. For standard transparency interoperability, log that statement about an already determined predecessor cut and supply its inclusion proof under the enclosing three-line checkpoint. Neither the statement nor its descriptor includes the enclosing root or seal recursively. Checkpoint inclusion does not establish correct folding, query completeness, availability or freshness.
>
> Distinguish local durability, signed coverage and policy-accepted witnessed coverage. Publish shared checkpoints at a declared cadence; only covering checkpoints support inclusion receipts. Witnesses atomically verify extension and persist their frontier before replying. The acceptance policy states its fault assumptions, honest-quorum-intersection requirement and transition rules.
>
> Recovery reconstructs candidates through anchors and journal before comparing independent frontier evidence; contradictory evidence prevents normal rollback. Witness coverage remains an explicit lower bound. Compatible restoration preserves lineage; an irrecoverable discontinuity requires separately authorized lineage establishment and never cancels prior promises.
>
> Retain integrity material according to explicit recovery and proof-service obligations. Any confidential-opening scheme states its disclosure and erasure limits; deleting a salt or key does not erase previously disclosed associations or independently retained identity metadata.

**Four additions**

- **Interoperability profile:** fix the Merkle algorithm, signature acceptance rule and encoding versions. C2SP’s ML-DSA-44 is not D09’s ML-DSA-65 hybrid; its fixed-width cosignature fields and witness proof limits also need an explicit bridge to fn2’s extensible counters.
- **Witness recovery protocol:** define bootstrap trust, retrieval freshness and policy updates. C2SP’s monitoring endpoint can lag; fetching “the last cosigned head” is not automatically an authoritative latest-frontier read.
- **Adversarial tests:** include disjoint quorums, witness rollback, persist-before-lost-response, stale monitoring replies, older anchors with sufficient replay, and a witnessed semantic head with lost maintenance state. The oracle checks promises and evidence, not merely relative counters.
- **Portable source integrity:** restore correction 10’s separate BLAKE3 range-verification contract—length, chunk position, final-block and root-output handling. Event inclusion, physical page verification and portable content verification remain distinct proofs.