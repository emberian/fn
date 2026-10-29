Keep the storage decision. The chapter’s expanded amendment overclaims its security proof and turns several application choices into storage requirements.

1. **Material — MLS and Signal support a narrower conclusion; tradeoff 1 is real but over-resolved.**

   The `PrivateMessage` layout is correctly read: sender data and signature are encrypted. That does **not** mean the delivery service cannot identify the sender through authenticated transport, IP address, fanout or other metadata. RFC 9750 explicitly discusses these channels. Signal’s sealed-sender article likewise acknowledges timing/IP correlation; its delivery token authorizes delivery **to a recipient**, not accountable per-sender quotas. Signal’s private-group system hides member identities while exposing encrypted entries and their access/update patterns. (`rfc9420-mls-protocol.txt` §6.3; `rfc9750-mls-architecture.txt` §8.4; `signal2018-blog-sealed-sender.txt`; `chase2020-signal-private-group-system.txt` introduction.)

   Keep public signers for fn’s portable attribution contract, not because accounting inherently requires them. Distinguish transport principal, quota principal and content signer; per-stream signing keys can reduce linkage without anonymous credentials. A hidden-signer profile changes authorization, signer chains and public evidence—not merely an envelope field. Naming it as possible is reasonable; committing to a later variant is premature. Its implementation also need not introduce new cryptographic *primitives*, much less automatically incur an “EverCrypt/HACL*-sized” obligation.

2. **Minor — Matrix is accurately described, but the comparison is overstated.**

   The cleartext `m.relates_to` requirement is real; the specification even tells clients to prefer it over an encrypted copy. But Matrix does not categorically expose “more than fn2 plans”: fn2 already exposes signer, stream, order/time and optionally relations. The difference is compulsory versus application-selected fields. Also distinguish the public event wrapper from the cryptographically authenticated client content; `unsigned` is not authenticated merely because it appears in the envelope. (`matrix2026-docs-client-server-api.md`, “Forming relationships”; `matrix2026-docs-m-room-encrypted-schema.yaml`; `matrix2026-docs-room-event-schema.yaml`.)

3. **Minor — Tahoe supports verification without reading, not “free” verification or unconditional confirmation attacks.**

   Tahoe offers random-key encryption as well as convergence, and its convergence derivation includes a secret specifically to mitigate guessing attacks. State the attacker’s knowledge before claiming confirmation-of-file exposure. A verify-cap authenticates the object or version covered by its commitment; mutable verification alone does not establish freshness. Repair additionally needs surviving bytes/shares and authority to store replacements. The useful conclusion is **no decryption-specific verification machinery**, not “free” or “erasure-safe.” (`tahoelafs2026-docs-file-encoding.rst`; `tahoelafs2026-docs-uri.rst`; `tahoelafs2026-docs-architecture.rst`.)

4. **Material — A leakage function is a specification, not a demonstrated Pareto frontier.**

   `L(trace)` should describe allowed disclosure; the real adversarial view must be **simulatable from** it. Equating the view with a list of metadata skips the security claim. Specify observers, auxiliary information, corruption and adaptive interactions. Distinguish authored timestamps, observed arrival times and commit order.

   No nondominance argument establishes “the Matrix point” as Pareto-optimal. Nor does the cited ORAM bound prove that every private search must pay logarithmic overhead: Goldreich–Ostrovsky’s bound assumes a restricted balls-and-bins model; later bounds cover specified online models. Full local replication, scans, PIR and server computation trade different resources. Cite the applicable model rather than “passive ORAM.” ([Boyle–Naor’s examination of the bound](https://www.wisdom.weizmann.ac.il/~naor/PAPERS/oram_lower.html); `curtmola2006-searchable-symmetric-encryption.txt` §3.)

5. **Material — Tradeoff 2 identifies a real binding requirement but gives an incorrect universal repair.**

   Re-signing ciphertext proves that a new signer endorsed those bytes; it is an authorship attack only if recipients interpret that as authorship of the enclosed plaintext. Define the signature’s meaning.

   For encrypt-then-sign, binding the immutable context into AEAD and signing context plus ciphertext is sensible. For sign-then-encrypt, **AAD alone does not prevent a recipient re-encrypting the original signed plaintext under fresh AAD**: the inner signature must bind the intended context too. MLS already signs contextual information, including `authenticated_data`. The chapter’s “re-encrypted plaintext fails signature verification” does not follow from its generic recipe. ([Davis, *Defective Sign & Encrypt*](https://www.usenix.org/event/usenix01/full_papers/davis/davis.pdf); `rfc9420-mls-protocol.txt` §§6.1–6.3.)

   Define a canonical, immutable, pre-encryption context. Exclude later-assigned commit metadata and avoid circular dependencies on ciphertext-derived identifiers. Recipients must check context agreement; the node can verify the outer signature but **cannot verify that the encryption actually used the prescribed AAD**.

6. **Material — “Two memberships” is useful shorthand, but tradeoff 3 omits essential distinctions.**

   Separate append authorization, ciphertext-fetch authorization, current cryptographic membership and possession of historical keys/plaintexts. Removing a member cannot revoke previously learned material. The node can coordinate admission changes with public epoch commitments without holding keys; “nothing the node does can close the gap” is too strong.

   Nor do all key-management messages simply travel as ordinary sealed events: MLS newcomers need KeyPackages, Welcome delivery and authenticated bootstrap information. A total-order journal supports RFC 9750’s ordering-server design only with the client rule **apply the first valid Commit for an epoch, including your own only after ordered delivery**. Acknowledged storage is not an accepted MLS transition. (`rfc9750-mls-architecture.txt` §§2, 5.2.1; `rfc9420-mls-protocol.txt`.)

7. **Material — Tradeoff 4 chooses a reasonable baseline using incorrect leakage and cost claims.**

   Public plaintext keywords are direct disclosure, not automatically an L2–L3 SSE construction. Cash’s levels describe particular occurrence-pattern disclosures; sorted pseudorandom tags differ from unsorted tags and literal public words. The 1.6× padding result and 35% recovery result are experimental results for specified attacks and datasets, not universal constants. Islam’s “minimal background knowledge” includes a keyword co-occurrence model; do not omit that assumption. (`cash2015-leakage-abuse-searchable-encryption.txt` §§2, 4–5; `islam2012-access-pattern-disclosure-searchable-encryption.txt` §6.)

   Encrypting a client index does **not** reduce disclosure to sizes and timing: selective index-block and result-object fetches expose access patterns. Full synchronization followed by local search can avoid query-dependent requests, at a measurable replication cost. “3–7k rows/day is cheap” ignores history, object sizes, client count and catch-up.

   Keep **no server search over sealed plaintext**. Preserve searches over deliberately public fields, already allowed in §5.1. “No server-side search” contradicts that contract.

8. **Material — Tradeoff 5 promises more than bucket padding provides.**

   Power-of-two rounding costs less than twice the unpadded encoded length, subject to the minimum bucket and framing overhead. It still reveals a size bucket; it does not hide size outright. A true-length public field would defeat it. Nearly doubling a 1 KiB row is not intrinsically negligible.

   The store necessarily observes its own commit order and timing. It need not thereby learn plaintext creation times or distinguish genuine messages from cover traffic. Fixed-rate transmission, dummy messages and padding across messages are alternatives to mixing/batching. State those exclusions as scope choices, not impossibility results. (`rfc9420-mls-protocol.txt` §15.1.)

9. **Material — Tradeoff 6 reaches the right envelope conclusion through false capability claims.**

   Miller’s sealer/unsealer analogy concerns encapsulation within an enforced object-capability environment; it is not encryption against that environment’s operator. Caretakers explain revocable mediated access, not the whole confinement result. (`miller2006-robust-composition-thesis.txt` §24.1; `miller2003-capability-myths-demolished.txt`.)

   seL4 badges label invoked capabilities, not inherently principals; delegated copies retain the badge. The manual specifies **28 usable bits on 32-bit platforms and 64 on 64-bit platforms**. Kernel rights concern kernel objects: stream-level read/append attenuation still requires a service protocol and its enforcement. (`sel4-2026-reference-manual.txt` §§3.1.2, 4.2.1.)

   Absence of a key-store capability does not prove absence of keys received through IPC, shared memory, initialization or collusion. Confinement needs a configured-system argument. “Robigalia proves it; Linux only promises it” is unsupported. Keep the envelope unchanged, but do not manufacture a platform guarantee.

10. **Material — Tradeoff 7 confuses risk management, erasure and cryptographic layers.**

    “Per-object erasure is inherent” is false: group/session keys, backups, retained derivation secrets and recipients’ plaintext copies may survive. Independently erasable objects require an appropriate key hierarchy and deletion assumptions.

    The EDPB does not endorse key destruction as blanket erasure. Paragraph 51 retains the personal-data classification and warns about compromise and obsolescence; paragraphs 63 and 103 require effective deletion/anonymization, and paragraph 104 advises against putting such personal data on-chain. Finck explicitly describes unresolved questions. ([`edpb2026-guidelines-022025-blockchain-v2`](https://www.edpb.europa.eu/system/files/2026-07/edpb_guidelines_202502_blockchain_v2_en.pdf); `finck2019-blockchain-gdpr-european-parliament.txt` §7.3.2.)

    A separate sealed-stream retention setting is reasonable, but **shorter than plaintext** is not entailed. Re-encryption cannot rescue old ciphertext already copied by an adversary. ML-KEM establishes keys; it is not a content cipher. Specify symmetric AEAD, key establishment and signatures separately, with confidentiality horizons and agility. Neither encryption nor seL4 proves the operator “cannot be made to” decrypt. Withdrawal, admission, quotas and metadata policy remain content-related policy mechanisms.

11. **Material — Tradeoff 8 should describe observer-specific leakage, not identical views.**

    Relays carrying the canonical object see its envelope. They do not necessarily see originating-client identity, every fetch, local acknowledgements or every node’s timing. The union is a **colluding-observer** model, not an automatic property of a peer group. The verdict’s “every peer and carrier sees the same” wrongly extends envelope visibility to the whole leakage profile.

12. **Fatal — Absence of a key is not the proposed confidentiality proof.**

    A node with no key can receive deterministic encryption, reused-nonce ciphertext, plaintext disguised as ciphertext, or auxiliary information that reveals the message. Absence of keys establishes an architectural boundary; confidentiality requires cryptographic assumptions, honest-client conditions and a specified adversary.

    Also, storing opaque client-supplied bytes need not change the node’s equality refinement or identity simulator. The **composed client–node confidentiality functionality** introduces indistinguishability. Keep those proof subjects separate. Application cryptography may lie outside the node implementation’s TCB while remaining indispensable to the end-to-end theorem. (`CLIENTS-AND-DATA-MODELS.md` §3.3; `curtmola2006-searchable-symmetric-encryption.txt` §3.)

13. **Material — Crash noninterference is not integrity renamed; “nothing new in the folds” needs conditions.**

    Returning exactly the wrong principal’s authentic object preserves byte integrity and violates confidentiality. Authorization, metadata responses, stale caches, recovery and observable failure behavior all matter. SFSCQ explicitly uses relational reasoning across executions; it does not reduce confidentiality to preventing stale-block substitution. (`ileri2018-sfscq-proving-confidentiality-file-system.txt` §§3–4.)

    Existing fold machinery can remain unchanged **if** it consumes only canonical public metadata and treats ciphertext opaquely. But extraction, indexing, control-message authorization and any new epoch/retention semantics require preservation obligations. Reusing folds does not discharge them.

I would replace the proposed verdict with:

> **Sealed streams:** retain client-encrypted opaque content with an explicit public envelope. The node authenticates the immutable envelope and ciphertext under the ordinary signed-record contract; it holds no application decryption keys and indexes only deliberately public fields. The supported client profile must cryptographically bind the immutable application context to the ciphertext and require recipients to verify that binding; the node’s signature check does not establish correct encryption.
>
> Declare leakage separately for nodes, relays and their possible collusion, including envelope fields, lengths and observable traffic. Distinguish append and fetch authorization from cryptographic membership and historical key possession. Public signers remain the initial profile; hidden-signer designs require a separate authorization and evidence contract.
>
> Key establishment, membership, rotation, padding and encrypted client indexes belong to the application protocol. Storage order can support an MLS delivery service with an explicit client integration protocol. Retention follows declared requirements and confidentiality horizons; encryption alone promises neither erasure nor permanent secrecy. Verification operates on ciphertext commitments without decryption; Tahoe’s time-expiring leases do not replace evidence-gated release.

Five additions:

- **Streaming encryption:** specify authenticated chunks, nonce derivation, chunk position/order, truncation detection and range-read behavior; one giant AEAD record may defeat bounded authenticated streaming.
- **Invalid-content acceptance:** distinguish node acceptance from recipient acceptance, and resolve validly signed undecryptable objects, Message-ID conflicts and their charges.
- **Client crash recovery:** test nonce/ratchet rollback, pending MLS commits, replay, device restoration and catch-up after retention removes required protocol messages.
- **Permanent metadata:** reconcile retained Message-ID/signer/identity evidence with the stated privacy and erasure contract; body expiry does not erase the relationship graph.
- **Measure the composed service:** replace “no performance measurement is needed” with bytes per useful message, catch-up bandwidth, index-fetch leakage, client storage and concurrent-Commit recovery. Ciphertext is bytes; the protocol determines how many and when.