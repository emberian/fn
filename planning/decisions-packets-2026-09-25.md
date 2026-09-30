# Decision packets 2 and 3 (2026-09-25)

The form follows [the mandate §12](handoff-2026-09-25-fable-mandate.md). These are [now.md](now.md) §5 items 2 and 3. Traced read-only at dev `c086f0e4`. Nothing here is implemented, and no store was restored to get these answers.

## Packet 2: restoring a news-only store, and article numbers (PKT-100)

**Where the numbers live.** A group's next number is not stored anywhere. Replay rebuilds it: each durable completion record advances it through `fn-bump-number` (books/acceptance-alloc.lisp), and `fn-next-number` reads it. The keystones `fn-own-served-watermarks-never-decrease` and `fn-own-raw-local-number-is-never-reassigned` (books/owner-numbering.lisp) hold because one record list only grows (`fn-own-step-records-prefix`). A restore replaces that list with a shorter one, so it falls outside their hypothesis.

**Trace (minimal).** Group `g` has next = 101 at backup time B. The live node then accepts article X as `g:101`, and reader R sees `GROUP g` → `211 … 1 101 g` and reads 101. The disk is lost, and the operator copies B back in, as docs/operator.md "Back up" describes. Replay yields next = 101 again. A new article Y takes `g:101`. R's newsrc already marks 101 as read, so R never sees Y. A reader that cached X's overview now has it under Y's number. Nothing in the store can notice:
- The D31 marker travels with the snapshot. Mandate §5.6: full-store stale-snapshot replacement is not detected.
- `fn-anchor-restore` (books/anchor.lisp:710) shows only that a fresh anchor is newer than the anchor the image references. That says when the image was made, not that it is the latest state. The native `fn anchor` has only `acquire`.
- The consumer-incarnation path cannot help either. `fn-cpa-rollover-proposal` (books/checkpoint-auxiliary.lisp:75, reached from host/native/checkpoint.lisp `fnn-checkpoint-command-clone`) returns `:refused :unbootstrapped` when the store has no consumer state.
- No restore verb exists: `fn-nop-parse-store` has upgrade-profile, needs-upgrade, rollback-check, compact and checkpoint.

**RFC consequence.**
- RFC 3977 §6: "there MUST only be one article with a given number within any newsgroup", and "articles arriving later MUST have higher numbers than those that arrive earlier". This is per server, and the RFC has no epochs.
- RFC 3977 §6.1.1.2: new articles take numbers "greater than the reported high water mark". A reinstated article is "not a new article reusing the number".
- Clients rely on this. §6.1.1.2 lets them discard everything below the low water mark "as these will never recur". So a reused number silently hides or mislabels articles. It is not a visible error.

**Selected constraints.**
- D10: a restore or clone "creates or validates a fresh sequence namespace".
- D31: A ≤ M ≤ D. Mandate §5.6: a store-local count is not an anti-rollback witness.
- AGENTS.md: never merge local numbers globally. Uncertain, refused and accepted stay distinct.
- Peers are unaffected. Peering is keyed by Message-ID (IHAVE, and NEWNEWS with a time cursor in books/peer-pull.lisp). Only NNTP readers hold numbers.

**Correction 2026-09-30 (PKT-336): proposal only; PKT-228 remains open and unimplemented.** A sampled high-water is not an upper bound on every prior issuance. For example, a backup through 100 and a sample at 110 do not cover the old writer subsequently issuing 111–120. Equal transaction IDs and high-waters also do not establish equal history. The earlier acceptance conditions below are replaced by three independent obligations; no restore lane may implement a success branch from the earlier conditions.

**Proposed default: an explicit rebase with complete evidence, run on the copy, never on the live store.**
- The proposed verb remains `fn operator CONFIG store rebase WITNESS`. A witness must identify the referenced store/history and its integrity evidence, its provenance and trust assumptions, and its coverage of every prior allocation or advertised high-water whose reuse would violate the numbering contract. A periodic `LIST ACTIVE` or status sample alone supplies no such coverage. A final observation requires a quiesced old writer that cannot resume; alternatively, an independently durable allocation bound must have been established before the covered numbers could be issued.
- An ACL2 verdict must establish three separate properties before acceptance:
  1. **History identity and integrity.** Validate the relationship between the recovered history and the history named by the evidence. Equal scalar txids, record counts or high-waters are insufficient; an abstract digest equality alone does not prove real integrity or the witness's honesty.
  2. **Complete prior issuance coverage.** Establish an upper bound covering every relevant earlier issuance, including groups absent from the current configuration. An older or incomplete sample cannot establish this property even when every sampled high exceeds the recovered high.
  3. **Mapping-preserving transformation.** Preserve the article-number mappings of all recovered articles. Raise future allocation floors strictly above the covered earlier highs, never lower a recovered next number, never renumber existing articles, and refuse an unrepresentable floor rather than wrapping.
- The proposed outcome classes are:
  - `:accepted :same-history` only when the history identity/integrity and complete coverage evidence establishes that the recovered history preserves the applicable issued mappings and needs no raised floor. Matching txid/high-water scalars alone never select this branch.
  - `:accepted :rebased` only when all three properties hold and the required raised floors are durably published before serving.
  - `:refused` for demonstrated contradictory evidence, an invalid transformation, or an unrepresentable floor, naming the reason.
  - `:uncertain` when history identity, integrity, coverage or witness authority is not established, including a missing group or a merely sampled high-water. The store stays unserved; an ambiguous persistence result also remains a recovery event, never an accepted in-memory update.
- An accepted transformation would persist a numbering-floor record with the floors for every covered group, a fresh restore incarnation and the witness's provenance. Its replay rule must preserve existing mappings and apply `next := max(next, floor)` only to future allocation. Durable layout, evidence validation, exit-code mapping and the actual proof/caller contract remain proposed work, not implemented guarantees.
- Operator documentation must distinguish consistent evidence from complete evidence. A witness consistent with the copy can still be too old to prevent reuse. No claim of safety may depend on an unproved assertion that the latest sample covered all later activity.

**Rejected alternatives and their real cost.**
- (b) A new numbering epoch that restarts or lowers numbers under the same group name. This violates RFC 3977 §6 arrival order, and no client understands an epoch. Choosing it means every existing newsrc for the group goes silently wrong.
- (a) A gap guessed from wall time or the profile. The mandate calls it safe only when the high-water is known. A guessed gap turns a known-unknown into a silent reuse.
- (c) Same-identity restore, left implicit. This is today's copy-back, and nothing demonstrates the backup is the latest. A same-history success would require the separate identity, integrity and complete-coverage obligations above.
- The cost of the default:
  - one new Store record kind, which touches store-events, replay, records-concrete, checkpoint and the identity and carried invariants (about 25 books, the count peer-pull made for its FNPL alternative);
  - a store format bump, if kinds need one;
  - operators must keep a witness.

**What changes.**
- Format: the numbering-floor record.
- Proof: owner-numbering's two keystones must extend across the mapping-preserving rebase step, with an explicit complete-coverage premise (every future next ≥ floor > every covered prior high). Literal witnesses must separate missing history identity, incomplete coverage and a mapping-changing transformation; scalar equality or a sampled floor is not sufficient.
- Callers: books/native-operator.lisp `fn-nop-parse-store` and the host/native/io.lisp dispatcher (beside `fnn-command-upgrade-profile`).
- docs/operator.md "Back up" and "Recover".

**Work that continues without the decision.**
- The clone path for stores that have consumer state.
- A docs warning that copy-back reuses numbers.
- Witness capture: `LIST ACTIVE` is served today.
- D31 marker work, and the anchor's native restore.

**Decision still open (PKT-228):** whether to adopt a witness-driven `store rebase` with durable per-group floors. PKT-336 corrects the prerequisite safety contract; it does not select an evidence mechanism, approve the product proposal, or establish an implementation. Any accepted design must satisfy all three obligations above and keep missing coverage uncertain.

## Packet 3: profile field 13 and the policy-member count

**What exists.**
- `*fn-pol-max-members*` = 64 (books/policy.lisp:59) is a check inside the grammar of a signed statement. `fn-pol-policy-of-items` returns `:member-count` past 64. `fn-pol-policy-decode-exact` decodes at most `*fn-pol-max-policy-items*` = 68 items within `*fn-stmt-max-payload-octets*` = 8192.
- Profile field 13, `max-policy-members` (books/byte-store-frame.lisp:121), defaults to 2^20. docs/operator.md:110 and the `init` usage line advertise it. Its only reader, `fn-bs-profile-max-policy-members` (books/store-profile-namespace.lisp), has no caller. So the operator knob does nothing today.
- Nothing served reaches policy. policy → policy-invariants → stx-policy → stx-epochs / stx-authority are certified roots (Makefile:871-872) with no host caller.

**Counterexample, if the decoder read field 13.** Nodes A (field 13 = 100) and B (the 64 default) both hold P1 (10 members) and then P2, a 65-member policy from the same authority, validly signed.
- On A, `fn-pol-statement-policy` P2 is a policy, so P2 is in force through `fn-pol-current`.
- On B it decodes to `:member-count`. That makes it nil, so P2 is not even a `fn-pol-candidatep`, and P1 stays in force.
- Member 65 posts article S. `fn-stx-transit-authority-ok` admits S on A and refuses it on B. The refusal carries no reason saying "local", and no equivocation evidence is recorded.
- So one signed statement means two things. That is the outcome the mandate forbids.

**Selected constraints.**
- D27: admission limits belong to the profile, and no arbitrary ceiling applies to stored data. Profile validation, representation and format evolution must agree.
- The policy term binds the statement's content id (the policy.lisp header, ATLAS law 12), so validity must be portable.
- AGENTS.md: refused and uncertain stay distinct.

**Proposed default: keep 64 as a protocol work bound of statement schema v1, and take field 13 out of validity.**
- Why 64 is justified:
  - 64 members × 34 octets (a CBOR 32-octet id) = 2,176 octets, which sits well inside the 8192-octet payload bound. That payload bound alone would allow about 229.
  - The duplicate check `fn-stmt-no-duplicatesp` is quadratic: 2,016 id comparisons at 64. `fn-pol-current` repeats that decode for every candidate in the lace.
- A larger count ships only as a new policy payload version: a new tag or `*fn-stmt-schema-version*`, with its own item bound.
  - A node without v2 classifies such a statement as `:unsupported-version`. It keeps it as evidence and does not call it invalid.
  - v1 statements keep their v1 meaning forever.
- Field 13 stays in the format-8 layout, so there is no layout change.
  - Profile admission requires it to be ≥ 64, so every profile can represent every valid v1 statement.
  - The docs and the `init` usage line call it reserved.
  - Any future local use (for example, total principals held) must refuse with `:local-capacity max-policy-members` at group or carriage admission. It must never change which policy is in force.

**Rejected alternatives and their real cost.**
- Reading field 13 in the decoder produces the counterexample above: split authority between honest nodes.
- Versioning the grammar now (v2 with a count derived from R) costs:
  - two decoders in policy.lisp;
  - a proof that v1 and v2 terms stay separate, through policy-invariants and the `fn-pol-receipt-re-verifiable` proof;
  - stx re-certification.
- No served caller or group needs more than 64 posters today, so versioning now buys nothing.

**What changes.**
- No record format change.
- The ≥ 64 check goes into `fn-bs-profile-admittedp`, which is byte-store-frame with about 300 dependents, or into a store-profile-namespace gate at init and upgrade (cheaper). It needs teeth either way.
- books/native-operator.lisp usage/`fn-nop-parse-profile-flags`, and docs/operator.md:110.
- A theorem in policy.lisp: the decoder's verdict is a function of the octets alone, with no profile argument.

**Work that continues without the decision.**
- Everything in stx/policy. Field 9 (consumers) and field 10 (BP rows) move to the profile as the bounds-profile record plans.

**Recommendation:** keep 64 as the schema-v1 protocol bound. Any raise is a new policy payload version, and field 13 is reserved (≥ 64, never a validity input; local use refuses as `:local-capacity`). **yes?**
