# Decisions for ember, 2026-09-26

Dev head `6c4cf043`, read-only. **Nothing here blocks the wave.** Every lane took its stated default and continues. The live node still runs `bbf52159` (format 8, marker unmarked).
There are **12 packets for ember** (PKT-164, 165, 167, 173 a/b/c, 175, 228, 229, 235, 296, 127), **2 for the coordinator** (PKT-246, 295) and a closing list of decisions already taken under the mandate's §2.
Folded in: PKT-233 was closed by 4b710f03 and is PKT-173 a's default now. PKT-241 (the `keys redecide` verb) is option (c) of PKT-173 a. PKT-230 is PKT-173 b and PKT-231 is PKT-173 c.
PKT-151 (profile monotonicity, packet 1) was closed at 03be0a78 and decided by the coordinator as recommended. It is listed at the end.
Each packet follows the mandate's §12 form. Every trace is quoted from the named record, and where a record has no trace, the packet says so.
**Legend.** "Implemented" means dev already runs the default, so answering the default's letter changes nothing. "Not implemented" means the default is only the recommendation.
**Answer with** one word per packet, for example `164a 165a 167a …`. The default is always (a).

## PKT-164: answer the D25 "already stored" question before the login and posting gates?

**The trace** (planning/evidence/visibility-join-2026-09-25.md, "The witness", `test_lost_reply_then_authorization_change_is_unresolved`):
- A protected node (STARTTLS, `[auth] required`). Login `vj-poster` posts under the cut `finish-durable:kill`, so the post is durable but the reply is lost (exit 3).
- The operator re-enrolls the login `--no-posting` and restarts.
- `reconcile` logs in (`281`) and draws `440 posting not permitted for this principal`, which the client reports as exit 4, `unresolved`. `show` still answers `220`, because the post was accepted.
- A rebound login gets `441 ... this login posts only articles signed by its bound principal` for the same reason: the login gate runs before the Store's decision.

**Constraints already selected:**
- D25: the answer compares the poster's bytes.
- Mandate §5.1: "Any privileged resolution mechanism must have an explicit authority and disclosure contract", and "When an ordinary reader cannot settle it, say unresolved."
- RFC 3977 orders the permission check first (440).
- Withdrawn content stays withdrawn for readers (NNT-013).

**Proposed default (implemented).** Keep the order. The client reports `unresolved` (exit 4), and the operator settles it with `fn-host --fn store STORE inspect <msgid>`, which uses an operator's authority. The coordinator recommends this: "440 first as RFC 3977 orders it, and a held Message-ID must not be probeable by an unauthorized poster."

**Rejected alternatives and their cost:**
- The lane's candidate: answer `already stored` or `different article` (nothing else) before the gates, for a resend under a held Message-ID. Its disclosure is that "whoever holds the exact bytes learns the node holds them", and the conflict line reveals that some article holds the Message-ID.
- A new privileged `ACCEPTED <msgid>` query: "new wire vocabulary, an authority row and a disclosure policy for little gain".

**What it touches.**
- Host: `fnn-owner-attempt-served` order.
- Proof: the composition of `books/login-binding.lisp`.
- Spec: NNT-013's text.

**What continues without it.** Everything. The client already reports unresolved honestly.

**Answer with:** (a) keep 440 first and settle by operator inspect; (b) answer D25 before the gates; (c) design a privileged `ACCEPTED` query.

## PKT-165: an optional content-holding consumer mode, separately charged?

**The trace** (planning/evidence/consumer-e2-2026-09-25.md, "Step 5" / "PKT-165"): "an E2 position 100 and an article numbered 2 at journal position 101 are different coordinates; `held-consumer-cursor` compares a per-group number." Nothing native calls `fn-rcl-reclaimable`, so there is no runtime conflict today.

**Constraints already selected:**
- D03: retention is an explicit obligation.
- The E2 contract says "the cursor creates no pin and specifies an unavailable gap".
- Mandate §5.2: a retaining mode needs "separately charged, durable authority and a proved projection from progress to the objects held".

**Proposed default (implemented).** No implicit pin: content reclaimed before a poll is an explicit unavailable gap. `specs/storage.md` now says consumer positions pin nothing. The coordinator recommends "not now".

**Rejected alternative and its cost.** A retaining consumer registration: a durable hold charged at register and released only by unregister or an explicit waiver. It needs a new Store event kind and charge, a projection proof (event prefix to the article identities after it), a reclaim holder built from that projection, and capacity accounting.

**What it touches.** Store-reclaim holders, consumer-store-events, capacity.

**What continues without it.** Everything in consumer-e2. Scope beyond one group is PKT-255.

**Answer with:** (a) no pin, not now; (b) yes, brief a lane for the charged retaining mode; (c) yes later, after PKT-228's restore floor lands.

## PKT-167: adopt the representation program, with the payload in the arena?

**The trace** (planning/evidence/rep-wave-d-2026-09-25.md §1.2 and §8): the node spends "16 bytes per retained octet". At N = 10,000 × 32 KiB that means 5.55 GB live, a 22 GiB journal-reopen peak, and a checkpoint publication that exhausts the 32 GB heap. A 32 KiB POST allocates 20.8 MB and an ARTICLE 5.8 MB.

**Constraints already selected:**
- D27 (bound work, never data; concrete representations at runtime).
- The mandate's §7.
- "A lane cannot change `fn-record-payloadp` (624 roots) and every byte consumer at once."

**Proposed default (not implemented; the arena itself, PRF-118, is merged at 19a71b2d with no host caller).** Run §3's program in its order:
- (i) The model change: `fn-record-payloadp` becomes `natp`, a handle into the arena, done as one coordinated freeze in the coordinator's batch. Records-shape's 624 roots recertify in 1:44 on hbox. This delivers 320 MB of payload at N = 10,000.
- (ii) The served article as a reference effect.
- (iii) The checkpoint codec over the arena.
- (iv) The ingress span machine.
- (v) Reclaim, feeds and BP, as their measurements justify.

**Rejected alternatives and their cost:**
- A profile ceiling on N × L. D27 forbids it, because it is a constant that bounds data.
- A raw-Lisp arena. It creates "a second authority for the bytes identity is derived from".

**What it touches.**
- The record's *logical* shape changes; its wire encoding does not.
- Every store invariant that says "the payload is an octet list".
- The checkpoint codec, and every host entry in §3.

**What continues without it.** Everything. "The node runs at sixteen bytes per octet."

**Answer with:** (a) adopt, with (i) as the coordinator's freeze; (b) adopt, but land (ii) or (iii) before the freeze (this option is the deputy's, not the record's; rep-wave-d-2 is already running (i) first on Fable); (c) not now.

## PKT-173 a: at reopen, is a declined key statement decided under the grants at its own txid (`:recorded`) or under today's (`:current`)?

**The trace** (planning/evidence/peering-compose-2026-09-25.md "Packet 7"; mandate §12.7; PKT-233):
- Enrol P, then POST a succession with no `keys` grant. The node answers 240 and logs `key-statement declined no-grant`.
- Run `control grant P keys fn.keys` live, then restart.
- The node logs `key-statement enrol-successor committed at-open`.
- "The grant was added AFTER the statement; the restart turned an old decline into new authority."

**Constraints already selected.**
- Mandate §5.4: recovery "must not silently turn an old decline into new authority".
- C3 binds a withdrawal to the configuration in force at its txid (`fn-ctl-config-at`).

**Proposed default (implemented, 4b710f03).** `(defconst *fn-ks-reopen-policy* :recorded)` in books/key-statements.lisp. The decline replays as a decline and needs no new record kind. Re-deciding under today's grants means filing a new statement. The coordinator took this default (statement item 5); you bless or flip it.

**Rejected alternatives and their cost:**
- A durable decline record: a new record kind reopens replay dispatch in about 25 books, and a tenth configuration slot touches every `fn-cfg-value-make`.
- `:current`: restores the traced resurrection.

**What it touches.** host/owner-host.lisp `fn-owner-key-statement-rows`, host/native/owner.lisp, PRF-124. No format change.

**What continues without it.** Everything. The switch is one line.

**Answer with:** (a) `:recorded`; (b) `:current`; (c) `:recorded` plus the explicit `keys redecide MSGID` operator verb (PKT-241, not built).

**Lane key-replay-fixture (2026-09-26) implemented gpt-6's advice, (a) with no supported `:current`:** the constant is gone, the reopen is recorded by definition (`fn-ks-statement-rows`), the old behaviour is only a counterexample fixture in the test book, PRF-140 proves an accepted statement cut before its key change finishes under its admission context, and `keys redecide MSGID` is specified as PKT-325, not built; ember confirms or overrules (overruling to (b) is now a Store format version, not a one-line edit).

## PKT-173 b (PKT-230): hold refused signed evidence as a charged record, or keep refusing?

**The trace.** The record has no trace. The question (peering-compose "Packet 4"; mandate §12.4) is whether to hold `:unenrolled` / `:unsupported-profile` evidence "as a charged durable record so a later enrolment can verify it".

**Constraints already selected:**
- D23: the receiver verifies against the author's own enrollment.
- D27: charge before promise.
- D03: a held item is kept until an authorized release.
- §12.4: holding is never "a license to downgrade a failed signed request into unsigned acceptance".

**Proposed default (implemented).** Classify, do not hold. `fn-pcb-admission-verdict` names seven classes (PKT-240 proved it). A refused signed input produces no event and no charge. The sending peer can offer it again after the enrolment. The coordinator took this default (statement item 7).

**Rejected alternative and its cost.** A bounded, charged hold per boundary (the shape of D23's `peer budget`), with a `:held` verdict distinct from `:carried`: one Store family, a replay branch and the budget theorem again, estimated at one lane. Without a bound, "every held refusal is a permanent capacity claim an unenrolled stranger can make".

**What it touches.** books/peer-authored-accept, stx-verify, the Store families, replay.

**What continues without it.** Everything. D23 carriage is unchanged.

**Answer with:** (a) keep refusing; (b) a bounded charged hold of `:unenrolled` evidence; (c) revisit when a peer asks for it.

## PKT-173 c (PKT-231): keep the pull cursor as `<store>/pull/*.fnpl` files, or make it a Store record family?

**The trace** (peering-compose "Packet 5", "Native"). The six-cut campaign `test_cursor_publication_cuts` kills the process before the write, after the write, and after the fsync of the begin and close records. In every case each article is stored once, and "the duplicate replay after any cut is at most the dead round's listing, each answered 435". Coordinator caveat: "one cut survived only because a process kill keeps the page cache, which says nothing about power loss".

**Constraints already selected:**
- §12.5: "choose by crash semantics, identity scope, write ordering, recovery, and model ownership".
- D03: retention.
- `max-config-generations` bounds the configuration history.

**Proposed default (implemented).** Keep the files. Identity is per peer, the write ordering is local and fenced, recovery is a prefix scan, and the model is PRF-100's. The coordinator took this default (statement item 6).

**Rejected alternative and its cost.** A Store family touches about 25 books (store events, replay, invariants, records-concrete, checkpoint) and keeps a permanent record per round per peer. Its only gain is one fsync domain instead of two.

**What it touches.** books/peer-pull*. Nothing changes under the default.

**What continues without it.** Everything.

**Answer with:** (a) files; (b) a Store family; (c) files now, with a power-loss cut test owed first.

## PKT-175: add a wire-visible HDR item `:fn-enrollment`?

**The trace** (planning/evidence/reader-daily-2026-09-25.md "PKT-175"): "the article page can show the node's historical verdict but not whether the signer is enrolled now; the node serves no query for it." The page reads "current enrollment 'not available'".

**Constraints already selected:**
- ACL2 decides it (AGENTS.md: no Python keyring reading).
- Mandate §5.4: "historical signature validity, historical local acceptance, current enrollment, and current administrative authority stay separate".
- `HDR :fn-control` sets the precedent: it is "the node's historical claim" (specs/peering.md §8).

**Proposed default (not implemented; the coordinator recommends adoption).** An HDR metadata item `:fn-enrollment` giving the current generation and state of the verdict's principal from the node's keyring view. It would be an ACL2 function on the pinned served step, with its theorem, and in the same disclosure class as `:fn-control`. Until then the page says "not available".

**Rejected alternative and its cost.** The client reads the node's keyring file. That is "a second decision engine and a store read from a client".

**What it touches.** The public wire (a new private `:fn-` metadata name), a new PRF, the article page in `tools/fn_web.py`.

**What continues without it.** Everything in reader-daily.

**Answer with:** (a) adopt `:fn-enrollment`; (b) adopt, but only to authenticated readers; (c) leave "not available".

## PKT-228: news-only restore and article numbers (mandate packet 2)

This packet is written in full in **planning/decisions-packets-2026-09-25.md, "Packet 2"** (7cd09f39). It is included by reference.
- *Trace:* a copy-back of an older backup lets new article Y take `g:101`, a number reader R already read as X. Nothing in the store can notice, and RFC 3977 §6 is violated silently.
- *Default (not implemented):* a witness-driven `fn operator CONFIG store rebase WITNESS` on the restored copy, never on the live store. It is a durable per-group numbering floor with the verdicts `:same-history`, `:rebased`, `:refused` and `:uncertain`. A numbering epoch is rejected.

**Answer with:** (a) adopt the witness-driven rebase; (b) a numbering epoch; (c) same-identity restore only, from a known-latest backup.

## PKT-229: policy-member count inside a signed statement (mandate packet 3)

This packet is written in full in **planning/decisions-packets-2026-09-25.md, "Packet 3"** (7cd09f39). It is included by reference.
- *Trace:* if the decoder read profile field 13, nodes A (100) and B (64) would disagree on one validly signed 65-member policy. Member 65's article would be admitted on A and refused on B.
- *Default (not implemented):* keep 64 as statement schema v1's protocol work bound, and ship any raise as a new payload version. Field 13 becomes reserved (at least 64, never a validity input; local use refuses as `:local-capacity`). Found: field 13's reader has no caller today.

**Answer with:** (a) keep 64 and reserve field 13; (b) version the grammar now; (c) read field 13 per node (rejected: split authority).

## PKT-235: mark the live node's store history-marker `required` now?

**The trace** (planning/evidence/node-hbox-bbf52159-2026-09-25.md "Next"; planning/evidence/qual-bbf52159-2026-09-25.md "The upgrade rehearsal" and "Migrate to required tonight, or stay unmarked"). The two-step upgrade is:
1. 7 to 8 unmarked, done at about 21:55 UTC.
2. `store upgrade-profile --history-marker required` "after a day of service, with a fresh snapshot".

The rehearsal on copies gave these results:
- The upgrade: rc 0, `status` shows `history-marker=required`, and `rollback-check` answers `rollback refused history-marker-required-dropped`.
- c3420013 on the required store: rc 4.
- Rollback by the snapshot: rc 0, but "**It loses every article accepted after the snapshot.**"
- U1b: a hand copy of the kept format-7 config over a required store still opens it under c3420013 and drops the requirement, so the rollback is safe only if the operator runs `rollback-check` first.

**Constraints already selected:**
- D31: A ≤ M ≤ D, and "a durable marker-required state after migration so that absence is damage".
- Mandate §2 "does not authorize changing the live node, migrating its store", so this needs your go.

**Proposed default.** The qualification lane's: go after a day of service, with a fresh `cp -a` snapshot first. The node was deployed at 21:55 UTC on 2026-09-25, so about six hours of service have passed at this writing, not a day; (a) below means "go when you judge the service long enough", and the deploy of the next qualified image (PKT-300's checks) is the natural moment.
- What you gain: a missing marker or a lost newest record is refused at open.
- What it costs: availability. Such a node stays down (exit 4, and `StartLimitBurst` gives up) until an operator acts. The lossless rollback to c3420013 is also gone.

**Rejected alternative and its cost.** Stay unmarked: "a store whose marker is deleted together with the files it covers is admitted."

**What it touches.** Only `/tank/fn/node`. No source change.

**What continues without it.** Everything. Note that the next image changes admission accounting (coordinator statement item 2; PKT-300), and its qualification checks the live store's copy.

**Answer with:** (a) go now on bbf52159 with a fresh snapshot; (b) take it with the next qualified deploy; (c) stay unmarked.

## PKT-296: the Store profile's `max-bp-rows` field (10) is read by nothing. Retire it, or bind it?

**The trace** (planning/evidence/bp-lifecycle-3-2026-09-26.md "PKT-276" item 2):
- The node's held rows live in the FNBS journal's `bp-node profile JOURNAL NODE ROWS OCTETS` (default 64 rows and 16 MiB, raise only), "because `bp-service` and `bp-contact` run with no Store".
- Yet `fn operator init --max-bp-rows N` accepts the field, and docs/operator.md advertises it.

**Constraints already selected.**
- D27: admission limits belong to the operator's profile.
- PKT-229 sets the precedent of a reserved field that is never an input.

**Proposed default (not implemented).** Keep the journal's number, one per journal. Retire the Store field: it stays reserved, admitted only at today's values and never an input, and it comes out of the `init` usage and the operator table.

**Rejected alternative and its cost.** A `bp-node serve` that has a Store takes its rows from the Store profile, so the operator sees one number. But a Store-less `bp-service` would still need the journal's number, which leaves two sources for one bound.

**What it touches.**
- books/byte-store-frame.lisp `*fn-bs-pf-max-bp-rows*` and store-profile-namespace `fn-bs-profile-max-bp-rows`.
- native-operator.lisp's init grammar and docs/operator.md.

**What continues without it.** Everything. "Nothing else waits on it."

**Answer with:** (a) retire the Store field; (b) bind it for a Store-backed `bp-node serve`; (c) leave it as is (advertised and unread; not recommended).

## PKT-127: RFC 5536 §3.1.4's special-purpose group names (confirm a standing default)

**The trace.** The record has no trace. 91bdf0e9 (lane group-names-2) says: "the five specific-purpose names are ember's call".

**Constraints already selected:**
- The gpt-6 review of 2026-09-24 says "accept only as an explicit local-agreement profile … never implicit control authority".
- planning/decisions.md, "Adopted defaults ember did not overrule" (around line 1106), admits them "at init and create as an explicit local-agreement profile that confers no authority". The patterns are: first or only component `to` or `control`, any component `all` or `ctl`, and exactly `junk`.

**Proposed default (implemented as the standing default).** The local-agreement profile. The backlog still marks the line as waiting on you.

**Rejected alternative and its cost.** Refuse all five. A local deployment then cannot use, for example, `junk`, and nothing is gained over a no-authority profile.

**What it touches.** books/native-admin.lisp `fn-native-admin-group-name-special-purposep`, docs/operator.md "Add a group".

**What continues without it.** Everything.

**Answer with:** (a) keep the local-agreement profile; (b) refuse them all; (c) refuse all but `junk`.

**Also yours but minor.**
- PKT-289, the shell for agent lanes, is closed with the BRIEF-COMMON "## Shell" section as the default (planning/review-2026-09-26-lane-friction.md §1). Setting `setopt no_nomatch sh_word_split; unsetopt equals` in agent shells is your call.
- planning/decisions.md still has three 2026-09-24 entries marked "pending ember", each with an adopted default:
  - retry after a death following a durable kind 8 (line 993);
  - D02's scope covering a signed served POST (line 1023);
  - a store identity on the wire (line 1112).

## PKT-293: the shape of the records freeze (the payload as an arena handle)

**The trace** (planning/evidence/rep-wave-d-2-2026-09-26.md §1): the brief's freeze "the record's payload field becomes an arena handle" is not closed as briefed: `fn-sn-finish` reads every finished article's payload for the statement verdict (`fn-stx-verdict-of-octets`), the reclaim digests the held payload inside its step, the served machine reads `fn-article-payload` in 40 books (tombstone checks, OVER's body walk, control targets), and the acceptance state's article/pending is a second payload field sharing the record's list. A handle there forces either `fn-arena` through `fn-sn-finish` (38 books), the replay and the served machine (about 100 books of statement moves), or parsed fields decided at intern.

**Constraints already selected:** D27 (the logical model stays octet lists; the executable path does not; no statement of an existing theorem moves), D30 (a named abstraction or refinement theorem at each boundary, not a twin of every helper), the arena's interface obligation (a tombstone is a new seal; space reclaimed at open).

**Proposed default (not implemented; the record's §2 closed design):** two views of one record shape (the wire record keeps its exact octet-list round trip; the owner's retained record carries the handle), intern with parsed fields (the statement verdict and the served walks read fields decided once at intern, not the payload list), a transition parametric in the payload (so `fn-sn-finish` and the replay are proved once over both views), and the served article as a reference effect. Order: the decoder over the buffer first (rep-wave-d-3, urgent: a published checkpoint must reopen), then the two views, then intern, then the served effect.

**Rejected alternatives and their cost:** pushing `fn-arena` through `fn-sn-finish` and the served machine directly (about 140 books of statement moves, a multi-day freeze with dev held); a profile ceiling on N x L (D27 forbids it).

**What it touches:** the record's logical shape (not its wire encoding), every store invariant that says "the payload is an octet list", the checkpoint codec, the host entries of §3.

**What continues without it:** everything; the checkpoint verb already halves its residency at the deployed profile's sizes; the node runs at sixteen bytes per retained octet until the freeze.

**Answer with:** (a) adopt the §2 design in its order; (b) push the arena through fn-sn-finish and the served machine directly; (c) not now.

## PKT-322: a revoked author's retry is refused on enrolment before identity, so it can settle only through the stored copy

**The trace** (planning/evidence/consumer-e2-2-2026-09-26.md, the red test and the review's cut): the consumer dies after fn accepted R and before recording; the author's enrolment is then revoked (`hybrid-revoke-next`); the restarted consumer resends the exact saved artifact; fn refuses it on enrolment before it checks identity, so the D25 "already stored" answer never comes; the consumer keeps the operation `uncertain` and settles it only by `store inspect` (or a served read) showing R stored.

**Constraints already selected:** D23 (the receiver verifies against the author's own enrolment); PKT-164's default (the login and posting gates run before the Store's duplicate answer: a held Message-ID must not be probeable by an unauthorized poster); NNT-019 (reconciliation by re-submission of the same source).

**Proposed default (implemented as the client's behaviour):** keep the gate order; a revoked author is exactly an unauthorized poster; the consumer's `uncertain` stays honest and settles through the stored copy served to a reader the author can still be, or through the operator's `store inspect`.

**Rejected alternative and its cost:** answering "already stored" to a revoked principal for a source it authored before the revocation: a disclosure to a principal the node no longer trusts, and a second gate order to prove.

**What it touches:** nothing under the default; the consumer contract CNS-003 names the case.

**What continues without it:** everything.

**Answer with:** (a) keep the gate order, the stored copy settles it; (b) answer D25 for a source authored before the revocation; (c) a privileged operator query for revoked authors.

## For the coordinator

### PKT-246: a distinct `:conflict` word in the FNCT control reply codec

**The trace** (planning/evidence/source-corpus-2-2026-09-26.md, "The conflict word: a packet"):
- A changed source under a held Message-ID over the control socket (`hybrid-author`) is D25's `:conflict`.
- hybrid-control.lisp maps it to `:refused`, and the client prints `refused hybrid-author REFUSED` and exits 1, the same as for a bad frame, a closed posting policy or an unusable clock.

**Constraints already selected.** D25. `*fn-nctrl-statuses*` is an enumeration codec, so a new word goes last (the precedent is `:article-exceeds-profile-bound`). Exit classes are 0, 1, 3 and 4.

**Default (not implemented).**
- Append `:conflict` to the enumeration and classify it `:refused` (exit 1). The client prints `CONFLICT`.
- Add a theorem that the conflict is a refusal and every earlier octet is unchanged.

**Rejected alternative and its cost.** A distinct exit code 2, which "breaks the three-outcome contract … for one diagnostic".

**What it touches.**
- Format: the FNCT enumeration gains one octet. An old client reads it as `:bad` and exits 4, so clients must be upgraded first or together with the node.
- Proof: native-control's round-trip and class theorems.
- Callers: hybrid-control.lisp, the operator post in owner.lisp, tools/fn_client.py.

**What continues without it.** Everything, because the conflict is correctly a refusal today.

**Answer with:** (a) append `:conflict`, exit 1; (b) exit 2; (c) leave it as `REFUSED`.

### PKT-295: exit code 6 means two things. Which family moves?

**The trace** (backlog PKT-295; the deputy's finding over 4a3f88d6 and 1de05b46; bp-lifecycle-3 "What now works"):
- For the native operator verbs, 6 is `refused`: "no store at the configured `[store] path`: run `init`" (HST-008, docs/operator.md's outcome table).
- For every BP verb, 6 is "a connection lost after it existed; the job stays and is re-offered" (specs/host.md "BP run classes", PRF-131).
- The operator table lists 6 once, with the operator meaning only.
- `bp decode` keeps article-verdict codes, where 3 means "the clock cannot decide the lifetime".

**Constraints already selected.**
- 3 means "recover first" for every fn command. bp-lifecycle-3 therefore moved the lost connection off 3.
- Mandate §4: a connection-local fault costs a connection.

**Default (not implemented).**
- One fn-wide exit table, owned by one ACL2 constant that every family's code function reads.
- The BP interrupted and not-connected classes get codes no other verb uses.
- docs/operator.md lists every code once, with its verb family.
- A theorem that the families' codes are disjoint except 0, 1, 3, 4 and 5.

**Rejected alternative and its cost.** Per-family tables that reuse a number: "a wrapper script reads the number, not the family".

**What it touches.**
- books/bp-run-class.lisp `fn-bprc-run-exit-code`, and native-operator.lisp's no-store answer.
- specs/host.md "CLI exit codes" and "BP run classes", and docs/operator.md.
- PKT-297's further classes will take codes chosen here.

**What continues without it.** Everything.

**Answer with:** (a) the BP classes move to fresh codes; (b) the operator no-store answer moves; (c) keep both and document them per family.

## Already decided under delegated authority (mandate §2); say so if you disagree

The coordinator's statement (planning/decisions-2026-09-26-coordinator-statement.md, 878ef61e, written for gpt-6's review) lists these as decisions taken on its own authority. Its own open question is whether items 2, 3 and 5 exceed §2's "routine reversible" line; each of them is proved and reversible.

1. **PKT-166.** A signed retry through the signing route answers `DUPLICATE` (exit 0) for the same source and `REFUSED` (exit 1) for a changed one. Basis: §5.1, §5.3, D25. The finding it produced, that ML-DSA-65 signing is randomized so a client must resend the saved bytes, is PKT-245.
2. **Packet 1 / PKT-151 / PRF-072.** Admission charges each article the worst case for its own length and group count. `fn-profile-upgrade-keeps-verdict` keeps its statement. Basis: §12.1. Closed 03be0a78. Residual: a store that the old image already over-committed stays unopenable.
3. **PKT-169.** Maintenance reservation: admission reserves room for a release, and the temporary-space check runs against the disk. Basis: §8. Closed 3ba3f9c6 (PRF-129).
4. **PKT-170.** Custody from a refused channel is refused, with a theorem. Basis: §4 and D23; the coordinator ruled it is not a decision.
5. **Packet 7 / PKT-173 a.** The `:recorded` reopen policy (the switch is above for you).
6. **Packet 5 / PKT-173 c.** The pull cursor stays as FNPL files.
7. **Packet 4 / PKT-173 b.** Classify refused signed evidence and do not hold it. D23 is preserved.
8. **The §5.2 join.** The no-pin E2 profile stands, and consumer positions pin nothing (D03). The retaining mode is PKT-165.
9. **Merge sequencing.** Mission-four-node's thirteen service failures were classified as the harness's C1 item. Width-boundary's gate wins over reclaim-lifecycle's F1 where the two collide.
10. **Process.** Source-corpus's fourth farm run (over the cap, green) was accepted. Bp-lifecycle got a continuation rather than a fourth blind run.
