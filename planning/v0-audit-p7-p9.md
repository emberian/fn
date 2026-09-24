# v0 audit: P7, P8, P9 against dev `6d3ed90b` (2026-09-24)

This audit checks every claim in the "Exists" and "Missing" cells of
[the trajectory plan §2.1](plan-2026-09-22-trajectory.md) (P7 at line 134, P8 at 135, P9 at 136)
against the tree at `6d3ed90b`. It uses T9, T10 and T11 in §3 (lines 212 to 214)
as the definition of DONE. It is read-only: no ACL2, farm or native run.

Tools run: `certified_claims.py --explain` on PRF-004, 023, 029, 042, 047, 051 and 058;
`reach_check.py` with no flags (37 orphans, and none of them is in these rows);
and `green_check.py --summary`, which reports all 673 books in the closure of the
658 roots green at their current digest, with no certification owed. So every
book named below is green, and that covers the bp-progress reds of the
previous restart record. "(not cited)" in `--explain` means that no manifest
certifying the current digest is cited in the row. Every row below is in that
state.

---

## P7: two nodes exchange both ways

### The claims in the Missing cell, re-checked

| Claim in §2.1 | Now |
| --- | --- |
| PRF-029 has zero events, although `fn-own-feed-target-is-offerable` exists at `owner-feed.lisp:790` | **Stale.** PRF-029 lists 2 events (`fn-own-feed-target-is-offerable`, `fn-own-feed-targets-omit-no-offerable-peer`). Neither is cited to a manifest, and the status is in-progress. |
| K5 `fn-feed-replay-is-the-live-feed-modulo-inflight` is open | **Replaced, as T9(a) allows.** `fn-feed-port-replay-is-live-modulo-inflight` is at `books/feed-port-replay.lisp:147`, with the host-subject corollary `fn-own-feed-port-tick-replays-the-live-tick` at `:163`. `specs/peering.md` contradicts itself: line 965 says "Earned", and the §4 row at line 1330 still says "Open". The open row has not been retired by name. |
| No octet-preservation theorem | **Stale.** `fn-peer-relayed-octets-change-only-path-and-xref` is at `books/peer-inbound-invariants.lisp:402`. Its registry row is PRF-058, with 8 events, uncited. |
| PRF-047 and PRF-051 have zero events | **Stale.** PRF-047 has 2 events and PRF-051 has 5. Both cite only `certify-20260922T202647Z-3725626`, which is not the current digest (the newest certifying manifest is `certify-20260924T070931Z-1040432`). |
| Never TLS (T9) | **Partly stale.** See the TLS section below. |

### Theorems and subjects

- **Outbound loop freedom (PRF-029).** `fn-own-feed-never-offers-a-loop` (`owner-feed.lisp:812`)
  states: for `(fn-own-feed-tablep tbl)` and `name ∈ (fn-own-feed-targets tbl origin groups path)`,
  `name ≠ origin` and `(not (fn-path-names-p path <name's path-identity>))`.
  - **Subject gap.** The host reaches `fn-own-feed-targets` only through
    `fn-own-submission-targets` (`books/owner.lisp:1686-1698`). That function
    filters the list with `fn-own-feed-new-targets` (`owner-feed.lisp:1280`),
    and its result is what `owner.lisp:1736` enqueues. No theorem relates
    `fn-own-submission-targets` to `fn-own-feed-targets`.
  - **Uncalled sibling.** `fn-own-feed-accept` and its two keystones
    (`owner-feed.lisp:943`, `:955`, "never enqueues on the origin") have no
    caller in `books/` or `host/`. Assurance rule 1 says a property of a sibling
    counts only with an equation to the called function, so they do not count.
  - `reach_check` does not flag PRF-029. It reports reachability, not this
    equation.
- **Inbound loop (K2) and held Message-ID (K3), PRF-042, 12 events.** `fn-peer-loop-is-refused`
  (`peer-inbound-invariants.lisp:137`) and `fn-peer-history-is-refused-at-transfer` (`:196`)
  both conclude "`fn-peer-transfer` leaves the node and `fn-peer-decide-transfer`'s kind is
  `:refuse` or `:have`". The host calls the decision at `host/owner-host.lisp:778`
  (`fn-owner-transit-decide`, `:762`). The offer half,
  `fn-peer-ihave-of-a-held-message-id-is-435-and-no-article` (`:258`), is over `fn-peer-command`.
  The subjects are the called functions.
- **Octets (PRF-058).** `(equal (fn-pu-strip (fn-peer-relayed-octets cfg peer octets) nil) (fn-pu-strip octets nil))`
  has no hypotheses. Its companions are:
  - `-carry-no-xref` (`:421`);
  - `-name-this-node-in-every-path` (`:430`, hypothesis `fn-path-identityp`);
  - `-are-idempotent`.

  The host line is `host/owner-host.lisp:550` in `fn-owner-take` (`:520`), which fills
  `fn-owner-submit-octets`. `fn-peer-injection-arguments-payload-unfolds` (`:393`)
  ties this to the staged payload. The subject is the host-called function.
  - **Residual.** The theorem says every non-Path and non-Xref line is
    unchanged, and that each Path starts with this node's identity. It does
    **not** say that the Path tail is the received Path. The prepend-only half
    is unstated.
- **Restart (K5).** The subject `fn-own-feed-port-tick-peer` is called at `owner-host.lisp:1536`,
  and `fn-own-feed-port-restart-fold` at `:1738`. The equation assumes that the
  persisted record sequence is the generated one, which `books/feed-port-replay.lisp:1-5`
  states. Physical append correspondence is open.
- **Outbound TLS and AUTHINFO (PRF-047 and PRF-051).** `fn-fc-offers-and-credentials-wait-for-tls-and-login`
  is stated over `fn-fc-step` and `fn-fc-after-tls`. Those are now called at
  `host/owner-host.lisp:1591` and `:1496`. The row still cites `:1374` and `:1279`,
  which have drifted. The native callers are `host/native/feed-service.lisp:256`
  and `:194`, which is correct.

### Teeth

| Keystone | Witness | must-fail per hypothesis |
| --- | --- | --- |
| `fn-own-feed-target-is-offerable` (2 hypotheses) | `targets = ("nodeB")`, `tests/acl2/owner-feed-tests.lisp:140` | 2 of 2 (`:148`, `:160`) |
| `fn-own-feed-targets-omit-no-offerable-peer` (3 hypotheses) | none separate | **0 of 3** |
| `fn-own-feed-never-offers-a-loop` | per-conjunct `assert-event (not offerablep)` at `:165` onward | **0** `must-fail` forms |
| PRF-042's loop and history keystones | ground witnesses in `tests/acl2/peer-inbound-tests.lisp` | **0**. The file's 4 `must-fail` forms (`:682`, `:701`, `:713`, `:723`) are all PRF-058's. |
| PRF-058 (no hypotheses) | INN-fed article, `:615` | false-neighbour must-fails `:682` and `:701`. That is sufficient for a theorem with no hypotheses. |
| K5 port replay | 5-article crash-after-third witness | `tests/acl2/feed-port-replay-tests.lisp:60`, 1 (false image) |
| PRF-047 and PRF-051 | `tests/acl2/feed-connection-teeth-tests.lisp` | 24 `must-fail` forms. The row says one per hypothesis, and I did not recount it. |

### Observed on an image

**TLS feed login on `1a9dd747`.** Yes, as an indirect positive observation. In the
two-Store join (`tools/runbooks/two_store_join.py`):

- Each Store is configured `auth.required = true` and `protected_only = true`
  (`:211-215`).
- Each direction's peer is added with `principal <id> <FNAUTH1 profile> false true starttls localhost <cert>`
  (`:228-236`). By `docs/operator.md:305-309`, the `false` is ALLOW-CLEAR.
- `r-peered-to-b` (A→B) and `q-peered-to-a` (B→A) were ACCEPTED in all five runs
  ([record](evidence/two-store-join-1a9dd747-2026-09-24.md)).

Under that configuration a delivery requires a STARTTLS feed and an AUTHINFO feed
login in each direction. What was not recorded:

- No step asserts the feed's TLS or AUTHINFO phase. The harness's own STARTTLS
  and AUTHINFO calls (`:428-439`) are the observer's reader connections, not
  the feed.
- There is no wrong-anchor and no wrong-password negative.
- The matrix rows `V0-TRANSIT-TLS-*` and `-AUTHINFO-*` read "not run" at `bc9be7ec`
  (`evidence/v0-native-peering-bc9be7ec-2026-09-23.json`).
- `tools/runbooks/two-host-protected-gate.md` has never run: no evidence record
  names it.

**Restart delivers exactly one copy.** Observed once on `1a9dd747`. The `a-accepted`
cut SIGSTOPs A after its durable `:feed-sent` record, checks that R is absent at B,
sends `kill -9` to A and restarts it. Then `r-exactly-once` gives `{a:1, b:1}`, and
the final count gives 2 articles at each Store (summary `a-accepted-summary.json`,
steps 14 to 22). This is T9's "kill -9 of the sender mid-transfer". It is at a
developer-image selector point, not a byte-level cut.

**Loop and held Message-ID.** The held-ID offer and transfer answered 435 on `bc9be7ec`
(`V0-TRANSIT-DUPLICATE-*`). `V0-TRANSIT-LOOP-*` is not run at `bc9be7ec`. On 915 those
rows drew 235, because the node then had no path-identity
(`evidence/native-matrix-915-2026-09-22.md:44-48`). No loop row has run since
path-identity landed.

**Only Path and Xref differ.** `V0-TRANSIT-IDENTICAL-*` is `identical: true` at `bc9be7ec`.
The join checks only that the signed source projects equal. It does not diff
the stored octets.

### Packet (T9)

1. **Proof, Opus.** `fn-own-submission-targets-are-feed-targets`:
   `(implies (and (fn-own-feed-tablep (fn-own-feeds o)) (member-equal n (fn-own-submission-targets o))) (member-equal n (fn-own-feed-targets (fn-own-feeds o) (fn-own-sub-origin (fn-own-inflight o)) (fn-own-sub-feed-groups (fn-own-inflight o)) (fn-own-feed-path-of (fn-own-sub-octets (fn-own-inflight o))))))`.
   - Derive `fn-own-submission-never-targets-a-loop` from it. That makes the
     loop theorem's subject the called `fn-own-submission-targets`.
   - Retire `fn-own-feed-accept` and its two keystones, or name them sibling-only.
2. **Teeth, Opus, same lane.** Must-fails:
   - one per hypothesis of `-targets-omit-no-offerable-peer` (3), `-never-offers-a-loop` (2) and the new pair;
   - for PRF-042: `fn-peer-loop-is-refused` without the Path hypothesis, where a
     fresh Path is accepted, and `-history-is-refused-at-transfer` without the
     history hypothesis;
   - the IHAVE/CHECK subject theorems, one per hypothesis (6 and similar).
3. **Proof, Opus.** `fn-peer-relayed-octets-keep-the-received-path-tail`: when the
   local identity is `fn-path-identityp`, the stored Path equals the local
   identity, `!`, and the received Path (or the expected-identity diagnostic
   form). Add one must-fail without the hypothesis.
4. **Registry, root.** Cite the current-digest manifests for PRF-029, 042, 047, 051
   and 058, and update PRF-047's host lines to `1591` and `1496`. In
   `specs/peering.md:1330`, retire the K5 "Open" row by name in favour of
   `fn-feed-port-replay-is-live-modulo-inflight` with its stated premise.
5. **Native run, Opus, on the next image.** Run the matrix's two nodes with
   path-identity set: the `V0-TRANSIT-LOOP-*`, `-TLS-*`, `-AUTHINFO-*`,
   `-TLS-WRONG-ANCHOR` and `-AUTHINFO-WRONG` rows. Add one assertion to
   `two_store_join.py`: diff R at A against R at B after `fn-pu-strip`.
6. **Open, and not closable in v0.** The physical correspondence between the FNFD
   append and the generated records. It is the premise of K5 and belongs to T16.

| P7 | theorem: K2 in and out, K3, K5 (port form), PRF-058 exist; missing: a subject equation for outbound loop freedom over `fn-own-submission-targets` and the Path-tail prepend clause | subject: inbound, octets, K5 and TLS are over host-called functions; outbound loop is over a filtered callee plus an uncalled `fn-own-feed-accept` | teeth: PRF-058, 047/051 and K5 have them; PRF-042 has 0 must-fail, `-omit-no-offerable` 0 of 3, `-never-offers-a-loop` 0 | observed: 1a9dd747 join has TLS+AUTHINFO feed both ways (indirect) and kill -9 → exactly one copy; loop, TLS-negative and octet-diff rows not run | obstruction: none of design; FNFD physical correspondence premise (T16) |

---

## P8: a signature an agent can check, and the verdict a reader sees

### The claims in the Missing cell, re-checked

| Claim | Now |
| --- | --- |
| `fn-stxe-profile-supportedp` returns `nil` for every profile (`:61`) | **Stale.** It is now `(equal profile *fn-hsig-profile-tag*)`, at `books/stx-evidence-records.lisp:62-64`, and it is asserted true at `tests/acl2/stx-evidence-records-tests.lisp:30`. `fn-stxe-authority-verdict` (`:66-71`) returns `:requires-binding`, not a verdict, which is what `specs/identity.md:121-125` intends. No must-fail. |
| S6 `:fn-verified` is not built | **Stale.** `books/nntp-verdict.lisp` renders `HDR :fn-verified` from the connection's pinned verdict list. `books/nntp.lisp:193-195` routes it. `fn-own-refresh` pins `(fn-sn-verdicts s)` (`books/owner.lisp:829`). On `1a9dd747`, B answered `0 verified <principal> keyring 1` to `HDR :fn-verified` for R (`b-verdict-gen1` ACCEPTED in all five runs; the harness check is at `two_store_join.py:574-590`). It held across a B restart in the `b-verdict` cut. |
| `fn-sig-verify` is constrained and unattached | **Holds.** It is constrained at `books/crypto-seam.lisp:109-127`. `books/crypto-attach.lisp:29-34` says signature verification is "NOT touched". `docs/architecture.md:115-116` says the same. `host/native/signatures.lisp` has no `defattach`. |
| So the article arm of `fn-sn-finish` cannot evaluate a verdict on a signed article | **Holds, but it is no longer the path signed articles take.** See the next section. |
| PRF-023 is open on the accepted-statement arm | **Closed in statement.** `fn-sn-finish-preserves-indexedp` (`books/store-node-invariants.lisp:1802`) is `(implies (fn-sn-indexedp s) (fn-sn-indexedp (fn-sn-finish s)))` with no arm hypothesis, and the `fn-stxa-p` arm is a proof case. PRF-023 has 8 events, all uncited, status in-progress. Teeth: one must-fail (a stale composite index, `tests/acl2/store-node-composite-index-tests.lisp:106`). |

### Where the verdict actually comes from

There are two arms.

- **Article arm.** `fn-sn-finish-records-the-acceptance-verdict` (`store-node-invariants.lisp:394`)
  covers only the article arm. Its hypotheses exclude the `fn-stxe`, `fn-stxk`,
  `fn-stxa`, retention, consumer and topic records. That arm records
  `fn-stx-verdict-of-octets` (`books/stx-lace.lisp:71`), which reads the
  **FN-Statement** header (`books/stx-verify.lisp:99-116`). Only on a parsed
  statement whose creator is in the keyring does it reach `fn-prin-verifiedp`
  (`books/principal.lisp:257`) and then `fn-sig-verify`, which is unattached.
  An **FN-Authorship** (hybrid) article on this arm gets `:absent :no-field`.
- **Kind-4 arm.** Hybrid-signed articles acquire a verdict only as a kind-4
  `fn-stxe` event, through two paths:
  - control-socket `hybrid-author`;
  - since the peer-authored packet, protected transit. The chain is
    `fnn-owner-attempt-transit` (`host/native/owner.lisp:746`), then
    `fn-owner-peer-carrier-form` (`host/owner-host.lisp:1111`), then
    `fn-pa-authorized-event` (`books/peer-authored-accept.lisp:79`).

  The verification in this arm is an **observed-verdict argument**. libsodium
  and OpenSSL observe the exact ACL2 preimage, ACL2's `fn-hsig-authorize`
  requires both observations, and `fn-stxk-apply-verdict`
  (`books/stx-keyring-records.lisp:193`) appends the event to the carried verdicts.
  `specs/identity.md:121-137` names the argument.

So the answer to the question asked is:

- The S6 exposure the ingress packet produces is real and observed on the image.
- The **only** theorem about the reader's content is `fn-nntp-verdict-hdr-msgid-is-recorded`
  (`books/nntp-verdict.lisp:86`). It unfolds `fn-nntp-verdict-hdr-msgid`, which
  is an inner function of `fn-nntp-archive-command-pinned`.
- `fn-stx-reader-verdict-is-the-recorded-verdict` (`books/stx-reader.lisp:52`) is
  the definition of `fn-stx-reader-verdict` restated. Under the assurance
  rules it is not a proof event.
- No theorem states that after the host-called `fn-sn-finish` of a kind-4 event
  `e`, `(fn-sn-verdict-lookup s' (msgid e))` is `e`'s verdict. None states that
  a connection opened after `fn-own-refresh` renders it. PRF-026 ("the reader's
  verdict is the recorded verdict", S6-1) is `planned` with **zero events**.
- The composition is exercised only by ground witnesses through `fn-own-step`
  (`tests/acl2/owner-verdict-tests.lisp`: 14 assertions, 0 must-fail), a native
  raw test (`tests/native_peer_authored_accept_raw.lisp`, with ACL2 values
  stubbed), and the join on `1a9dd747`.

### Checkable without trusting fn

**Not established.** Every verifier in the tree is fn code:

- the join's `verify` step calls the native `hybrid-verify-source` (`two_store_join.py:552-566`);
- Mini's `mini-verify-r-at-b` goes through `fn_bridge.sh --fn hybrid-verify-source` (`:919-926`);
- `tests/test_native_hybrid_author.py` uses the native `hybrid-verify-carrier`.

`tools/fn_client.py` has no `--sign`, and there is no `principal new` verb.
The subject framing is proved injective:

- `fn-hsig-subject-body-injective` (`books/hybrid-signature-invariants.lisp:184`),
  under `fn-hsig-subject-p` of both arguments, gives equal bodies ⇒ equal
  principal, keys and source;
- `fn-hsig-signed-preimage-injective` holds likewise;
- both are in PRF-048, which the row says has one must-fail per hypothesis
  (`tests/acl2/hybrid-signature-invariants-tests.lisp`, 6 must-fail).

So a second implementation is *possible* from `specs/identity.md`, but none exists.

**Two defects found:**

1. **POST keeps no verdict.** The local NNTP POST path
   (`fnn-owner-complete-bound-submission`, `host/native/owner.lisp:1131`, then
   `fnn-owner-attempt` at `:1173`) has no carrier classifier. An agent that
   POSTs an FN-Authorship-signed article over NNTP gets no durable verdict.
   Only `hybrid-author` and transit produce one.
2. **Missing assumption.** No `A-*` encapsulate in `books/assumptions.lisp`
   names the primitive-observation trust. The ACL2 verdict depends on
   libsodium's and OpenSSL's answers.

### Packet (T10)

1. **Proof, Fable, T10a.** `fn-sn-finish-of-an-evidence-event-records-its-verdict`: under
   `(fn-sn-completion-enabledp s)` and `(fn-stxe-p (fn-sn-completion-record s))`,
   `(fn-sn-verdict-lookup (fn-sn-finish s) (msgid-of e))` equals the item built
   from `e`. Add its sibling: every other message's lookup is unchanged. Teeth:
   a must-fail without `enabledp`, and one without `fn-stxe-p`, where an article
   record gets the article-arm verdict instead.
2. **Proof, Opus, T10b.** `fn-own-hdr-fn-verified-is-the-store-verdict` over **`fn-own-step`**
   (the function the host calls): for a connection opened after `fn-own-refresh`
   at store `s`, the reply to `HDR :fn-verified <m>` is
   `(fn-stx-reader-item (fn-stx-reader-lookup m (fn-sn-verdicts s)))`. Then
   rename `fn-stx-reader-verdict-is-the-recorded-verdict` to `-by-definition`
   and move PRF-026's events to the new theorem. Teeth:
   - a must-fail for a reader pinned *before* the publication, which
     `owner-verdict-tests.lisp` already builds as a witness;
   - a must-fail for a Message-ID absent from the archive.
3. **Assumption, Opus.** Add `A-SIG-OBSERVE` as an encapsulate in
   `books/assumptions.lisp`: a constrained observation relation for Ed25519 and
   ML-DSA-65, which `fn-hsig-authorize`'s theorems mention. The alternative is a
   `defattach` for `fn-sig-verify`, but that realises only the FN-Statement arm
   and is not needed for hybrid.
4. **Host and proof, Opus.** Route the local POST path through
   `fn-owner-peer-carrier-form`, or refuse a present FN-Authorship on POST.
   Add the theorem that a present-malformed carrier on POST is refused, and a
   native test.
5. **Client, Sonnet.** Add `principal new --seed`, `fn_client.py post --sign`
   (key file mode 0600), and `tools/verify_hybrid.py`: an independent verifier
   using Python `cryptography` and OpenSSL only, with no fn import and no fn
   binary. It is driven over `ARTICLE` output with its own keyring.
6. **Native run, on the next image.** Run the join with the independent
   verifier replacing `bridge_verify`. Add HDR after key rotation and
   revocation (persisted historical verdict), and a POST-path signed article.
7. **Registry.** Cite current manifests for PRF-023, 048 and 069, and move
   OBJ-003 and OBJ-007 when 1 to 6 land.
8. **Decision for ember.** Whether FN-Statement's article-arm verdict needs
   `fn-sig-verify` evaluated in v0. If it does, an Ed25519 attachment packet is
   required. If not, the arm's verdict for statement-signed articles stays
   non-evaluable, and the release says so.

| P8 | theorem: injectivity (PRF-048) and indexedp over all arms exist; missing: the kind-4 finish verdict keystone and HDR-over-`fn-own-step` (PRF-026, 0 events) | subject: `nntp-verdict` theorem is over inner `fn-nntp-verdict-hdr-msgid`; `stx-reader` "is-the-recorded-verdict" is definitional | teeth: nntp-verdict, owner-verdict and stx-reader tests have 0 must-fail; PRF-048 has them | observed: `HDR :fn-verified` = `0 verified … keyring 1` at B on 1a9dd747, across restart; verification only via fn's own binary | obstruction: no non-fn verifier or `--sign` client; POST path records no hybrid verdict; primitive-observation trust is not a named assumption; `fn-sig-verify` unattached (decision) |

---

## P9: keep every accepted article until release, and refuse what cannot be afforded

### The claims, re-checked

- **"No keystone states that an unaffordable obligation is refused" (the RET-002 note). Stale.**
  - The theorem is `fn-retain-admit-refuses-unaffordable-obligation`
    (`books/retention-invariants.lisp:141`):
    `(implies (> (+ (fn-retain-reserved s) charge) (fn-retain-capacity s)) (equal (fn-retain-admit s id subject kind evidence charge) s))`.
  - RET-002 is `implemented`, and its note now cites this theorem
    (`planning/requirements.json:750-773`).
  - The theorem is **not** among PRF-004's six events: `--explain PRF-004`
    lists admit-preserves-statep, release, and the others. No PRF row carries it.
- **Subject.** It is the wrong function in composition.
  - The host calls `fn-store-sn-prepare` (`host/store-node-host.lisp:438`). That
    calls `fn-spc-prepare` (`:472`), which equals `fn-sn-prepare` under
    `fn-snt-relation` (`books/store-prepare-correspondence.lisp:170`), which
    calls `fn-sn-prepare-node`, which calls `fn-node-prepare`
    (`books/node.lisp:180-205`).
  - `fn-node-prepare` refuses at `:185-188` on its **own**
    `fn-retain-admissiblep` test. It calls `fn-retain-admit` (`:197`) only after
    that test passed.
  - So the refusal branch of `fn-retain-admit` is **unreachable in
    composition**. The keystone's only hypothesis negates one conjunct of the
    branch test, which makes it a `-by-definition` fact under the assurance
    rules.
  - The note argues "identical call, identical arguments". That is prose, not
    the named equation that rule 1 requires.
- **Teeth.** `tests/acl2/retention-tests.lisp:254-294` has a reachable
  capacity-10/reserved-6 witness, refusing at charge 5 and admitting at 4. The
  hypothesis-dropped case is an `assert-event` of the negated conclusion, not a
  `must-fail`, and the file has 0 `must-fail`.
- **Charge ownership.** It is ACL2's. `fnn-charge` (`host/native/io.lisp:971`)
  asks `fn-store-charge`, and transit uses `fn-charge-for-payload`
  (`books/identity.lisp:271`).
- **Keeps until explicit release.** D03 holds through:
  - `fn-retain-wrong-evidence-does-not-release` (`books/retention.lisp:327`);
  - `fn-retain-exact-release-records-its-evidence` (`:336`);
  - the release-preserves theorems (`retention-invariants.lisp:80-117`).

  These are over the ledger, not over the Store's served archive. No theorem
  says an accepted article stays in `fn-state-articles` across every
  `fn-sn-finish` arm until a matching release record. The retention arm's
  verdict-keeping theorem (`store-node-invariants.lisp:427`) is about verdicts,
  not articles.
- **Observed.** `V0-CAP-REFUSE-{A,B}` were refused on 915
  (`evidence/native-matrix-915-2026-09-22.md:77`). They are "not run" at
  `bc9be7ec` and were not run on `1a9dd747`: the night record says no matrix
  ran on it.

### Packet (T11, restated)

1. **Proof, Sonnet.** `fn-node-prepare-refuses-unaffordable-obligation`:
   `(implies (and (fn-node-statep s) (> (+ (fn-retain-reserved (fn-node-retention s)) charge) (fn-retain-capacity (fn-node-retention s)))) (equal (fn-node-prepare s g m p gs id subj ev charge stamp) s))`.
   Lift it to `fn-sn-prepare` (and so to `fn-spc-prepare` under
   `fn-snt-relation`): the returned state is `s`, and the host maps `(equal next s)` to `:refused`
   (`store-node-host.lisp:475`). Mark `fn-retain-admit-refuses-…` `unreachable-in-composition`
   or rename it `-by-definition`.
2. **Teeth, same lane.**
   - A `must-fail` per hypothesis of (1): drop `fn-node-statep`, and drop the capacity comparison.
   - Convert the existing assert-event tooth into a `must-fail` of the theorem without its hypothesis.
3. **Proof, Opus, the "keeps" half.** `fn-sn-finish-keeps-accepted-articles`:
   for every arm, `(fn-find-article m (fn-state-articles (fn-node-acceptance (fn-sn-node s))))`
   is preserved, unless the completion record is a retention release whose
   evidence matches `m`'s obligation. If v0 has no article deletion, the
   theorem states that articles are never removed. Teeth: a must-fail showing
   that a matching release (if one exists) is the only removal.
4. **Registry.** Add both keystones to PRF-004 and cite the manifest.
5. **Native run.** Run `V0-CAP-REFUSE-{A,B}` on the next image. The expected
   outcome is REFUSED (441 with the capacity reason, and the exit code for
   refused), not UNCERTAIN.
6. **Stays open.** Physical-byte charging (RET-002's implementation_note) is a
   twin of the abstract charge. It is not closed in v0, and the release must
   quote the abstract-unit scope.

| P9 | theorem: `fn-retain-admit-refuses-unaffordable-obligation` exists; missing: the same over `fn-node-prepare` and `fn-sn-prepare`, and a "never removed without matching release" statement over `fn-sn-finish` | subject: `fn-retain-admit`'s refusal branch is unreachable from the host (`fn-node-prepare` refuses first, `node.lisp:185`) | teeth: reachable witness, 0 `must-fail` (assert-event only) | observed: `V0-CAP-REFUSE` refused on 915 only; not run on bc9be7ec or 1a9dd747 | obstruction: none of design; physical-byte charge remains abstract (stated scope) |
