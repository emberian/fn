# v0 audit of P1 to P6 against dev `6d3ed90b` (2026-09-24)

This audit re-checks the "Exists" and "Missing" cells of P1 to P6 in
[the trajectory plan §2.1](plan-2026-09-22-trajectory.md) (lines 127 to 132)
against the tree at `6d3ed90b`. It judges each P by §3's DONE definition:
the theorem exists over the subject the host calls, its teeth book exists,
`green_check` is clean, the behaviour was measured on an image, and the
evidence file exists. This is a read-only lane: it ran no ACL2, no farm job
and no native test.

**Tools run (read-only):** `python3 tools/green_check.py --summary` reports
673 of 673 books in the closure green at their current digest, 0 red.
`--table` supplies the per-book rows cited below. `python3 tools/reach_check.py`
finds 37 orphaned registry events; none of them is in PRF-028, -031, -039,
-040 or -052. `python3 tools/certified_claims.py --explain PRF-028/031/039/040/052`
and `python3 tools/ledger.py` (without `--write`; `tools/ledger.py:2490`
writes only under `--write`) raised no finding on the theorems below.
`teeth_check.py --summary` was run statically.

**Image note:** books changed between the image source `1a9dd747` and
`6d3ed90b` only in proof hints and cost repairs
(`git diff --stat 1a9dd747 6d3ed90b -- books host`: no host file changed,
and no definition in the P1 to P6 books changed). Native runs on `1a9dd747`
covered only BP N03, the interrupted fragment, consumer E2 and the two-Store
join ([record](evidence/native-cut-1a9dd747-2026-09-24.md), "What this does
not establish"). **No P1 to P6 test ran on `1a9dd747`.**

**A reach_check caveat that applies to every P:** `reach_check` counts a
theorem as hosted when a host line reaches its subject in the call graph
(`tools/reach_check.py:139-149`). That graph is seeded by any book symbol a
`tools/*.py` string names, including a docstring. `fn-auth-step` is reached
this way: its only non-theorem mention outside `nntp-auth*` is the docstring
at `tools/run_owner.py:278`. The native served path never calls it. "Not
orphaned" is therefore not evidence of which function the host calls. Each
host line below was traced by hand.

## The served call chain (used by P1, P3 and P5)

A socket read becomes `fn-owner-chunk` at `host/owner-host.lisp:1235`, which
calls `fn-ocfg-read-tls-prefix` (`:1240`). The chain continues through:

1. `books/owner-tls-prefix.lisp:62`, equated to `fn-ocfg-read` by
   `fn-ocfg-read-tls-prefix-is-full-read` (`:91`, hypothesis `fn-wire-statep`
   of the connection's wire);
2. `fn-own-read`, reached through `books/owner-config.lisp:524`, a
   definitional wrapper;
3. `fn-served-step` (`books/owner.lisp:1336`);
4. `fn-served-dispatch` (`books/served.lisp:616`);
5. `fn-auth-step-pinned` (`books/nntp-auth.lisp:2659`);
6. `fn-auth-delegate-pinned`, then `fn-peer-step-pinned`, then
   `fn-nntp-step-pinned` (`books/nntp.lisp:243`).

Other entry points skip `fn-ocfg-step`:

- `fn-own-outcome`, called directly at `host/owner-host.lisp:1034`;
- `fn-ocl-complete` (`:276`) followed by `fn-own-configure` (`:284`);
- `fn-opc-prepare` (`:340`);
- `fn-ocfg-fault` (`:1273`);
- `fn-ocfg-open` (`:1218`).

Everything else goes through `fn-owner-step`, which calls `fn-ocfg-step`
(`:212`).

---

## P1: protected channel and authentication

**Theorems.**

- **The gate: exists, but moved.** `fn-auth-gated-command-is-refused-and-not-performed`
  is now at `books/nntp-auth.lisp:1613`; the cell cites `:1348`. It is stated
  over `fn-auth-step`. It has seven hypotheses: `fn-auth-sessionp`, not
  handshaking, `config-requiredp`, no subject, `command-inputp`,
  `arguments-at-mostp` and `restricted-keywordp`. Its conclusion is that the
  step makes no submission, makes no offer and leaves the session unchanged,
  and that the effects equal `(fn-auth-single as "480 authentication required")`.
- **Other exported theorems:**
  - `fn-auth-step-protected-only-refuses-authinfo-before-tls` (`:2074`): the
    483 answer;
  - `fn-auth-step-post-without-permission-is-not-offered` (`:1682`);
  - `fn-auth-pass-accepts-only-a-checking-secret` (`:1933`).
- **The served lift exists only for POST.**
  `fn-served-dispatch-of-a-refused-post-leaves-the-wire-in-place`
  (`books/nntp-auth-invariants.lisp:158`) covers a refused POST.
  `fn-auth-step-pinned-agrees-with-auth-step-on-handled-command` (`:232`)
  bridges the two steps, but only when `(fn-auth-command ...)` is non-nil.
  No event uses it for the 480 gate or the 483 answer.

**Subject: not the function the host calls.** The host calls
`fn-auth-step-pinned`, through the chain above from
`host/owner-host.lisp:1240`. The 480 and 483 keystones are stated over the
sibling `fn-auth-step`, and nothing equates the two for the gate. PRF-031 is
"hosted" in `reach_check` only because of the `tools/run_owner.py:278`
docstring.

**Teeth: exist.** The cell's "no teeth book for the auth chain" is stale.
`tests/acl2/nntp-auth-teeth-tests.lisp` has 49 `must-fail` and 240
`assert-event` in total:

- keystone 1 has a reachable witness (`:191-202`) and one `must-fail` per
  hypothesis, H1 to H7 (`:221, 256, 287, 318, 365, 409, 442`);
- the 483 keystone has G1 to G8 (`:523-784`);
- the greeting and advertisement theorems each have their own drops
  (`:843-995`).

The book is green (`e16a7dd3`, certify-20260924T105922Z-3604838, persvati).

**Registry.**

- The cell's "PRF-031 carries zero events" is stale. PRF-031 has 13 events
  and status `in-progress`, and cites no manifest. Every one of its events is
  certified at `certify-20260924T105650Z-3582222`, "not cited".
- PRF-039 has 4 events and the same state.

**Red books:** `books/owner-tls-prefix` is green (`3c915508`,
certify-20260924T105922Z-3604838), as is `served-tls-prefix` (`0a50713c`).

**Native observation.**

- `tools/node_probe.py:101` checks for a 483 before TLS. It ran against the
  `da5fd8cb` image from the LAN and every assertion held: 483, TLS 1.3,
  STARTTLS withdrawn, then 281, then POST
  (`evidence/node-hbox-da5fd8cb-2026-09-23.md:43-50`).
- `tests/test_native_starttls.py:223` also checks for a 483 (assertion at `:255`).
- No run sends a restricted command before the login. The probe's `GROUP`
  comes after 281 (`node_probe.py:151`), and `V0-AUTH-GATED`
  (`tools/v0_matrix.py:346`) covers POST only.
- Did any of this run on `1a9dd747`? No.

**Packet.**
1. Proof lane (Opus, about 1 day): add `fn-served-dispatch-of-a-gated-command-is-480` to
   `books/nntp-auth-invariants.lisp`:
   `(implies (and (fn-served-connp conn) (not (fn-auth-session-handshakingp S)) (fn-auth-config-requiredp (fn-auth-session-config S)) (not (fn-auth-session-subject S)) (equal event (list :command line)) (fn-nntp-command-inputp line) (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)) (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line)))) (and (equal (fn-served-conn-session (fn-served-result-conn (fn-served-dispatch conn event))) S) (equal (fn-served-conn-wire ...) (fn-served-conn-wire conn)) (equal (fn-served-result-effects (fn-served-dispatch conn event)) (fn-auth-single S "480 authentication required"))))`,
   where `S` is `(fn-served-conn-session conn)`. It needs one lemma: that
   `fn-auth-command` is non-nil on the gate, which instantiates `:232`. Add a
   483 sibling the same way. The chain from `fn-served-dispatch` to
   `fn-own-read` is K1 (`fn-own-reader-sees-pinned-prefix-replay`,
   `owner-invariants.lisp:1560`). From `fn-own-read` to the host, the chain is
   `fn-ocfg-read-tls-prefix-is-full-read`.
2. Teeth: lift H1 to H7 and G1 to G8 into `nntp-auth-teeth-tests.lisp` at
   the `fn-served-conn` level. Reuse the existing values.
3. Registry: cite `certify-20260924T105650Z-3582222` on PRF-031 and PRF-039,
   and add the two served events.
4. Native lane (small): extend `node_probe.py` with GROUP before login (480,
   and nothing is performed). Run it with the 483-then-login sequence on the
   next image.

| P1 | theorem: exists, `fn-auth-gated-command-is-refused-and-not-performed` (nntp-auth.lisp:1613) but over `fn-auth-step`; served-level 480/483 missing | subject: none (host calls `fn-auth-step-pinned` via owner-host.lisp:1240; sibling bridge at nntp-auth-invariants.lisp:232 is not instantiated) | teeth: nntp-auth-teeth-tests, 49 must-fail / 240 assert-event, H1 to H7 and G1 to G8 each covered | observed: node_probe 483-then-login on da5fd8cb; 480-before-login never; ran on 1a9dd747? n | obstruction: none (one served-level lemma plus registry citation) |

---

## P2: 240 only after the consumed completion

**Theorems.**

- **The Store keystone exists.**
  `fn-sn-new-success-requires-actual-matching-durable-node-completion` is at
  `books/store-node-invariants.lisp:737`. If `fn-sn-finish` changed the
  success list, then the completion was enabled. On the acceptance arm, the
  record binds, the node equals `fn-node-complete ... :durable`, and the
  record is committed. It is PRF-007's event, with teeth in
  `tests/acl2/store-node-teeth-tests.lisp:99`.
- **T5's named theorem does not exist.** `fn-own-240-follows-consumed-completion`
  has no match in `books/`.
- **Its substance exists under another name.**
  `fn-own-durable-reply-names-a-durable-record` (`books/owner-invariants.lisp:2393`)
  states: if `(fn-own-relation o)` holds and `(car (fn-own-outcome o id word))`
  equals the served `:durable` reply, then
  - something is in flight for `id`;
  - `word` is `:durable`;
  - `(< (fn-own-sub-mark inflight) (len (fn-own-ledger o)))`;
  - `(fn-sf-record-has-pairp (car (last (fn-own-ledger o))) (fn-sf-records ...))`.

  `fn-own-outcome-completion` (`books/owner.lisp:1955`) projects `:durable`
  from ledger evidence, never from the host word alone.

**Subject.** The theorem is over `fn-own-outcome`, which the host calls at
`host/owner-host.lisp:1034`, so this half is right. Two gaps remain:

- **What the theorem identifies.** It shows that some completion was
  consumed after the take and that the newest ledger pair names a durable
  record. It does not show that the record is this submission's Message-ID
  or payload.
- **A host twin.** `fn-owner-finish` (`host/owner-host.lisp:495-507`) and
  `fn-store-sn-finish` (`host/store-node-host.lisp:552-557`) decide
  `:durable` or `:fault` in host code, by comparing phases and the ledger or
  success length. The model re-checks the ledger for a 240. A wrong `:fault`,
  however, becomes an uncertain 441 without any model decision.

**Refusal and uncertain lines.**

- The uncertain line is `"441 ... uncertain, do not repost"`
  (`books/nntp-post.lisp:282`), and `fn-own-outcome-completion-is-one-of-four`
  is at `owner-invariants.lisp:2068`.
- **"441 refused names its reason" holds only for injection refusals**
  (`nntp-post.lisp:154-165`). The Store refusal is the generic "the article
  was refused" (`:280`). `:conflict` becomes `:refused` in raw Lisp
  (`host/native/owner.lisp:712-713, 771-772`), and `:duplicate` becomes
  `:refused` in the model (`owner.lisp:1964`).

**Teeth.**

- The reachable witness `*own-240*` is at `tests/acl2/owner-tests.lisp:760-765`.
- Both hypotheses have violating values, as `assert-event`s at `:1467-1520`:
  a forged ledger without `fn-own-relation`, and a taken submission without
  the 240 equality.
- There are 0 `must-fail` for this theorem.

**Registry.** No PRF row cites `fn-own-durable-reply-names-a-durable-record`
(it has no match in `planning/proofs.json`). NNT-005 is `specified`, and its
note still names T5.

**Red books:** `owner` (`07dd772b`), `owner-invariants` (`9c229a82`) and
`nntp-post` (`3e525769`) are all green (certify-20260924T105650Z-3582222).

**Native observation.**

- The cell's "run in no image since the 32 KiB repair" is stale. The 16-cut
  campaign ran twice on `da5fd8cb` with byte-identical tables
  (`evidence/campaign-da5fd8cb-2026-09-23.md`).
- `test_native_crash_model` and `test_native_served_crash_model` passed on
  `daa6c15e` (`evidence/t2-native-daa6c15e-2026-09-23.md:41-42`).
- On `1a9dd747`, only the two-Store join's `a-accepted` cut ran. It is a
  restart after acceptance with stable bytes, not the POST cut table.
- Did the POST cut table run on `1a9dd747`? No.

**Packet.**
1. Proof lane (Opus, 1 to 2 days): add `fn-own-240-names-this-submissions-record`
   over `fn-own-outcome`, with the hypotheses of `:2393`. Its conclusion: the
   newest ledger pair's record is an article record whose Message-ID and
   payload are those of `(fn-served-submission-... (fn-own-sub-... (fn-own-inflight o)))`.
   Also add the converse, `fn-own-consumed-completion-renders-240`: with
   `word` equal to `:durable` and the mark below the ledger length, the reply
   is the 240. Rename or alias the pair to T5's name, or amend T5's text.
2. Move the host twin: make `fn-owner-finish` return the word the model
   computes (a book function `fn-own-finish-word o o'`) instead of comparing
   phases in host code. Do the same for `fn-store-sn-finish`.
3. Teeth: add a `must-fail` per hypothesis next to the existing value drops.
4. Registry: add a PRF row, or events under PRF-007 or PRF-033, and move
   NNT-005 to `implemented` once the step below has run.
5. Native lane: `native_operator_campaign` together with
   `test_native_crash_model` and `test_native_served_crash_model` on the next
   image.
6. **Decision for ember (small):** should a Store refusal name its reason
   (duplicate or conflict) on the wire? Otherwise drop the phrase from P2.

| P2 | theorem: exists under another name, `fn-own-durable-reply-names-a-durable-record` (owner-invariants.lisp:2393); `fn-own-240-follows-consumed-completion` missing; this-submission identity missing | subject: host/owner-host.lisp:1034 (`fn-own-outcome`); durable word from host twin owner-host.lisp:500-507 | teeth: owner-tests.lisp witness :760, 2 hypotheses with value drops, 0 must-fail | observed: 16-cut campaign on da5fd8cb, crash-model tests on daa6c15e; ran on 1a9dd747? n | obstruction: host twin for the durable word; wording decision on refusal reasons |

---

## P3: reading resumes, the pinned view and NEWNEWS

**Local numbers never reused.** OBJ-005 is `implemented`. PRF-002's events
include `fn-allocate-at-watermark`, `fn-watermark-does-not-conflict` and
`fn-state-has-fresh-local-numbers`. The row is `in-progress`, and OBJ-005's
note records that H1 and H2 are still droppable.

**Pinned view.**

- **T6's named theorem does not exist.**
  `fn-own-read-of-a-pinned-reader-is-stable-under-another-connections-complete`
  has no match.
- **The pieces exist:**
  - `fn-own-read-is-served-step-on-pinned-prefix-after-any-trace` (`owner-invariants.lisp:1521`)
    and `fn-own-reader-sees-pinned-prefix-replay-after-any-trace` (`:1592`):
    a read is `fn-served-step` over the replay of the first `version`
    records;
  - `fn-own-pinned-prefix-survives-any-trace` (`:1765`): that prefix is
    unchanged after any `fn-own-run`;
  - `fn-own-outcome-touches-only-its-connection` (`:1996`): another
    connection's record is `EQUAL` after an outcome.
- **The subject gap.** The "after any trace" theorems are over `fn-own-run`,
  that is, `fn-own-step`. The host drives `fn-own-outcome` (`:1034`),
  `fn-opc-prepare` (`:340`) and `fn-ocl-complete` plus `fn-own-configure`
  (`:276`, `:284`) outside `fn-own-step`. Relation preservation exists for
  some of these separately: `fn-own-outcome-preserves-relation` (`:1370`),
  `fn-own-configure-preserves-relation` (`:1128`) and
  `fn-ocl-complete-preserves-full-historical-relation` (`config-owner-live.lisp:457`).
  No trace theorem is stated over the host's event set.
- **A caveat for the stability claim.** The read also depends on
  `(fn-own-clock final)`, so exact stability holds only across events that do
  not observe the clock.

**NEWNEWS.**

- The cell's "PRF-052 over the injector's Injection-Date" is stale. PRF-052
  is `certified`, over the acceptance stamp.
  `fn-nntp-newnews-scan-is-the-acceptance-filter` has an independent
  specification, and `fn-nntp-newnews-scan-reads-no-payload` is proved.
- Its subject equation, `fn-nntp-step-dispatches-newnews-to-the-newnews-response`
  (`nntp-newnews.lisp:204`), is over `fn-nntp-step`. The served path is
  `fn-nntp-step-pinned` (`nntp.lisp:243`), which falls through
  `fn-nntp-command-pinned` to `fn-nntp-archive-command` and reaches the same
  `fn-nntp-newnews-response` (`nntp.lisp:127`). No pinned equation exists.
- `nntp-newnews-tests` has 12 `must-fail`.
- The six `nntp-newnews` events are certified at
  certify-20260924T030421Z-3524851, but that manifest is "not cited".
- The store now keeps an acceptance stamp (T2a landed), so the cell's "the
  store keeps no acceptance stamp" is stale.

**Red books:** `books/owner` is green (`07dd772b`), and so is `nntp-newnews`
(`aaf2a3f5`).

**Native observation.**

- `V0-POST-CONCURRENT` (`tools/v0_matrix.py:382`, driver `:1376-1401`)
  asserts only that the watcher is live: `ok` is WATCHER MID 211 and COMMIT
  240. It records WATCHER AFTER but never compares it with WATCHER BEFORE,
  so no run checks that the view is kept.
- NEWNEWS over the stamp ran on the 329 image
  (`evidence/t2b-newnews-migration-329-2026-09-23.md`).
- NNT-006's note still says "T6".
- Did any of this run on `1a9dd747`? No.

**Packet.**
1. Proof lane (Opus, 1.5 to 2 days; it shares `owner-invariants` with the P2
   and P5 lanes): add `fn-own-read-of-a-pinned-reader-is-stable-under-another-connections-post`.
   Hypotheses: `(fn-own-relation o)`, a connection `id` distinct from the
   in-flight `sub-id`, and `o2` equal to
   `(cdr (fn-own-outcome (fn-own-complete o) sub-id :durable))`.
   Conclusion: `(car (fn-own-read o2 id octets))` equals
   `(car (fn-own-read o id octets))`. It follows from the three pieces above
   plus a `fn-own-complete-keeps-every-connection` lemma. Also state the
   relation over the host's transition set, meaning `fn-own-outcome`,
   `fn-opc-prepare`, `fn-ocl-complete` then `fn-own-configure`, and
   `fn-ocfg-step`, or give each its subject equation.
2. Add `fn-nntp-step-pinned-dispatches-newnews-to-the-newnews-response`.
3. Teeth: a `must-fail` with `id` equal to the poster (repinned by
   `fn-own-durable-outcome-repins-the-poster`, `:2331`) and one without the
   relation.
4. Registry: cite certify-20260924T030421Z-3524851 on PRF-052, add the T6
   event, and rewrite NNT-006's note.
5. Native lane: make `concurrent()` assert WATCHER AFTER equal to WATCHER
   BEFORE, and that STAT of the new number is 423 on the watcher. Run it on
   the next image.

| P3 | theorem: missing, `fn-own-read-of-a-pinned-reader-is-stable-under-another-connections-complete` (pieces exist at owner-invariants.lisp:1521, 1765, 1996); NEWNEWS PRF-052 certified | subject: host/owner-host.lisp:1240, reaching `fn-own-read` via owner-tls-prefix.lisp:91; trace theorems over `fn-own-run`, not the host's event set | teeth: none for T6; nntp-newnews-tests 12 must-fail | observed: V0-POST-CONCURRENT checks liveness only; ran on 1a9dd747? n | obstruction: none; trace theorem must cover the host's direct `fn-own-outcome`/`fn-ocl-complete` calls |

---

## P4: one owner decides duplicate versus conflict

**This P is substantially done; the cell is stale.**

- **Theorem.** `fn-sn-existing-action` is defined at `books/store-node.lisp:65`
  (guard `t`, with no whole-store recognizer). The three direct case
  equations are in `books/store-node-existing-invariants.lisp`:
  `-is-duplicate-iff-byte-identical-by-definition` (`:6`),
  `-is-conflict-iff-held-binding-differs-by-definition` (`:17`) and
  `-is-missing-iff-no-held-binding-by-definition` (`:28`). They are
  correctly named `-by-definition` and are not registry events.
- **Subject: the called function.** The host calls it at
  `host/store-node-host.lisp:456` and `:577`, and at
  `host/owner-host.lisp:324` and `:1166`.
- **The host twin is gone.** `fn-store-article-match` has no match in
  `host/`, `books/`, `tools/` or `tests/`.
- **Remaining raw-Lisp renaming.** `host/native/owner.lisp:712-713` and
  `:771-772` map `:conflict` to `:refused` in raw Lisp. This is a renaming,
  not a comparison, but it erases the distinction before the model sees it.
- **Teeth.** `tests/acl2/store-node-existing-tests.lisp` has 10
  `assert-event` and 5 `must-fail`: payload alone, groups alone, binding
  alone, and missing-is-not-conflict. It is green (`44f506ff`,
  certify-20260924T094824Z-1155517, hbox). `store-node` is green (`3b1567f7`).
- **Registry.** OBJ-002 is `implemented`, and its note records that T3
  removed the twin. NNT-005's note: "the owner-to-Store retry composition is
  not yet a theorem."

**Native observation.**

- T3 landed on 2026-09-23 ([record](evidence/t3-store-existing-action-2026-09-23.md)).
  None of the image runs since then exercises a duplicate or a conflict:
  `daa6c15e`, `295bbe35`, `863c2141`, `1a9dd747`.
- [native-duplicate-outcome](evidence/native-duplicate-outcome-2026-09-22.md)
  predates T3.
- T3's text names `V0-OUT-REFUSED` as the witness. That row is "a lookup of
  an article the node does not hold exits 1" (`v0_matrix.py:297`). The
  duplicate-POST row is at `:372`.
- Did any of this run on `1a9dd747`? No.

**Packet.**
1. Native lane (small): the matrix duplicate-POST row (`v0_matrix.py:372`)
   and a conflicting re-POST of the same Message-ID with different bytes,
   run on the next image and recorded.
2. Optional proof, for v0 honesty (Opus, about 1 day):
   `fn-own-operator-retry-is-duplicate-at-the-store`. It composes
   `fn-own-operator-retry-resubmits-the-stored-injection` (PRF-056) with
   `fn-sn-existing-action`. Its statement: over `fn-opc-prepare`'s state, a
   retry of stored octets answers `:duplicate`. This closes NNT-005's open
   composition sentence.
3. Correct T3's witness row name in the plan.

| P4 | theorem: exists, `fn-sn-existing-action-is-{duplicate,conflict,missing}-...-by-definition` (store-node-existing-invariants.lisp:6,17,28) | subject: store-node-host.lisp:456,577; owner-host.lisp:324,1166 | teeth: store-node-existing-tests, 5 must-fail / 10 assert-event | observed: none since T3; ran on 1a9dd747? n | obstruction: none (native run owed; conflict renamed to refused at host/native/owner.lisp:713) |

---

## P5: a host fault costs one connection, and sessions are bounded

**Theorems exist** in `books/owner-fault.lisp`, which has 11 `defthm`:

- `fn-own-fault-closes-the-faulted-connection` (`:128`);
- `fn-own-fault-keeps-every-other-connection` (`:138`):
  `(implies (not (equal other id)) (equal (fn-own-find-conn other (fn-own-conns (cdr (fn-own-fault o id)))) (fn-own-find-conn other (fn-own-conns o))))`;
- `-clears-the-faulted-submission`, `-keeps-another-connections-submission`,
  `-releases-the-faulted-transaction` and `-is-not-a-store-event`;
- `fn-own-fault-reply-is-not-a-post-outcome` (`:182`).

**Bound.** `fn-own-connections-bounded-after-any-trace`
(`owner-invariants.lisp:1836`, K4) states: under `(fn-own-relation o)`,
`(<= (len (fn-own-conns (fn-own-run o events))) (fn-own-max-conns o))`.
It is over `fn-own-run`, not the host's event set (see P3). No theorem says
that `fn-own-open` refuses at the bound. The witness `*own-full*`
(`owner-tests.lisp:521-527`) shows it only as a value.

**Subject.**

- The host calls `fn-ocfg-fault` (`host/owner-host.lisp:1273`), a
  definitional wrapper (`owner-config.lisp:542-548`). No named equation
  equates it to `fn-own-fault`.
- **The native scope is narrower than P5's sentence.** Only a
  connection-local fault continues the service:
  `fnn-owner-abandon-connection`, `host/native/owner.lisp:629-648`, which
  logs "service continues".
- A core or Store fault, or an OS or serious condition inside a shared owner
  action, calls `fn-owner-fault` and then **stops the whole service with
  exit 4** (`:563-564`, `:579-580`, `:588-589`). That is by design:
  ambiguous persistence is a recovery event. P5 must carry that
  qualification.

**Teeth.**

- There is no `tests/acl2/owner-fault-tests.lisp`, so the cell is still true.
- Witnesses are in `owner-tests.lisp:1540-1620`.
- Value drops exist for K2's `(not (equal other id))` and K3's `sub-id`
  hypothesis.
- There are 0 `must-fail` for any fault theorem.
- I found no violating value for `-releases-the-faulted-transaction`'s
  `(equal (fn-own-pending o) id)`, nor for the `(fn-own-inflight o)`
  hypotheses.

**Registry.**

- The cell's "PRF-040 carries zero events" is stale. PRF-040 has 6 events,
  status `in-progress`, and no cited manifest (`owner-fault` is certified at
  `7abaf319`, certify-20260924T105650Z-3582222).
- K-FAULT-5, `fn-own-fault-reply-is-not-a-post-outcome`, is called a
  keystone in PRF-040's note but is **not an event**.
- K4 is in no P5 row.
- HST-005 is `specified`.

**Native observation.**

- `tests/test_native_owner.py:246`
  (`test_local_handler_fault_uses_core_fault_and_preserves_other_clients`)
  expects the 403 at `:255`. Its last recorded run is
  `evidence/native-owner-fault-isolation-2026-09-21.md`, before every
  current image.
- No max-conns overflow runs on an image.
- Did any of this run on `1a9dd747`? No.

**Packet.**
1. Proof lane (Opus, about 1 day):
   - add `fn-ocfg-fault-is-own-fault`: car equal, and
     `(fn-ocfg-owner (cdr ...))` equal to `(cdr (fn-own-fault ...))`;
   - add `fn-own-open-at-the-bound-refuses`:
     `(implies (<= (nfix (fn-own-max-conns o)) (len (fn-own-conns o))) (equal (fn-own-open o acfg) (cons nil o)))`;
   - add `fn-ocfg-open-at-the-bound-refuses` over the host-called
     `fn-ocfg-open` (`owner-host.lisp:1218`).
2. Teeth: `tests/acl2/owner-fault-tests.lisp` with one `must-fail` per
   hypothesis. That is 1 for K2, 2 for clears, 2 for keeps-another and 1 for
   releases, plus the bound theorem's single hypothesis.
3. Registry: add K-FAULT-5 and K4 to PRF-040 and cite the manifest. Restate
   P5 and HST-005 as "a connection-local fault costs one connection; a Store,
   core or OS fault in the shared action fences the process (exit 4)".
4. Native lane: `test_native_owner` fault case and a (max-conns + 1)th
   connect on the next image.

| P5 | theorem: exists, `fn-own-fault-keeps-every-other-connection` (owner-fault.lisp:138) and K4 (owner-invariants.lisp:1836); open-at-bound refusal missing | subject: owner-host.lisp:1273 (`fn-ocfg-fault`, wrapper with no named equation); native: connection-local only (host/native/owner.lisp:629-648); shared-action faults stop the process (:563,:579,:588) | teeth: no owner-fault-tests; owner-tests.lisp:1540-1620 value drops for 2 of 6 hypotheses, 0 must-fail | observed: test_native_owner.py:246, last 2026-09-21; ran on 1a9dd747? n | obstruction: P5's sentence overclaims; needs the exit-4 qualification (design, not a gap) |

---

## P6: live reconfiguration

**Theorems exist** in `books/owner-config.lisp`: `fn-ocfg-no-reader-observes-a-half-change`
(`:1063`), `fn-ocfg-pin-is-stable-without-advance`, and
`fn-ocfg-crash-at-any-instant-recovers-the-live-generation`. The first states:

    (implies (fn-ocfg-staged (fn-ocfg-step oc (list :reconfigure other deltas)))
      (let* ((staged (fn-ocfg-step oc (list :reconfigure other deltas)))
             (published (fn-ocfg-step staged (list :complete))))
        (and (equal (fn-ocfg-owner published) (fn-ocfg-owner oc))
             (equal (fn-ocfg-pins published) (fn-ocfg-pins oc))
             (equal (fn-ocfg-config staged) (fn-ocfg-config oc))
             (equal (fn-ocfg-config published)
                    (fn-ocfg-published-config (fn-ocfg-config oc) (fn-ocfg-staged staged))))))

**Subject: split.**

- Staging is right. `host/owner-host.lisp:230-231` calls
  `fn-ocfg-reconfig-refusal`, then `fn-ocfg-step (:reconfigure ...)`.
- **Publication is not.** `fn-owner-reconfigure-complete` calls
  `fn-ocl-complete` (`:276`, `books/config-owner-live.lisp:39`) and then
  `fn-own-configure` (`:284`). It never calls `fn-ocfg-step (:complete)`.
- The headline's first conjunct, "owner unchanged", is false of
  `fn-ocl-complete`: it installs `fn-cpo-configure-durable`'s store, per
  `fn-ocl-complete-success-install-exact-store` (`:70`).
- The called function has its own pin and table facts:
  `fn-ocl-complete-keeps-existing-pins` (`:60`),
  `-keeps-existing-served-table` (`:65`),
  `-preserves-pinned-connection-histories` (`:252`) and
  `-preserves-full-historical-relation` (`:457`). No theorem equates it to
  `fn-ocfg-complete`, and none restates the headline over it.
- `tests/test_native_live_reconfiguration.py:110-117` checks textually that
  the host calls `fn-ocl-complete`.
- `fn-owner-config-deltas` (`owner-host.lisp:220-225`) builds deltas in host
  code. It is a two-case constructor, but a comment at `:217` says "ACL2
  constructs the delta".

**Stale cell claims.** PRF-028 has 8 events. Its text no longer says "no
host line calls" (checked). Status is `in-progress`, with no cited manifest
and no evidence. `native-admin` (`d9854f08`) and `native-operator`
(`bff90334`) are green.

**Teeth.** `tests/acl2/owner-config-tests.lisp` has witnesses for all three
headline theorems (`:237`, `:392`, `:456`). It has value-level violating
values per hypothesis: the half-change theorem's one hypothesis at `:422-426`.
It has 2 `must-fail`. `config-owner-live-tests` has 2 `must-fail`. Both are
green.

**Native observation.** `tests/test_native_live_reconfiguration.py`, 11
tests including `:235` (live `peer add` leaves a pinned reader unchanged),
passed on `295bbe35` (`evidence/native-t8-t10a-295bbe35-2026-09-23.md:54`).
T8 is DONE per §3. Did it run on `1a9dd747`? No.

**Packet.**
1. Proof lane (Opus, 1 to 1.5 days): restate the headline over what the
   host calls, as `fn-ocl-no-reader-observes-a-half-change`. Take
   `staged = (fn-ocfg-step oc (:reconfigure other deltas))` and
   `published = (fn-own-configure-at (fn-ocl-complete staged))`. Conclusion:
   for every `id` in `(fn-ocfg-pins oc)`, the connection record and
   `fn-ocfg-served` are unchanged, the pins are equal, and the live
   configuration is the old one or `fn-ocfg-published-config` of the whole
   record. Alternatively, prove `fn-ocl-complete` equals `fn-ocfg-complete`
   modulo the store component, and cite both.
2. Move `fn-owner-config-deltas` into `books/native-admin` or `owner-config`,
   or delete the comment's claim.
3. Registry: cite certify-20260924T105650Z-3582222 and
   certify-20260924T102224Z-3270826 on PRF-028, and add the `fn-ocl-*`
   events.
4. Native lane: rerun `test_native_live_reconfiguration` on the next image.
   T8b (a live group is served before restart) is a separate step.

| P6 | theorem: exists, `fn-ocfg-no-reader-observes-a-half-change` (owner-config.lisp:1063) but over `fn-ocfg-step (:complete)` | subject: staging owner-host.lisp:231 yes; publication owner-host.lisp:276,284 calls `fn-ocl-complete` then `fn-own-configure`, no equation | teeth: owner-config-tests witnesses and value drops, 2 must-fail; config-owner-live-tests 2 must-fail | observed: test_native_live_reconfiguration on 295bbe35; ran on 1a9dd747? n | obstruction: headline stated over a sibling of the called completion |

---

## Across P1 to P6

The six scoreboard rows are the last line of each section above.

**Lane estimate across P1 to P6:**

- **Proof lanes (Opus):** four, about 5 to 7 lane-days in total.
  - P1: served 480/483.
  - P2 with P3 and P5: these share `owner-invariants`, so one lane in
    sequence.
  - P6: the `fn-ocl` restatement.
  - P4's retry composition is optional.
- **Host lanes:** the P2 durable-word twin and the P6 delta constructor,
  both small.
- **Registry:** one pass, citing manifests on PRF-028, -031, -039, -040 and
  -052, and adding the new events.
- **Native-run lane:** one lane on the next image. It runs `node_probe`
  (extended), the cut campaign and crash tests, the amended
  `V0-POST-CONCURRENT`, duplicate and conflict POST, `test_native_owner`
  fault plus overflow, and `test_native_live_reconfiguration`.

**Decisions for ember:**

- the P2 refusal-reason wording;
- whether P5's sentence is restated with the exit-4 fence. That fence is the
  AGENTS rule on ambiguous persistence, not a defect.
