# LANEDUMP codex-liaison (lane/codex-burndown), 2026-10-01

Liaison: Opus (agent driving `codex exec -m gpt-6.1-sol`). Protocol:
build/coordinator/codex-protocol.md. Task files: build/codex/tNN-*/ (gitignored).
Runner: a0b78a011d3edc4ee. Scope: make-check burndown, TOOLS/DOCS/REGISTRY only.

## Tasks (DONE / AUDITED / REJECTED, Codex wall time, rounds)
- t01-secrets: AUDITED OK. Codex 90 s + 1 resume round (~60 s). Redacted 8 lines
  in compression-c10-all3-harvest/.../test_native_friends_accounts.log (it found
  line 40, a code the check did not flag, unprompted). The liaison's full-tree
  box run found the same codes in a duplicate file
  (operator-friends-6462-harvest-2026-09-29/friends_accounts.log); resumed with
  that; consistent placeholders; `git grep` of the four codes now empty.
  Commits 9308518e4, afb3659d0. Note: make-check-summary shows only the FIRST
  finding of a step: a TASK's ground truth must come from a full box run.
- MODEL: t01-t02 on gpt-6.1-sol; from t03 on gpt-6-astra (ember via coordinator).
- t02-registry (gpt-6.1-sol, 245 s, 1 round): B AUDITED OK (beec02488: retired-name
  exemption, replacement fn-bpnjc-contact-next verified at books/bp-node-job-cursor.lisp:328).
  C AUDITED OK (e927ef872: SUB-007 -> 5 families, SUB-008 -> 6, each with a per-family
  justification from the spec sections; liaison read them, plausible, no over-reach).
  A NOT DONE, CORRECTLY: the liaison's TASK said "line 937 only" in IN SCOPE after the
  liaison widened PART A to 4 lines; Codex stopped and reported the contradiction
  instead of guessing (also: the liaison's `grep -P` fallback does not exist on macOS;
  Codex used rg). Liaison error, not Codex's. Folded into t03 PART D.
- t03-cites (gpt-6-astra, 464 s, 1 round): 5 commits 9d6f62ce6..069091883. AUDITED (diff read
  line by line; full-tree box run pending at time of writing):
  A spec_cite: 7 of 15 corrected to real definitions with defining lines quoted
    (slash forms spelled out; fn-pix-decide-offer -> fn-peer-decide-offer;
    schema1 -> schema3 golden-octets theorem; fnn-bps-send-effect -> -next);
    7 left OPEN as planned names with `git log -S` evidence (no invention, no exemption);
    fn-recovery-profile-buffer stopped: it IS defined (defstobj inside a defmacro,
    books/recovery-profile-buffer.lisp:12) = a spec_cite_check false positive. Correct call.
  B coverage: 20 ids filed with per-id justification; generous (CNS-011 in 7 families)
    but within the file's "overlap allowed" rule. coverage check 0 problems.
  C FAQ: rewrapped; the long command line got a shell continuation, docs_check fold verified.
  D ascii: 4 comment lines in records-canonicality (book bytes change -> recert).
  E cite: generator header + book line 2 -> baseline-1.json (book bytes change -> recert).
  Codex flagged unrequested follow-ups honestly (encoding.md schema-1 prose; CNS-011's
  spec anchor missing). Scope respected on every file.
- t04-logsize (gpt-6-astra): round 1 (33 s) STOPPED on two liaison contradictions (the
  acceptance probe file vs "touch nothing under planning/"; REPORT.md vs "three new files
  only"); round 2 after clarification (259 s): ed9730ac4 tools/evidence_size_check.py +
  baseline (272 grandfathered logs) + unit test + 5 Makefile lines. AUDITED: code read in
  full, matches the spec; liaison reran tests OK and the tool: 3586 raw logs, 0 refused,
  272 baselined, 0 stale. Lesson: Astra is literal about scope; write "tracked files" and
  name scratch exceptions explicitly.

## Reviews (range, raised / confirmed / rejected)
- r01 served-certify 896c48c16...8f73a444f (deflate-pool served change), gpt-6-astra 168 s:
  raised 0 findings, 6 questions answered with quoted lines; liaison spot-checked Q3/Q6
  claims against the source (true). Liaison-derived nit from Codex's Q3 note: the full
  pooled=unpooled answer equality (fn-zpl-decode-bufs-is-pzd) is LOCAL; the public keystone
  equates only the tag. Sent to main. Usefulness: thorough confirmation, no new bug.
- r02 def-carried 896c48c16...30351838a (generator + :raw-with (:carried) + interface_emit),
  gpt-6-astra 213 s: raised 7 (3 bug, 4 claim-gap), CONFIRMED 7, rejected 0. Liaison had
  independently spotted F1 (line 473 `(and writers ...)`) while Codex ran; Codex found it
  too plus F2 (composed-term theorem bound to a raw entry) which the liaison had not. Every
  finding came with file:line, quoted lines and a concrete construction. High value.
  OUTCOME: the coordinator verified F2 independently and HELD def-carried from dev; all 7
  sent to the lane; r01's keystone-strength nit also confirmed and sent to served-certify.
  This is the value ember wanted from Codex reviews: a generator that would have let a raw
  served entry cite a theorem about a different term was stopped before landing.
  TODO: re-review def-carried's next READY (r03).
- t05-macro-defs (gpt-6-astra, 157 s, 1 round): f4c64ae40 spec_cite_check recognizes a
  literal defstobj/defun/defthm in a backquoted defmacro body when the same book invokes the
  macro at top level; unit test with the positive case and both negative cases. AUDITED:
  diff read; tree-wide effect exactly 1 new name (fn-recovery-profile-buffer); tests pass but
  the tree test (7 parked planned names, coordinator: leave them).
- (liaison, not Codex) evidence_manifests: cf8804ae3. The tool's own harvest over hbox
  /tank/fn/scratch ran 30 min and was stopped; searched both boxes by exact run id instead
  (found 20 on persvati fn-gates/*), harvested them, `sync --add --record-lost`: LOST.txt
  181 -> 250 (the Codex-era runs whose build/ dirs are gone). check: exit 0. Manifests only.
- r03 recovery-refinement 896c48c16...2d1b10ed7, gpt-6-astra (~10 min): raised 6
  claim-gaps, CONFIRMED 6 (liaison verified F1 no host caller of fn-rr-open, F2 encapsulate
  admits a NIL full-open, F6 SIGKILL inside the batch-write loops; F3-F5 by the cited lines),
  rejected 0. Notably honest: Codex separated "theorem false" (none) from "claim too strong"
  and gave counter-models satisfying the full antecedent. Sent to main.
- (liaison) cf8804ae3 pushed with t04/t05; box: evidence_size_check 0, spec_cite 7 parked,
  secrets 0.
- t07-next-id (gpt-6-astra, ~25 min, 1 round): 3ac3f7757. Profiled: the "2 minutes" did NOT
  reproduce on the laptop (6 s; phases: tree grep 4.5 s, 94 branch diffs 3.4 s, 153 worktree
  diffs 1.9 s, 251 git processes). Added a validated scan cache (key = index entries + every
  tracked file's stat + git config/attributes/replace refs; allocation never cached; scan
  outside the lock, decide inside as before) and an 8-thread concurrent-claim test.
  AUDITED: diff read in full; tests OK (13); liaison timing cold 13.0 s, warm 2.35 s. Real
  ledger untouched. Duplicate-claim cause not found in code (Codex checked every path).
  Verdict: correct but elaborate (~150 lines) for a 6 s -> 2 s win; the lane's 2-minute
  figure needs its own context (box? load?).
- LIAISON ERROR: cf8804ae3 said it carried LOST.txt but LOST.txt was left unstaged; Codex
  noticed and reported "not part of this task" without touching it; fixed in dbe313f98.
- r05 msgid-linear da0688560 (gpt-6-astra, 166 s): raised 2 claim-gaps (teeth), confirmed 2;
  the four algorithmic questions (orphaned overflow, Litwin off-by-one at S and N->2N, 2-page
  bound, refusal vs absent) answered CLEAN with quoted evidence. Sent to main.
- PARALLEL from here: r04 generators, r06 resource-ledger, r07 page-word, t08 umbrella diff
  (codex-regen) running concurrently (5 sessions peak).
- t08-umbrella-diff (codex-regen, gpt-6-astra, report only): world.py render() vs committed:
  49 lines missing, 0 committed-only, 0 reorder; each traced to the commit that added a build
  input without regenerating. Recommendation regenerate-as-is; sent to main. Clean tree after.
- r06 resource-ledger 3dcaebc47 (gpt-6-astra): raised 8 (2 bug, 5 claim-gap, 1 nit), CONFIRMED
  8 (liaison verified exec book has 0 defthm, the saturating store, the missing test root).
  Most valuable: the slot-reuse ABA settle and the non-revoking destroy. Sent to main.
- r04 generators ba67b814b (gpt-6-astra): raised 4 (3 bug, 1 teeth), CONFIRMED 4 (liaison
  verified the quote-blind fn-dl-subst and ledger.py's invented :sum/:into bridge
  statements). Clean on the asked-for soundness worries (attachment trap refused, no skipped
  obligations, pilots not weaker). Sent to main; the def-loop conversion stream waits.
- t08 rerun: coordinator says re-run after stage 0 lands; then propose a fast check
  `world.py render == committed`.

- r07 page-word aa338ba4a (gpt-6-astra): raised 2 claim-gaps, CONFIRMED 2 (liaison verified
  the new fn-pgs-page-words-u64 constraint absent from the old encapsulate: a strictly
  stronger trust assumption under prose saying "the SAME assumption"). Sent to main.

## Liaison-2 log (codex-liaison-2, Opus, from 2026-10-01 ~07:00)
- t06 cert: the first box run failed for the liaison's reason (certify_books without --incremental: the
  parents were never roots, "no certificate on file"); rerun --incremental -> CERT 0
  (certify-20261001T110426Z-2824301). READY lane/codex-burndown 0363e9ef6.
- t11-pagefix (audited by liaison-1): liaison-2 certified on hbox (assumptions + history-records-disk-tests
  closure, CERT 0, certify-20261001T110322Z-2822986), merged dev (generated-file conflicts resolved by
  regenerating ledger + current view on persvati, both --check 0). READY lane/codex-pagefix a88089666
  superseding aa338ba4a.
- t13-program-gone (gpt-6-astra, 392 s, 1 round): 39d26761e removes exactly the 21 stale program names;
  AUDITED: liaison diffed removed set == depth_check's stale "program" lines at the head (24 stale lines
  total: the other 3 are "append"->"bounded" rows, correctly left). READY lane/codex-regen 335c676a5.
- t10-genfix (audited by liaison-1 at 7899f4547; liaison-2 read the 4 diffs): merged dev, ledger
  regenerated (persvati --check 0, DefLoopBridgeTests 4 OK), hbox cert of the two test books running.
  Nit: the non-stobj :into must-fail is :unchecked (ACL2's own refusal, labelled).
- r10 recovery-refinement 12ea7e0a3 RE-REVIEW (gpt-6-astra): raised 4 (1 nit, 3 claim-gap), CONFIRMED 4:
  prose still says the store discharges the third constraint (store book unadmitted); removal witnesses
  assert no retained hypotheses; PRF-1222 targets the table estimate but the staged file is image region
  + stream (fn-his-file-octets) and fn-sct-encode is undefined; PRF-1223 registers r03-F6 without a model
  cut. Answer to the coordinator: the new constraint is non-vacuous and excludes a successful
  record-dropping open, but an always-refusing open still satisfies it (by design). Sent to main.
- r11 msgid-linear-hash d47156da4 (gpt-6-astra): raised 4 (1 bug, 3 claim-gap), CONFIRMED 4; all four
  algorithmic asks CLEAN (60-bit tag: completeness PROVED; flag bit and fixnum bounds hold). Bug:
  fn-mlh-put accepts the reserved tag 0 (latent: real callers pass posp tags). Coordinator: d47156da4
  lands; fixes as t15 (lane/codex-msgidfix).
- r12 figure-and-contract b224e8a69 (gpt-6-astra): raised 3 claim-gap, CONFIRMED 3 (A-SBCL-INTERNALS prose
  only; M10 "allocation-epoch outside the image" false via build.lisp:185 include chain; M9 per-miss thread
  fallback nonexistent); asks clean (no fn-rov writer left; 5 terms traced to allocations; no hypothesis
  added). Plus a pre-existing gate-before-producer on the start path (runtime bootstrap with a NIL
  compiled table) -- coordinator: stage 0 unwires it. b224e8a69 lands; doc fixes queued as t16 after
  stage 0.
- t14-dcfix2 (liaison-1's launch): Codex STOPPED correctly on the TCPCL value-state pilot (20
  (fn-tcl-result-session _) transitions). Liaison-2 decided the value-state rule (pure-selector SEL:
  non-recursive, logical body car/cdr/nth/mv-nth only) -> t14b-dcfix3 running.
- t13 READY sent; t10-genfix READY lane/codex-genfix ce9932b05 (hbox cert of def-loop/def-representation
  tests CERT 0, certify-20261001T113059Z-2852386) + lane/codex-rrnit b444981e0 (liaison, comments only: r13 F1).
- r13 recovery-refinement cc63cdcd9 follow-up (gpt-6-astra): raised 1 nit, CONFIRMED 1 (residual "discharges"
  prose); r10's F2-F4 verified CLOSED; PRF-1214 fn-rrc-relp a genuine, non-vacuous weakening. Fixed by the
  liaison in codex-rrnit.
- t15-msgidfix (gpt-6-astra, 532 s): 4 commits (posp tag guard; header NEXT; complete-antecedent + removal
  witnesses). Codex could not REPL-admit (60 s dependency limit) and COMMITTED UNADMITTED TEETH; hbox cert:
  both test books FAIL (assert-event over an mv-returning split; ground defthm stuck on HIDE). Round 2
  (resume) running with --load-limit 0. Lesson: require "admitted to the end" before commit in the TASK.
- t14b-dcfix3 (gpt-6-astra, 497 s): the one validator (stobj + value-selector rule) 04299d899; REPL-admitted
  4 books; hbox cert of def-carried-tests + tcpcl-session-carried at the dev merge CERT 0.
- r14 def-carried fresh re-review of 04299d899: raised 1 bug, CONFIRMED 1: :concludes bridges head-only checked
  and fed to definterface's occurrence lint (4th hole of the same class). All pattern paths clean.
  t14c (syntactic bridge fix) committed e3ad96de4 then STOPPED by the liaison when the coordinator changed the
  approach: def-carried GENERATES the D40 statements; :raw-with (:carried) resolves only to generated names.
  def-carried design now owned by Fable deputy a673cde35dfbc7eaf (sent full state); r15 on its sha.
- r12 / r11 cleared to land by the coordinator (b224e8a69, d47156da4); t16 figure-docs queued after stage 0:
  build/coordinator/queue/codex-t16-figure-docs-AFTER-STAGE0.md.
- t17-defloop-1 (gpt-6-astra, 461 s): 10 of 24 hand twins converted in 7 books (-295 lines), 14 left with
  exact reasons (generator gaps: :keep branch order, LET vs LET*, separate loop guard, read-only stobj
  formals, posp/atom take base, per-element append, true-list-fix acc). hbox: 4 books certify, 3 blocked
  behind store-reclaim-pack (red at dev, untouched). READY lane/codex-defloop 7f20b3270.
- r16 served-certify 48bbd31a5: 6 asks CLEAN (index fix on the host-called reopen; 13 installer paths
  inventoried), 1 comment nit (store-finalize-incremental.lisp:243-245). CLEARED to the runner.
- t15 round 2 (resume, 523 s): 7685be9ec, both test books admitted (Codex used proof_repl --host hbox: a
  protocol deviation, the result useful); hbox CERT 0. READY lane/codex-msgidfix 075adef14.
- t19-reach (gpt-6-astra): 96 per-theorem dispositions, reach --strict 96 -> 0; 2 MISSING JOINs (PRF-1131
  window codec tick vs fnn-pzd-decode; PRF-201 keyed clear). READY lane/codex-reach 022d7d66d.
- consumer-account-auth-tests: found on codex/consumer-remainder (+ its include adoption-tests), committed
  verbatim by the liaison: READY lane/codex-authtests 62e434e33 (auth/adoption/ingress certify; the rest
  blocked behind nntp-index-runtime, a stage-0 root).
- LIAISON ERROR: r17 launched with a bare `&` (the process survived, detached). Use run_in_background only.


## Liaison-3 log (codex-liaison-3, Opus, a737641d2e4257880)
- r17 paged-catalog-gen a5d1f2c4a (launched by liaison-2): raised 1 claim-gap, CONFIRMED 1 (NAME-clear has no
  teeth for adt-corr-of-clear-c: tests only observe count after clear). Asks Q1-Q3 clean (TP rule
  adt-nth-of-all-elt-p-natp valid, free ct bound by type-alist matching). Plus a PRE-EXISTING FALSE theorem,
  verified: proto/adt-consumer-position.lisp:65 fn-cp-entryp-is-cpent-record (8-field schema) vs
  consumer-position.lisp:338 (10-field remote entries); counter-model e='(:entry (1) (2) (3) 0 0 1 0 ((4)) (5)).
  Sent to main, the deputy a673cde35 (owner) and paged-catalog-2. Deputy fixed both on deputy1/generators
  ee31fe17d (reviewed as r19).
- r19 deputy1/generators ee31fe17d (launched by liaison-2): raised 2 (1 bug, 1 claim-gap), CONFIRMED 2: F1 clear's
  RESIZE-/UPDATE- names built from a STRING base by adt-sym (proto/adt.lisp:223, 379-381) intern in ACL2, so a
  foreign-package instance's clear calls ACL2::RESIZE-... (latent: every fn instance is ACL2-package); F2 no
  single-hypothesis removal witnesses for adt-corr-of-clear-c. Q2 answered the coordinator's question: the
  8-field hypothesis is NOT vacuous for host-stored local entries (fn-cp-entry, 8 fields); remote entries (10)
  are excluded and the book says so; no registry/spec claim exists. Coordinator: ee31fe17d lands; fix-forward
  = t22 (lane/codex-genfix2).
- r18 deputy1/resource-ledger 0903f9d2b (launched by liaison-2): raised 3 (2 bug, 1 claim-gap), CONFIRMED 3 (liaison
  read fn-rl-install/fn-rl-resize-all): F1 install mutates (resize, budget store, baseline draw) before the
  reserve check and returns the partial ledger with the refusal; F2 install has no freshness guard, so a
  shrink-then-regrow reinstall zeroes generations and an OLD settle token releases a NEW draw (5-step
  construction, all guards hold); F3 relation teeth for fn-rv-prs-gate-is-a-funded-root still absent. Logical
  ABA, tree one-level rule, arbitrary-run revocation: clean. r06's 8: 4 closed, 3 closed-by-scope, F7 half open.
  Coordinator: 0903f9d2b lands (no served caller); fix-forward = t23 (lane/codex-rlfix) incl. the install
  exec<->logic correspondence theorem.
- t18-defloop-gen AUDITED: def-loop.lisp diff read in full (one library induction per new shape, instances by
  :functional-instance only; :cons-first/:default paths emit the old forms; read-only stobjs checked after
  translate); ledger.py mirror read. Merged origin/dev, hbox certify-20261001T124501Z-2924938: 6 of 7 roots
  certify; nntp-reader-compat blocked behind nntp-index-runtime (stage 0). DefLoopBridgeTests 11 OK; ledger/cv
  --check 0, regen committed. READY lane/codex-defloop-gen 747f17594 (runner: batch 7).
- t21-defloop-2 LAUNCHED (lane/codex-defloop-2 from 747f17594): 29 hand twins in 13 low-fan-in books outside
  stage 0/catalog/msgid/page-word/reclaim; generator frozen for the batch.
- t22-genfix2 (gpt-6-astra, ~5 min, 1 round): 8e39d3776 = r19 F1 (adt-sym-pre at the 4 sites) + package-regression
  expansion test + F2 removal witnesses (true-listp one labelled corrupted-state, checked by thm since
  UPDATE-NTH's guard rejects the improper list). DUPLICATE WORK: the deputy fixed F1 in parallel (5f0e0755e,
  adt.lisp byte-identical to Codex's). Liaison carried the TEST FILE ONLY onto 5f0e0755e: READY
  lane/codex-genfix3 7a0946d0e (hbox certify-20261001T130048Z-2943497 CERT 0; runner batch 8).
  Lesson: before launching a fix-forward, ask the owner whether it is already fixing.
- t23-rlfix STOPPED after ~10 min (deputy fixed r18 F1/F2 first, ba8d2ff8c); its 3 proof_repl sessions were
  orphaned by the stop and stopped by the liaison (proof_repl stop). Relaunched narrowed as t23b.
- t23b-rlfix2 (lane/codex-rlfix2 from ba8d2ff8c): PART B AUDITED OK e43a4144a (defkeystone relation teeth;
  4 labelled corrupted dotted-tail removals for the funded-root gate; fn-rv-prs-below's two shape hypotheses
  shown possibly REDUNDANT, recorded as evidence only, not removed). PART C STOPPED TWICE, correctly, on real
  exec/logic divergences in the deputy's fn-rl-install, each with an ACL2 Q.E.D. counterexample:
  (1) baseline nil: exec :invalid-install vs logic :invalid-draw (word); (2) nslots 2^32: logic ACCEPTS, exec
  refuses (accept/refuse). Liaison decisions: logic is the spec, refusal words = logical words; exec-only
  refusals exactly :already-installed and :unrepresentable-profile (budget words OR the u32 slot count, one
  named representability predicate). Round 3 running.
- r20 paged-catalog 78d3f5c52 (stage-3 core; coordinator's 4 asks: attach soundness / codec totality+escapes /
  pool bounds+freeing / split preservation) LAUNCHED.
- t20-reach-export AUDITED: rule read (same stobj, same relation, direct exec call edge, literal :use; no name
  similarity, no {preserved}); PRF-201 verified in source (fn-cat$c-clear-keyed calls fn-cat$c-clear-w, the
  fn-cat-clear exec). persvati reach --strict 0, --explain names the link + host chain; hbox unit 47/48: the 1
  red is SharedGraphTests.test_a_macro_body_is_followed (tree fact, not t20). READY lane/codex-reach bcc5965c6.
- t24-reachfix LAUNCHED (coordinator): diagnose that red (dispatcher changed vs reach_check stopped following
  the macro), fix, and list every NNTP command arm's reach.
- r20 paged-catalog 78d3f5c52 (gpt-6-astra, 288 s): raised 3 (2 bug, 1 claim-gap), CONFIRMED 3 (liaison read
  put-row/clear-w/clear-base and grepped host/Makefile): F1 every withdraw/redecide re-pushes msgid+aux into the
  append-only pool, old extents never freed (unbounded by history); F2 clear keeps overflow rows referenced;
  F3 the attach book claims host selection that does not exist. Clean: attach soundness (20 exports, identical
  :logic symbols), codec+overflow lossless, split preserves 384 defthm verbatim (Codex scripted the compare).
  Sent to main + paged-catalog-2. CORRECTION: F2 REFUTED by paged-catalog-2 and re-verified by the liaison:
  fn-cat$c-clear-w (catalog-logic.lisp:3858) calls fn-cat$c-clear, which resizes rows to 0 (:1173); Codex read
  clear-base only. r20 = 3 raised, 2 confirmed, 1 REJECTED. LIAISON ERROR: confirmed F2 without following the
  call chain to the definition. Rule: verify a "never done" claim by reading every function on the path.
- t21-defloop-2 (gpt-6-astra, 1117 s, 1 round): 8a66941e1 converts 8 twins in 7 books (-233 lines), translated
  equality evidence per twin; 17 left with exact generator gaps (9 = base-first (if (atom xs) TAIL ...) maps;
  CDDR/fn-ag-cdr steps; two-list merge; :concat with keep; recursive-result validation); 4 blocked by the
  nntp-index-runtime red, whose CAUSE Codex found (fn-nntp-numbers-sort-of-descending hints a withdrawn rule
  REVAPPEND-REMOVAL) -> main -> stage-0-2. AUDITED (removed events = exactly the 8 twins' defun/loop/bridge/
  verify-guards). hbox cert running.
- t25-defloop-gen2 LAUNCHED (coordinator-approved): :map :base TERM (base-first), one library theorem, the 9
  twins in the same commit, expansion-compat over every existing declaration.
- t26-hintcheck LAUNCHED (coordinator's idea): tools/hint_names_check.py, report-first, a static check that every
  hint rune/name is defined in the book's include closure (system-book names UNCHECKED, never passes); must
  find REVAPPEND-REMOVAL; then proposed to the runner for the fast checks.
- t23b round 3 (~10 min): 5767da6c8 PART C PROVED: fn-rl-install-correspondence (exported): on fn-rl-freshp (created
  ledger proved fresh) the exec word = (car (fn-rv-install ...)) except :unrepresentable-profile
  (fn-rl-profile-representable-p: u64 budget words AND u32 slot count); :installed -> fn-rl-bank = the logical
  bank; refusal -> ledger unchanged. The install now asks fn-rv-install on a 2-slot table before any store (cheap;
  ACL2 decides the word). The two "unreachable" branches proved by a LOCAL theorem (nit: the comments cite a
  local name). Liaison updated specs/resource-vector.md (b486c94d0). hbox cert running. Rounds: 3 (two were
  liaison decisions on real divergences, not rejected audits).
- t26-hintcheck (gpt-6-astra): ed8cb2eb8 tools/hint_names_check.py (report-only, ledger.Reader, include closure,
  system-book names UNCHECKED). 19 unit tests. Box: 5 TRUE dangling names (liaison verified each is defined only
  outside the referencing book's closure): nntp-index-runtime:343 REVAPPEND-REMOVAL; admission-semantic-census-
  prefix:161 fn-rccap-actual-resident-offer-establishes-same-mapped-row; config-carried-candidate:145-146
  fn-ocl-cpr-loop-configuration-is-the-record-fold + fn-ocl-config-fold; consumer-publication-budget:70
  fn-cpe-is-disjoint-from-old-event-kinds-by-shape. 0 residual false positives; ~40 s. Liaison box rerun pending.
- t24-reachfix: 05082e7e7 (a) stale test fact after 6aa65979f; READY. Its arm table exposed the tools/*.py
  seeding hole -> t29 (coordinator APPROVED: measure first, decide per arm).
- t25-defloop-gen2 (gpt-6-astra): bd0a4d5da :map :base (one library theorem, progress-only constraint, 0-ary
  fixp selector for acc-fix); 42 existing expansions identical; 8 of 9 twins converted (the 9th blocked by the
  nntp-index-runtime red). AUDITED; persvati cert (t21+t25 books) running.
- LAUNCHED: r15 def-carried-gen ed418f107 (fresh; prior findings + LANEDUMP in the prompt) -- LIAISON ERROR:
  launched with a bare & (detached, survived; poll last.txt); t27-genscan (scanners see generated defuns;
  callgraph.collect lacks def_loop_expansion; unblocks the held 747f17594); t28-declare (every host dispatch
  declared + "0 undeclared" as a hard precondition of the carried check); t29-reachseed step 1 (measure only);
  r21 paged-catalog-3 58e81c4e9.
- r15 def-carried-gen ed418f107 (fresh, gpt-6-astra): raised 2 (1 bug, 1 claim-gap), CONFIRMED 2 (liaison read
  fn-cd-stobj-position/fn-cd-parts and the test): F1 congruent stobjs: input slot and output slot chosen by two
  INDEPENDENT first-congruent matches, so (cross A B) -> (mv B A) binds an invariant about B's output as A's carried
  transition (5th instance of the wrong-subject class; full counter-model, legal per ACL2's own congruent-stobj demo);
  F2 bump "single" removal drops R twice. Clean: forged rows, name capture, exact 'theorem equality, :concludes,
  :hyps, value rows; r02/r08/r09/r14 closed except r02-F7 partly. Sent to main + def-carried-gen. Runner holds.
- r21 paged-catalog-3 58e81c4e9: raised 3 (1 bug, 1 claim-gap, 1 nit), CONFIRMED 3: F2 FN_NATIVE_IMAGE (always set by
  hbox_native) defeats the -paged suffix: a stale FN_NATIVE_CATALOG=paged builds a paged core under the old name and
  image_set/--reuse-image reuse it; F1 section 6 teeth do not assert the literal keystones; F3 stale attach comment.
  Coordinator's asks clean (real equation; default old everywhere; no new allocation). Sent to main.
- t30-danglefix LAUNCHED (coordinator): census-prefix include or local lemma; consumer-publication-budget's hint names
  the theorem 0778994b1 renamed (fn-cpe- -> fn-cne-, different recognizer).
- t29-reachseed step 1 (report only): dropping tools/*.py seeds loses 143 functions and 3 hosted events (PRF-041 x1,
  PRF-222 x2), 0 protocol arms. LIAISON CORRECTION: my "arms reached ONLY via tools/ledger.py" (from t24's chain
  display) was wrong -- the display picked a tools root first; host roots exist. Sent to main; step 2 awaits OK.
- r16 def-carried-gen 10126138b (the r15 fix: one congruent input slot; output by slot name) LAUNCHED with the
  congruent-stobj family (swapped, passed twice, nested mv, stobj-let children, returned twice).
- r16 def-carried-gen 10126138b: SOUNDNESS CLEAN (congruent family + standing question); 2 test-only confirmed (F1 tick
  positive is a selector assertion; F2 stale comment at tests:782). Recommended land + fix-forward; coordinator decides.
- t25+t21 READY lane/codex-defloop-gen2 f3b35dc70 (persvati certify-20261001T140258Z-2023672 CERT 0); contains held
  747f17594 -> must land with/after t27.
- t23b: hbox certify-20261001T135735Z-3052843 CERT 0 (exec, exec-tests, relations-tests; 6 deps installed without
  cited manifest). ledger --check was RED on the deputy's stale PRF-1210 cite fn-rv-credit-ledger-funded-iff (renamed
  -by-definition, uncitable): liaison removed it from planning/proof-events.json; regen on hbox RUNNING at hand-off.
- t30-danglefix: BLOCKED (its base predates hint_names_check on dev; both books' dependencies red at that base;
  hbox certify-20261001T140440Z-3064186 failed). Changes left UNCOMMITTED in build/lanes/codex-danglefix.

## HAND-OFF liaison-3 -> liaison-4 (2026-10-01 ~10:10, ~150 tool uses)
Tally liaison-3 reviews: r17 1/1 (+1 pre-existing false theorem), r18 3/3, r19 2/2, r20 3 raised / 2 confirmed / 1
REJECTED (F2; my verification miss, caught by paged-catalog-2), r21 3/3, r15 2/2 (a real soundness bug), r16 2/2
(test-only; soundness clean). Tasks: t18, t20, t22(->genfix3), t23b (3 rounds), t24, t25, t26 READY or done; t21 in t25.
### LIVE (poll <wt>/build/codex/<id>/last.txt; bg notifications will NOT reach you)
- t27-genscan: DONE BY CODEX AFTER HAND-OFF, UNAUDITED (last.txt present). build/lanes/codex-genscan (lane/codex-genscan = held 747f17594 + dev). Scanners see generated defuns
  (callgraph.collect lacks ledger.def_loop_expansion). Audit: diff, unit tests, box reach --strict 0 with PRF-243
  fn-rcompat-hdr-lines-are-clean HOSTED; regen committed. READY -> runner lands it WITH codex-defloop-gen2 f3b35dc70.
- t28-declare: DONE BY CODEX AFTER HAND-OFF, UNAUDITED (last.txt present). build/lanes/codex-declare (from def-carried-gen ed418f107). Every undeclared host dispatch gets an honest
  definterface; interface_emit --check 0; "0 undeclared" a hard precondition of the carried check (tools/interface_emit.py)
  + unit test. Audit EVERY declaration (no blanket, true :kinds/:exempt), host_check --books/--load no new findings.
  NOTE def-carried-gen moved to 10126138b: merge it into codex-declare before READY.
- t23b: DONE. READY lane/codex-rlfix2 eb30e5777 sent to the runner (ledger/cv --check 0 on hbox; dev moved after b2efd577a,
  so the runner regenerates the planning files on merge).
### QUEUED (approved, not launched)
- t29 STEP 2 (coordinator APPROVED): in tools/reach_check.py seed only from loaded host files (drop tools/*.py
  bridges); unit test "a book symbol mentioned only in tools/ is NOT hosted"; baseline dispositions EXACTLY:
  PRF-041 fn-bs-k0-finish-program-preserves-relation = SPEC "crash-model program for fnn-finish, checked by
  native_program_check, not a served call target"; PRF-222 fn-auth-view-consistent-back and fn-gac-consistent-back =
  SPEC proof-only (fn-served-connp is a carried-invariant hypothesis that never runs, books/served.lisp:725-731).
  Step-1 data: build/lanes/codex-reachseed/build/codex/t29-reachseed/{REPORT.md,measurement.json}.
- t30 rerun: new worktree from origin/dev AFTER codex-hintcheck lands (runner batch 9) and the census/consumer deps
  certify; same TASK (build/lanes/codex-danglefix/build/codex/t30-danglefix/TASK.md + its REPORT for what failed).
- r22 (requested by deputy-2 ab962860f9681bdd5): Codex review of deputy2/recovery 9b040fe99 (PRF-1223 batched program:
  books/byte-store-programs.lisp :write-at step kind + D1/D2 coverage; byte-store-state-checkpoint-program.lisp
  fn-bs-scp-batched-program + the by-definition one-batch equation; tests/acl2/byte-store-state-checkpoint-program-
  tests.lisp). Ask: does any D1-D3 discipline predicate or existing theorem over fn-bs-step MISS the new kind (a hole
  the split opens)? is the labelled offset-0 mutant the right contrast? The keystone at every state is NOT claimed.
  Also cheap: deputy2/def-carried 8c7b477e9 = 10126138b + prose in books/owner-retain-carried.lisp (review prose).
- r23 (requested by paged-catalog-4 a92c068d6d7a309ec): Codex review of lane/paged-catalog dabe9458e, answering r20-F1 and
  r21-F1/F2. Range from 58e81c4e9. Ask: (a) r21-F2: does EVERY build/publish/link/reuse path now refuse a catalog
  mismatch (build_native_host name/catalog checks + IMAGE.catalog; image_set catalog_of/wrong_catalog on
  publish/link/link-run; hbox_native explicit FN_NATIVE_CATALOG / --catalog paged); a path still untyped?
  (b) r20-F1: books/proto/adt-load.lisp adt-fill-is-load + def-representation :write-once (NAME$C-FILL-IS-LOAD-OF-*
  per writing export); put-row deleted -> fn-cat$p-set-withdrawn / -set-cell. Is pool fill now a FUNCTION of the
  live rows (a real bound, not vacuous); does every writing export carry the theorem; does withdraw/redecide still
  push bytes? (c) teeth sections 6-7 (drt-tpp, drt-t1-is-append-ok, drt-w1-run-ok, drt-t1-rewrite-ok removal):
  complete antecedent, removal, labelled mutation? Known open, do NOT re-raise: adt-pool-cput silent no-op (NEXT A'),
  gates B and C (lanedumps/paged-catalog-4.md).
- r24 (requested by assurance-remainder a3a6e59697a3eeca3): Codex review of lane/assurance-remainder c27cecc00.
  books/post-record-width-owner.lisp PKT-250 keystone fn-prwo-owner-post-record-is-narrow-within-the-profile (over
  fn-pak-post-admission + fn-sn-article-record + fn-apc-intern-row-at + fn-ppc-pout-prepare-article-cat; host callers
  host/owner-host.lisp fn-owner-post-boundary / fn-owner-prepare-buffer) + tests/acl2/post-record-width-owner-tests.lisp;
  the Q3a deletions in books/bp-fnbs-replay.lisp / bp-fnbs-delivery-replay.lisp and the ported
  tests/acl2/bp-fnbs-replay-tests.lisp. Ask: any vacuous/unsatisfiable hypothesis (reachable full-antecedent witness?);
  is the subject the host-called function or a named equality to it -- are the boundary/prepare host-side equalities
  named in PRF-123's statement the ONLY gap; did the deletions remove anything still cited or depended on (registry,
  includers); teeth complete.
- r16 follow-up: def-carried-gen fixed F1/F2 at 3360e2157 (owner: r16-carried row admitted, statement pinned, reachable witness on a live congruent instance; comment fixed; hbox run-20261001T141433Z-a9fd; READY sent to runner by the owner). Liaison-4: spot-check the new witness asserts the complete antecedent + conclusion (tests only; no fresh review).
- After stage 0 lands (BC-ANNOUNCE.md): REVIEW its READY hard first; then t16 figure-docs
  (build/coordinator/queue/codex-t16-figure-docs-AFTER-STAGE0.md); re-certify the chains blocked behind
  nntp-index-runtime (codex-authtests scope/completion/wire-charge; defloop nntp-reader-compat/group-access/peer-catchup);
  t08 rerun + world.py==umbrellas fast check (r21 noted the OLD umbrella already drifts from its renderer).
- def-loop next generator gaps (t21 report): configurable step (CDDR / fn-ag-cdr), :concat with :keep / base-first
  / non-nil tail, two-list merge, recursive-result validation.
### Forwarded, owners pending: r20-F1 pool leak on withdraw/redecide (paged-catalog-3 NEXT F); r21-F2 FN_NATIVE_IMAGE
  defeats -paged (paged-catalog-3 successor); r17/r19 done; 5 dangling hint names (3 stage 0's, 2 = t30).
### Lessons: verify a "never done" claim by reading EVERY function on the path (r20-F2); never a bare & (I repeated
  liaison-2's error with r15: detached, survived); ask owners before a fix-forward (t22/t23 duplicated the deputy);
  a remote_check whose local merge conflicted still runs on the dirty tree -- check `git status` after.

## HAND-OFF liaison-2 -> liaison-3 (2026-10-01 ~08:40, ~146 tool uses)
### LIVE / DONE-UNAUDITED (harvest by polling <wt>/build/codex/<id>/last.txt; bg notifications will not reach you)
- r17 paged-catalog-gen a5d1f2c4a (coordinator stream A): build/lanes/codex-r-r17-pcg/build/codex/r17-pcg/
  FINDINGS.md (questions: NAME-clear correspondence for every shape, logical vs concrete clear, the TP rule
  adt-nth-of-all-elt-p-natp global safety, the 2 reds). Triage -> findings to main; clean -> tell runner
  a5d1f2c4a may land; also reply to ad5b0b72e2a23338a (paged-catalog-2).
- t18-defloop-gen DONE, UNAUDITED: build/lanes/codex-defloop-gen (lane/codex-defloop-gen on codex-defloop
  7f20b3270): def-loop extended for the 7 gaps, 8 twins converted, 6 left; REPORT has translated-equality
  evidence. Audit: read def-loop.lisp diff (one library theorem per new shape, no per-instance induction,
  existing emitted forms unchanged), ledger.py mirror + tests; hbox certify --incremental
  tests/acl2/def-loop-tests + the changed books (nntp-reader-compat/web-session etc. may be blocked
  behind nntp-index-runtime until stage 0 lands -- say so); READY; send the READY to the Fable deputy
  a673cde35dfbc7eaf too (it owns the generators). Then batch 2 over remaining twins (inventory:
  scratchpad loop-fanin.txt method: git grep -l -- "-loop-is-revappend" origin/dev -- books, rank by
  include fan-in; avoid catalog/served-catalog/msgid/page-word/stage-0 books).
- t20-reach-export DONE, UNAUDITED: lane/codex-reach b5af31929 (on t19 022d7d66d): reach_check rule linking
  a correspondence export to the host-called keyed export via named evidence; PRF-201 baseline entry
  removed; Codex's box run 0 unbaselined. Audit: read the rule (must not match by name similarity),
  the unit tests, rerun reach --strict on a box yourself; READY superseding 022d7d66d.
- def-carried: owned by Fable deputy a673cde35dfbc7eaf (generated-statements design per coordinator).
  When it sends a sha: launch r15 (fresh Codex, prompt base scratchpad/q-r14.md) with the coordinator's
  instruction "find any way to make def-carried emit, or :raw-with accept, a statement other than the
  generated forms"; include r02/r08/r09/r14 FINDINGS; clean -> superseding READY (runner holds 450005e2c).
- r18 deputy1/resource-ledger 0903f9d2b and r19 deputy1/generators ee31fe17d (requested by deputy
  a673cde35dfbc7eaf): Codex reviews LAUNCHED by liaison-2 at hand-off; outputs
  build/lanes/codex-r-r18-rl/build/codex/r18-rl/FINDINGS.md and build/lanes/codex-r-r19-gen/build/codex/
  r19-gen/FINDINGS.md. r19 TRIAGED by liaison-2: 2 raised / 2 confirmed (F1 clear uses string-base adt-sym ->
  ACL2-package RESIZE-/UPDATE- names for foreign-package instances, proto/adt.lisp:223,379-381; F2 no removal
  teeth for adt-corr-of-clear-c), sent to main. r18 TRIAGED too: 3 raised / 3 confirmed (exec fn-rl-install
  half-installs on refusal; reinstall resize discards generations -> exec ABA replay; relation teeth still open),
  logical model clean; sent to main. Both reviews DONE.
- r20 paged-catalog-2 78d3f5c52 (requested by ad5b0b72e2a23338a): correctness clean, 2 resource claim-gaps
  confirmed (commit doubles rows array in one call; scan-up Theta(N) on withdraw); not host-called yet. Sent to
  main + lane; coordinator decides gate vs stage-3 NEXT. Triage (verify each in source), findings -> main; clean -> tell runner it may land.
- def-carried: the deputy did NOT do the rewrite; the generated-statement design is in
  build/coordinator/lanedumps/deputy-1.md section 3 for the NEXT deputy. No r15 until a sha exists.
### QUEUED
- t16 figure-docs: build/coordinator/queue/codex-t16-figure-docs-AFTER-STAGE0.md (launch when stage 0 lands).
- After stage 0 lands: re-certify the chains blocked behind nntp-index-runtime / store-reclaim-pack
  (codex-authtests scope/completion/wire-charge; codex-defloop expiry/group-access-cache/nntp-reader-compat);
  t08 rerun (world.py render vs committed umbrellas) + propose a world.py==umbrellas fast check to the runner.
- PRF-1131 missing join (window codec tick -> served pooled decoder): queued LOW by the coordinator.
- r16 nit (store-finalize-incremental.lisp:243-245 comment), r13 nit done in codex-rrnit.
- Stage-0's READY: review it hard (gates without producers, early returns, wrong restorations).
### READYs sent by liaison-2 (all audited + certified as stated): codex-burndown 0363e9ef6 (t06),
  codex-pagefix a88089666 (supersedes aa338ba4a), codex-regen 335c676a5 (t13), codex-genfix ce9932b05 (t10),
  codex-rrnit b444981e0, codex-defloop 7f20b3270 (t17), codex-reach 022d7d66d (t19), codex-authtests 62e434e33,
  codex-msgidfix 075adef14 (t15). Cleared to land: msgid-linear-hash d47156da4, figure-and-contract
  b224e8a69, served-certify 48bbd31a5.
### Tally liaison-2 reviews: r20 2/2, r18 3/3, r19 2/2, r10 4/4, r11 4/4, r12 3/3 (+1 pre-existing gate), r13 1/1, r14 1/1, r16 1/1
  confirmed; 0 rejected. Codex task lesson: require "admitted to the end in proof_repl (--source-deps
  --load-limit 0 --limit 600)" before commit; t15 round 1 committed unadmitted teeth.

## LIVE SESSIONS at hand-off (each in its own worktree; outputs under <wt>/build/codex/<id>/)
- (done) r08 def-carried RE-REVIEW 450005e2c: VERDICT not clean; 3 raised (1 bug: the
  declared third-element PATTERN re-opens r02-F2's exploit; 2 teeth), 3 confirmed (liaison
  verified fn-cd-entryp/fn-cd-returned-call). 5 of r02's 7 confirmed closed. Sent to main.
  NEXT: re-review def-carried's next READY again (r09).
- t06-test-moves: DONE by Codex 48b713d0e, AUDITED by liaison (2 renames with only the
  include path changed + 2 Makefile root lines; pushed). CERT RESULT hbox certify-20261001T105259Z-2809623: roots check 0; both test books FAILED only because their parent books (index-reader-render-establishment, reader-output-storage) have NO certificate, never having been roots -- recertify with the parents first, then READY. Earlier: box certification launched by
  the liaison -> build/lanes/codex-burndown/build/codex/t06-test-moves/certify-remote.txt
  (ROOTS_EXIT, CERT_EXIT). If CERT_EXIT=0 -> READY lane/codex-burndown 48b713d0e to runner+main;
  else report the failing root to main (the parents index-reader-render-establishment /
  reader-output-storage were never roots and may not certify).
- t11-pagefix DONE by Codex (21bfc0cfb, 448c6c5fc; pushed lane/codex-pagefix), AUDITED by
  liaison: u64 NOT derivable (counter-model checked by Codex in ACL2); prose now says the
  encapsulate GAINED u64 and cites the real host realizer (byte assembly in host/native/extent.lisp,
  NOT a u64-array pread -- Codex corrected the brief instead of inventing evidence);
  failures.md + PRF-1217 registry rows updated; teeth: whole-frame witness + labelled offset
  mutant. OPEN before READY: the full test book was not REPL-admitted (a clean dependency session
  timed out at the 60 s prover limit on unchanged books/octets-stobj fn-oct-octet-listp-of-back-copy):
  certify tests/acl2/history-records-disk-tests + books/assumptions-pgs-host-io on hbox, and
  regenerate planning/current.md (current_view --check stale). Was: t11-pagefix (PRIORITY, build/lanes/codex-pagefix, lane/codex-pagefix from aa338ba4a): r07's
  u64 assumption made honest (derive or declare + registry + mentions) and the frame teeth.
  Audit: the assumption encapsulate diff line by line (must not get stronger than u64), the
  test witnesses, proof_repl admission; superseding READY to runner + main BEFORE t10.
- (done) t09-program-baseline: found 610, listed 530, intersection 509, NEW 101, GONE 21; sent
  to main; coordinator: keep the ratchet; 101 -> DEPTH-AND-PROGRAM lane.
- t12-dcfix DONE by Codex (0b8a3046f, f0a34effc, 68daac251; pushed lane/codex-dcfix); diff
  audited. FRESH re-review r09 (new codex exec, gpt-6-astra): VERDICT not clean. Confirmed by
  liaison: F2 [bug] the PATTERN restriction is applied only to transitions --
  fn-cd-establishment check (def-carried.lisp ~486) still accepts `(r09-bad-open thm (fn-cdt-open _))`
  as an establishing point, and :raw-with resolution includes established theorems. F1
  [claim-gap] value-state rows still accept a repairing PATTERN (raw binding of it is refused by
  definterface, so a row/trace claim gap only). Fixes needed: apply fn-cd-stobj-patternp to
  establishing entries; restrict value-state patterns to declared projections (or record them as
  unverified). Then another fresh re-review (r10). NO READY.
  Was: t12-dcfix (PRIORITY 1, build/lanes/codex-dcfix, lane/codex-dcfix from 450005e2c): r08's three
  fixes (PATTERN restricted to _ / (mv-nth K _) with K from stobjs-out; complete-declaration
  must-fail-checked teeth; tcpcl-session-carried witnesses). Audit the diff + proof_repl
  admission on hbox; THEN a FRESH Codex re-review session (new exec, not resume) with r02+r08
  findings told to break the PATTERN restriction; only a clean re-review -> superseding READY.
- t10-genfix DONE by Codex (2f02804ad quote-respecting fn-dl-subst; 5c22b4fbf ledger.py exact
  :sum/:into bridge statements; d29db6646 def-representation names in the instance package via a
  two-expansion probe -- clever, heuristic, prototype helpers untouched; 7899f4547 teeth), pushed
  lane/codex-genfix. AUDITED diff by liaison: correct. Admission-only (clean proof_repl); the
  two-package collision test was not added (needs a new .acl2 portcullis; package-of-name checks
  instead). OPEN before READY: merge origin/dev (generators landed at 69fe92a80), regen
  planning/ledger.* on a box (tests.test_ledger's checked-in-ledger test fails because the
  recorded bridge statements changed -- expected), certify def-loop/def-representation tests on hbox.
  Was: t10-genfix (stream B', build/lanes/codex-genfix on lane/codex-genfix from ba67b814b): r04's
  four fixes. Audit: 4 commits, scope, rerun proof_repl admission of def-loop-tests and
  def-representation-tests + the ledger unit tests; merge origin/dev (generators landed);
  one READY. THEN start the def-loop conversion stream (coordinator: batches of ~20 twins in
  low-fan-in books; inventory build/coordinator/scholar-proof-engineering-2026-10-01.md;
  never served host files or stage-0/paged-catalog/msgid/page-word books).

## NEXT (successor liaison)
0. Priority order of audits: t12-dcfix (+ fresh re-review), t11-pagefix, t10-genfix, t06 cert.
   Queued, not started: t13 drop the 21 GONE names from tools/depth_baseline.json "program"
   (list in build/lanes/codex-regen/build/codex/t09-program-baseline/REPORT.md; separate
   commit; audit = the 21 removed only, depth_check on a box shows gone 0); then the def-loop
   conversion stream after t10 lands.
1. Harvest the four live sessions above (each has last.txt when done; a background Bash
   notification will NOT reach a new agent: poll `ls <wt>/build/codex/<id>/last.txt`).
2. Review queue: re-review def-carried's next READY (r02's 7 findings); r01/r03/r05/r06
   lanes' fixes when they READY; at least one review per stage-0 and generators landing.
3. t08 rerun after stage 0 lands on dev (world.py render vs committed); any residue -> READY;
   propose a fast check `world.py render == committed` to the runner.
4. Remaining burndown (make-check-summary 2026-10-01): L10 REGEN-TRUTH rest -- coverage.json
   via tools/coverage.py on a box after SC certifies the world, reach_check seed/baseline
   dispositions, twins.json; the 11 orphan books for the coordinator (list below).
5. Orphan books (no include, no Makefile root, no host load; coordinator decides, do not
   delete): admission-semantic-census-initial-order-refinement, admission-semantic-census-
   owner-refinement, bp-received-raw-registry, bp-segmented-wire-job, consumer-configured-
   control-source, decoded-window-stored-frontier-trajectory, history-config-completion,
   recovery-file-turn, recovery-page-file-controller, replay-identity-enrollment-continuation,
   tcpcl-received-source-refinement.

## Verdict on the protocol so far
Codex (6.1-sol then 6-astra) under TASK files with pasted ground truth stayed in scope on
every task (0 out-of-scope edits, 0 gates added, 0 rejected diffs); it STOPPED and reported
on 2 contradictions that were the liaison's own drafting errors. Reviews were the strongest
use: r02 (def-carried) and r06 (resource-ledger) found real bugs the lanes missed; every
finding raised was confirmed on verification (34 raised by Codex across r01-r09 plus 1 liaison-derived from a Codex note; 34 confirmed, 0 rejected). Costs:
the liaison's audit time, and Astra's literalness (write scope precisely). Ground truth must
come from a full box run (make-check-summary shows only the first finding per step).

## FINAL (liaison 1 stops here)
- t14-dcfix2 was LAUNCHED just before the coordinator's stop: Codex session running in
  build/lanes/codex-dcfix, TASK build/lanes/codex-dcfix/build/codex/t14-dcfix2/TASK.md = the
  coordinator's structural fix (one pattern validator for every consumer; fn-cd-returned-call
  refuses unvalidated patterns; enumeration test per keyword). Output last.txt/REPORT.md there.
  liaison-2 (afd193de1477ccaae): audit it (or discard), then a FRESH re-review instructed "find ANY
  declaration path that binds a theorem about a term other than the function's returned carried
  state"; clean -> superseding READY.

## Liaison-4 log (codex-liaison-4, Opus, a11a588e8e91a5dd4)
- t23b: liaison-3's hbox regen finished LEDGER 0 / CV 0; eb30e5777 committed+pushed (by liaison-3 at hand-off). Liaison-4
  merged origin/dev (312c0f043; generated ledger conflict -> dev's, regen on hbox).
- t28-declare AUDITED: 32 declarations read; spot-checked 14 against source (explicit :guard t; eagerness-0 books ->
  :ideal honestly; fn-ort-log-close-exit integerp kinds right); precondition + unit test read (fires only with a
  :carried :raw-with; none in host/ yet). CONFIRMED its report-writer gap: native reclaim swap (owner.lisp ~6258)
  dispatches fn-owner-report-writer-enter/-leave/-fault whose book no build loads -> main (already owned by stage 0;
  verify in stage 0's review). Rebased per coordinator onto CANONICAL def-carried-gen 3360e2157 + prose 8c7b477e9:
  lane/codex-declare2 (cherry-picks 0a62607fe, af569f48d). lane/codex-declare (merged deputy2 b6fcbf06a) ABANDONED.
- r22 deputy2/recovery 9b040fe99 LAUNCHED (worktree codex-r-r22-recovery).
- t29b-reachseed (step 2) LAUNCHED: lane/codex-reachseed2 from c9c1791a3.
- t23b READY lane/codex-rlfix2 3f747a8e6 (dev merged; hbox ledger OK / cv OK / reach --strict 0; cert 135735Z CERT 0)
  -> runner (batch 10, replaces eb30e5777) + main.
- r22 deputy2/recovery 9b040fe99 (gpt-6-astra, ~4 min): raised 2 (1 claim-gap, 1 test bug), CONFIRMED 2 (liaison read
  fn-bs-crash-select/fn-bs-tear-write and the keystone): F1 comment claims fn-bs-scp-program-crash-is-old-or-new covers
  every BATCHED state (it is over fn-bs-scp-program only); F2 *scp-t-apply-all* '(:apply ...) lands NO write bytes
  (a :write takes a selector list; non-list -> tear-write nil), so the "land-everything" teeth were drop-the-writes.
  Split soundness CLEAN (exhaustive step-kind inventory). Extra open joins for the batched keystone (history-image
  prefix io.lisp:3306 before the steps; empty batch steps io.lisp:3364; a non-:ok positive-offset mutant survives).
  Coordinator: 9b040fe99 lands; fix-forward = t31-scpfix (lane/codex-scpfix) LAUNCHED. Deputy-2 confirmed it had not
  started (no duplicate).
- r16 follow-up spot-check (f3c7c9567 in def-carried-gen 3360e2157): r16-witness evaluates the full antecedent
  (r16-r, r16-bp) before r16-tick and the conclusion after, on a live congruent stobj; statement pinned. OK.
- t27-genscan AUDITED (gpt-6-astra, ~45 min incl. box runs): 51ac84e00 = ledger.generated_expansion (one dispatch for
  def-loop/defrecord/defprotocol/defkeystone) used by ~25 scanners; def-loop mirror now carries bodies. PRF-243 and
  PRF-366 HOSTED. LIAISON FIX: after merging defloop-gen2 f3b35dc70 (t25's :map :base), the body mirror lacked
  :map :base (base TERM's callees missed) -> ledger.def_loop_bodies + test case (liaison commit). Merged f3b35dc70 +
  origin/dev into codex-genscan so ONE READY covers 747f17594 + f3b35dc70 + t27. Box acceptance running.
- r23 paged-catalog dabe9458e LAUNCHED (r21-F2 image identity on every path; Gate A write-once enforcement — a second
  write must be a refusal/guard violation, never a silent overwrite/no-op; pool fill = f(live rows) incl. churn;
  teeth sections 6-7).
- t28 HELD by runner until stage 0 lands (collides with stage 0's host/interfaces.lisp): after stage 0 on dev, re-run
  t28 against the post-stage-0 host (declare only what it still dispatches), fresh READY. lane/codex-declare2
  af569f48d pushed (interface_emit 48 -> 16; host_check unchanged).
- r23 paged-catalog dabe9458e (gpt-6-astra, ~6 min): raised 5 (3 bug, 2 claim-gap), CONFIRMED 5. Write-once CLEAN
  (byte setters not exported); fill=load per every writing export, churn leak gone. F1 missing IMAGE.catalog -> "old"
  (pre-fix paged cores publish as production); F2 old branch accepts FN_NATIVE_BUILD=build/native-build-paged.lisp;
  F3 --no-build preflight ignores -paged; F4 drt-t1-is-append-ok natp checks field A not fill, projection not state
  equality; F5 write-once "removal" is a schema mutation. -> main + paged-catalog-4.
- r24 raw-dispatch dc4144a13 (def-carried :ok + :witness + NAME-FN-reaches, H1) LAUNCHED, priority, trust-critical.
- r24 raw-dispatch dc4144a13 (gpt-6-astra): raised 2, CONFIRMED 2: F1 bug forged (table fn-carried) row with
  :established nil / vacuous establishment passed fn-cd-raw-problem (fn-cd-problem never required an establishment;
  only the macro's fn-cd-refusal did); liaison extension: the macro's vacuity probe is minimal-theory only, so an
  opener guarded by R passes. F2 teeth: 3b witness lacked fn-cdt-stp. H1 (:ok) itself clean. -> raw-dispatch (fixer)
  + main. Fixed at d79a0fd07 (+ new feature (b) :produced b18f4d4c2) -> r25 LAUNCHED.
- t31-scpfix (gpt-6-astra, ~15 min, 1 round): 639f456bc: F1 comment reworded (+ config.json -> store-checkpoint.fnsc
  slips), F2 choices generated per state from fn-bs-pending, fn-bs-crash-choicesp asserted, land-everything proven to
  land (1 2 3 4 5 6) pre-fsync, error-outcome mutant must-fail, PRF-1223 note. Codex hbox cert 144234Z CERT 0 (dirty
  tree); liaison recertifying at the commit.
- t32-imageid LAUNCHED (r23 F1-F3, coordinator-approved, lane/codex-imageid from dabe9458e).
- LIAISON ERROR (x2): run_in_background without a long timeout killed t29b's Codex at 30 min (mid-acceptance; diff
  intact, box run survived) and my t27 box-wait. Use timeout 3600000 for Codex sessions and attaches.
- r25 raw-dispatch d79a0fd07 (gpt-6-astra, 345 s): raised 5 (1 bug, 4 claim-gap), CONFIRMED 5: F1 r24-F1 NOT closed
  (an entry with a :reaches field but no :witness/:ok skips the reaches check; fn-cd-unwitnessed-1 tests field
  presence only); F2 (b)'s caller scan is 'unnormalized-body only (raw fnn-call / defattach alias escape); F3
  named-assumption = constrainedp + FN-ASSUME- spelling, no book provenance; F4 3c witness asserts natp not the
  literal assumption, omits fn-cdt-stp; F5 the witness's own literal-0 call masks the later caller must-fails.
  Host-order standing question: no current defect (documented host obligation). -> raw-dispatch + main.
- t32-imageid READY lane/codex-imageid 90342fc47 (54 unit tests OK) -> runner + main. Coordinator: add a one-time
  evidence BACKFILL -> t33-backfill LAUNCHED (image_set backfill-catalog SHA --repo GIT_DIR; liaison runs it on hbox
  with --git-dir /tank/fn/scratch/remote-check.git). The 4 published sets (33bb1ada7, 444fb9f41, 6462bd687,
  e739bc934) all PREDATE books/catalog-paged.lisp (laptop git cat-file).
- t31 READY lane/codex-scpfix 58a34f379 (liaison recert hbox certify-20261001T151508Z-3164213 at 639f456bc, manifest
  committed) -> runner.
- r26 assurance-remainder c27cecc00 (gpt-6-astra): raised 3 (1 bug, 1 claim-gap, 1 nit), CONFIRMED 3: F1 deleted
  fn-bpah-replay-rows still called 12x by tests/acl2/bp-fnbs-delivery-replay-tests.lisp (Makefile root + included
  by -publication-tests); F2 fn-prwo keystone absent from proof-events.json; F3 stale spec prose. PRF-123 subject
  = host POST path (clean), teeth complete. -> main.
- r27 paged-catalog-5 6134b2399 LAUNCHED (findings -> main + paged-catalog-6; paged-catalog-5 handed off; it flags
  the guard-checking :none removal witness as OPEN: does it execute the :logic body or raw stobj code?).
- t30 rerun: lane/codex-danglefix2 from origin/dev 136914edf with Codex's uncommitted t30 diff applied; liaison
  hbox cert + hint_names_check running.
- t33-backfill (gpt-6-astra, ~5 min): e346744e8 image_set backfill-catalog (SUMS + TREE_SHA verified; git cat-file
  evidence; atomic manifest + sums). AUDITED; liaison RAN it on hbox: 4/4 sets predate catalog-paged -> backfilled
  33bb1ada7 (4), 444fb9f41 (3), 6462bd687 (3), e739bc934 (3); image_set check OK each. READY lane/codex-imageid
  e346744e8 -> runner BI af0c83681089d902e (merged into batch/bi) + main.
- r27 paged-catalog-5 6134b2399 (gpt-6-astra): r23 F4/F5 CLOSED (and the guard-checking :none removal executes the
  logical bodies — traced); raised 3 claim-gaps, CONFIRMED 3 (catalog-live-links header claims nonexistent
  integration; "clear-keyed changes no liveness" false; keystone fn-cpl-okp-of-withdraw has no teeth) -> main for
  paged-catalog-6 (pc5 handed off) + runner told it was reviewed.
- r28 raw-dispatch 9e38b7e87 (gpt-6-astra): r25-F1 CLOSED; raised 5 (2 bug, 3 claim-gap), CONFIRMED 5: F1 produced-open
  lint misses (funcall 'F)/apply/symbol-variable targets (harness_check.raw_applications); F2 defabsstobj :exec /
  attach-stobj aliases outside the caller scan; F3 fn-cd-attached-to reads attachment history (removed defattach
  refuses forever); F4 forged-field must-fails accept any refusal; F5 producer theorem lacks a positive witness and
  its premise is redundant. -> raw-dispatch + main.
- assurance-remainder-2 1ba65b974: r26 F1-F3 verified by liaison inspection (grep); told it to certify the two
  delivery-replay test roots + regen before READY.
- t27 box flake: test_generated_scanners FAILS when run in one process with tests.test_ledger (passes alone and with
  test_reach_check); import-order pollution from test_ledger — follow-up before adding it to the Makefile fast list.
- t29b READY lane/codex-reachseed2 7c0bec092 (hbox at dev merge: reach --strict 0, ledger/cv OK) -> runner BI + main.
- t30 rerun (lane/codex-danglefix2 = Codex diff on dev 136914edf): STILL BLOCKED, hbox certify-20261001T154150Z-3188362
  fails 60 closure books (history-cold-record-cursor, snapshot-*, census-resident/-lineage, store-profile-carried,
  nntp-index-runtime -> nntp/owner/served). Rerun after CERT-ROOTS + stage 0.
- COORDINATOR RULE (def-loop conversion stream): a batch lands only when EVERY converted book AND its direct
  dependents certify on hbox; "blocked behind a red" = HOLD. (t17 7f20b3270 broke books/expiry's bridge on dev;
  fixed forward by stage-0 8849a9aa9.) Liaison: cert world lane/codex-defloop-cert = origin/dev + lane/stage-0 +
  lane/codex-genscan (NOT for landing); certifying t17's 7 + t21/t25's 10 converted books and their 50 direct
  dependents (image-world umbrellas excluded) on hbox. codex-genscan's READY waits for that cert.
- t27 genscan: final hbox acceptance at the dev merge ba11616df: 84 unit tests OK (generated_scanners + reach_check +
  interface_emit), reach --strict 0, PRF-243 HOSTED via fn-rcompat-hdr-lines, interface_emit 48 / host_check 4 (= dev),
  ledger/cv OK -> 1aa58d03e pushed. READY HELD for the conversion cert (rule above). Merge resolution: tree_theorems
  keeps dev's carried_generated over t27's shared-mirror reader.
- r29 raw-dispatch 388c8102c LAUNCHED (A-RECOVERED-OPEN, producer pairing, owner row, r28 closure).
  LIAISON ERROR: first launch used a bare `&` inside a Bash call — the process died with the shell (nothing ran);
  relaunched with run_in_background. Third liaison to do this; the launcher should refuse a non-background parent.
- r30 paged-catalog-6 f755523b6 LAUNCHED (reader equalities, okp preservation per export, msort=isort, fallback).
- CONVERSION CERT DONE: hbox certify-20261001T160420Z-3208843 in dev 136914edf + lane/stage-0 + codex-genscan: 17
  converted books (t17/t21/t25) + 51 direct dependents = 68 roots, 267 books certified, 0 failed (umbrellas excluded).
  Manifest committed; READY lane/codex-genscan c6aa40479 -> runner BI (land WITH/AFTER stage 0: dependents need its
  nntp-index-runtime/expiry fixes). t17's batch-1 dependents now certified in that world too (the coordinator's ask).
- r29 raw-dispatch 388c8102c (213 s): soundness CLEAN (A-RECOVERED-OPEN honest; producer pairing = host's literal
  fn-ock-install over the classified-open triple; witness valid; r28 F3-F5 closed). raised 2, CONFIRMED 2: F1 nit dead
  attach-stobj arm (reads 'attach-stobj, ACL2 uses attach-stobj-table); F2 owner producer/preservation theorems lack
  teeth (store-pair assumption satisfiable as constantly nil). -> main (raw-dispatch handed off).
- r30 paged-catalog-6 f755523b6 (348 s): reader equalities + okp preservation CLEAN; raised 4 claim-gaps, CONFIRMED 4
  (no-fallback claim unproved; withdraw positive uses partial tables; msort=isort no teeth; non-okp removals missing)
  -> main (paged-catalog-6 handed off).

## HAND-OFF liaison-4 -> liaison-5 (2026-10-01 ~12:30 local, ~145 tool uses)
Tally liaison-4 reviews (raised / confirmed / rejected): r22 2/2/0, r23 5/5/0, r24 2/2/0 (+ liaison extension: macro
vacuity probe minimal-theory only), r25 5/5/0, r26 3/3/0, r27 3/3/0, r28 5/5/0, r29 2/2/0, r30 4/4/0 = 31 raised, 31
confirmed, 0 rejected. Trust-critical def-carried thread: r24 -> r25 (r24-F1 not closed) -> r28 (closed; 2 new bugs) ->
r29 (soundness clean). Tasks: t27 (liaison fix :map :base), t28 (rebased to declare2), t23b, t29b, t31, t32, t33
(+ liaison ran the hbox backfill), t30 still blocked. READYs sent: codex-rlfix2 3f747a8e6 (on dev), codex-scpfix
58a34f379 (on dev), codex-imageid e346744e8 (on dev), codex-reachseed2 7c0bec092 (batch 12), codex-genscan c6aa40479
(land with/after stage 0), codex-declare2 af569f48d (HELD until stage 0).
Runner is BI af0c83681089d902e (WAVE-STATE line 1). No Codex session is live at hand-off.
### NEXT (in order)
0. FIRST AND FOREMOST: the stage-0 READY (lane/stage-0; stage-0-3 finishing). Hard Codex review the moment it exists
   (runner BI asked: it is the gate): served path — gates without producers, early returns, wrong restorations, every
   D43-D46 claim, the unwired-to-completion list; and SPECIFICALLY verify the reclaim-swap report-writer fix
   (host/native/owner.lisp ~6258 fnn-owner-core 'fn-owner-report-writer-enter/-leave/-fault: the book
   books/owner-report-writer-entry.lisp is in the image world or the calls are gone; nothing faults before the
   handler-case).
1. After stage 0 is on dev: re-run t28 against the post-stage-0 host (declare only what it still dispatches; 0
   undeclared is def-carried's completeness precondition), fresh READY superseding codex-declare2 af569f48d.
   TASK: build/lanes/codex-declare/build/codex/t28-declare/TASK.md (+ REPORT for the per-entry classes).
2. t30 rerun (lane/codex-danglefix2 holds Codex's diff on dev 136914edf, uncommitted) after CERT-ROOTS + stage 0 clear
   the 60 closure reds (history-cold-record-cursor, snapshot-*, census-resident/-lineage, store-profile-carried,
   nntp-index-runtime chain); cert cmd in this log's t30 entries; then commit with Codex's trailer, READY.
3. Next raw-dispatch lane fixes r29 F1/F2 (and its NEXT 2 = r28-F1 raw-host symbol rule) -> fresh review r31 of the
   whole raw gate + owner row; def-carried stays trust-critical: review every change fresh.
4. paged-catalog-7 fixes r30 F1-F4 -> review.
5. t16 figure-docs after stage 0 (build/coordinator/queue/codex-t16-figure-docs-AFTER-STAGE0.md); t08 rerun +
   world.py==umbrellas fast check.
6. def-loop conversion stream: NEW RULE (coordinator): a batch lands only when EVERY converted book AND its direct
   dependents certify on hbox; blocked = HOLD (or certify in a world with the fixing branch merged, as liaison-4 did in
   build/lanes/codex-defloop-cert, branch lane/codex-defloop-cert, NOT for landing). Remaining generator gaps (t21):
   configurable step (CDDR / fn-ag-cdr), :concat with :keep / non-nil tail, two-list merge, recursive-result validation.
7. Known follow-ups: tests.test_generated_scanners fails when run in ONE process with tests.test_ledger (import-order
   pollution; passes alone/with reach_check) — fix before adding it to the Makefile fast unit list. hint_names_check
   (report-only, 48 findings at BH) flags ACL2 built-in rules like CAR-CONS — fix before strict (runner BH's note).
### Worktrees: codex-declare (ABANDONED, superseded by codex-declare2), codex-defloop-cert (cert-only), codex-danglefix
  (old t30, superseded by codex-danglefix2), codex-r-r22..r30 (read-only reviews) — removable once their branches land.
### Lessons (liaison-4): (1) run_in_background needs timeout 3600000 for Codex sessions and box attaches — the default
  30-min limit killed t29b's Codex mid-acceptance and two of my waits; (2) a bare `&` inside a Bash call kills the
  child with the shell (r29's first launch silently never ran) — always run_in_background; (3) `cmd && next; echo
  EXIT=$?` reports the FIRST failure's exit, so a failing unittest hid whether reach ran — use `;` and separate echoes;
  (4) when two owners fix the same finding (deputy2 vs def-carried-gen r16), ask the coordinator which is canonical
  before rebasing a dependent lane onto either.

## Liaison-5 log (codex-liaison-5, Opus)
- r31 stage-0 PRE-READY 136914edf..99b9f30e5 (gpt-6-astra, 714 s): raised 8 (2 bug, 6 claim-gap), CONFIRMED 8,
  rejected 0; + 2 liaison (L1 incoming-context tuple shape shifted under (fn-cp-nth 9 context) readers, dead today;
  L2 stale "stays loaded" comments in build.lisp/auth.lisp). REPORT-WRITER FIX VERIFIED (dispatches gone, swap body
  unchanged, errors propagate; no dispatched symbol of the loaded build lacks its book, 1,029 files traversed).
  No producerless gate left on init/POST/read/mux/auth. BUGS: F1 :direct cold read has no issued row/pin, fd preads
  off-lock, retirement can close it mid-read; F2 timed-out direct threads orphaned (unbounded, faults unobserved).
  Gaps: F3 D46 byte-exact/unhooked overstated; F4 deleted (not parked) pic/adopt-config host fns named as
  re-installs + PRF-1148 cites deleted test; F5 unlisted removed roots/declarations; F6 bp-design CRC0 prose;
  F7 encoding.md stale schema3 cite; F8 parked captured book edited into unresolved call. -> stage-0-3 + main.
- QUEUED after hand-off (for liaison-5): r31 review of lane/assurance-remainder 77063b220 (assurance-remainder-2
  ac725ef02035e71b3): PKT-202 / PRF-1224 books/transit-same-decision.lisp + tests/acl2/transit-same-decision-tests.lisp
  (subject = host-called transit path? teeth?). r26 cert ask met: hbox certify-20261001T154245Z-3189339 283/0 committed.
- QUEUED after hand-off (for liaison-5, TRUST-CRITICAL, right after stage 0): r32 (requester called it "r30"; r30 is
  taken by paged-catalog-6) fresh review of lane/raw-dispatch 388c8102c..b72458824 (requester a9268009b2572233d,
  findings -> raw-dispatch successor + main): (1) tools/raw_dispatch_rule.py — escapes the five rules
  NAME/NAMEVAR/MAKE/WORLD/CALL miss; CALL tracing fixpoint (params, specials, struct slots, lambda params,
  dolist/loop elements, local setq); every ALLOW/PENDING reason; derived-dispatcher and label/key-position exemptions
  (r28-F1 closure). (2) r29-F1: attach-stobj arm removed — is the absstobj-info scan sufficient (new defabsstobj teeth
  in def-carried-tests). (3) r29-F2: books/assumptions-recovery.lisp new non-vacuity constraint +
  tests/acl2/owner-retain-carried-tests (positives; removals by contrapositive) — vacuous/tautological anywhere?
  (4) Q4 prose in books/owner-retain-carried.lisp.
- stage-0 3d1ffa844 (r31 F3-F8 + L2 fixes): liaison verified F4 parks are VERBATIM (post-captured-parked.lisp holds
  the 136914edf pic runtime block byte-for-byte; auth-adoption-parked.lisp holds fnn-native-auth-adopt-config
  byte-for-byte); F8 include restored to acceptance-binding-held-gate. F1/F2 (direct cold line) still open at this sha.
- t34-testiso LAUNCHED (lane/codex-testiso from c6aa40479): root cause found by Codex — tests/test_ledger.py:22-29
  re-executes tools/ledger.py as a second module and overwrites sys.modules["ledger"]; callgraph already bound the
  first module's Sym/head, so protocol_emit's forms (new Sym) fail isinstance in old head. Fix: plain import.
- COORDINATOR: A-SBCL-INTERNALS folded into queued t16 (queue/codex-t16-figure-docs-AFTER-STAGE0.md appended).
- QUEUED after hand-off (for liaison-5): r33 review of lane/paged-catalog f755523b6..947ef73c1 (paged-catalog-7
  accab00a981232e1a): r30 F1 fn-cpl-coverp (catalog-live-links sec. 6) preserved by commit/withdraw/redecide/clear and
  carried in fn-cat$pcorr, KEYSTONES fn-cat$p-next-is-probe / -prev-is-probe (is coverage established by the creator
  and EVERY export incl. clear-keyed/load? does "is-probe" really exclude the scan on every reachable state?);
  F2 commit-generated tables; F3 msort 9-row bucket + tie-order MUTATION; F4 natp-r removal, r<len weakening
  fn-cpl-okp-of-withdraw-any-r, fn-cat-rowsp still open; NEW fast paths fn-cp-isort-of-asc/-of-desc (PRF-1226):
  equal to isort on every input the reader sees? teeth? Lane reports hbox 5/0 + 3/0.
- t34 AUDIT: diff read (tests/test_ledger.py only, -10/+4: plain `import ledger` after sys.path insert; no assertion
  changed); no other test reloads ledger. Liaison box acceptance (both orders) running.
- r32 assurance-remainder-2 77063b220 (PRF-1224 transit-same-decision; gpt-6-astra 227 s): raised 4 (3 claim-gap, 1 nit),
  CONFIRMED 4, rejected 0: F1 keystones about fn-tsd-drain-decision (no host caller, :verify-guards nil) with no
  equation to fn-owner-transit-decide nor to the host's fn-owner-step path; PRF-1224 statement says "the decision
  fn-owner-transit-decide makes"; F2 "reachable" NNTP positive is update-nth of a sub from a never-opened conn 0;
  F3 missing per-keystone removals/mutations (stringp peer redundant: prove weakened); F4 local car-of-pta-decide
  under a KEYSTONE marker -> -by-definition. No false theorem; BP :ungoverned honestly disclosed. -> main (forward).
- LIAISON ERROR: launched r33 with `( ... &)` inside a Bash call (4th liaison to do it). This time the script was
  reparented to init and Codex ran; not relaunched. Always run_in_background.
- r33 paged-catalog-7 947ef73c1 (base 3c19ce453) and r34 raw-dispatch-2 b72458824 (base 5b0191de5) LAUNCHED.
- t34 READY lane/codex-testiso d660b3d39 (stacked on genscan c6aa40479): liaison persvati rerun both orders -> only the 2 repo-state ledger failures. Codex 1320 s, 1 round. -> runner BI + main.
- r33 paged-catalog-7 947ef73c1 (gpt-6-astra): raised 3 teeth claim-gaps, CONFIRMED 3, rejected 0 (probe witnesses never assert fn-cat$pcorr + no liveness removal; coverage teeth incomplete incl. redecide/probe-of-live; asc/desc positives literal not writer-built). Logic clean (exec=isort, writers carry coverage, local disables, registry scoped). -> main.
- r34 raw-dispatch-2 b72458824 (base 5b0191de5; gpt-6-astra): raised 7 (6 bug, 1 claim-gap), CONFIRMED 7, rejected 0.
  r29 fixes clean. raw_dispatch_rule.py bypasses: F1 strip-world.lisp (after :q) unscanned + load/require not
  refused/followed; F2 package-qualified cl:funcall/cl:intern -> 0 sites; F3 defconstant/defsetf OPAQUE; F4
  setdefault keeps first defun body; F5 syntactic dispatcher derivation (dead arm); F6 allows match by function,
  CALL/WORLD/MAKE carry no symbols -> carried ban unenforced; F7 bp.lisp:464 `read` with *read-eval* under a "fixed
  names" reason. Liaison REPRODUCED F2/F3/F4 by running scan_sources on toy input (control: unqualified -> CALL+MAKE).
- stage-0 6478e2ada delta: LET -> LET* (view first) in fn-owner-finish-submission-synced + fn-hist twin: view reads the
  pre-enter state exactly as the parallel LET did (first view reads `result`, second (fn-owner-core state) of the old
  state) — equivalent; fn-orc-writer-enter is books/owner-report-capture.lisp:59. OK.
- COORDINATOR (r34): raw-dispatch-3 redesign = image traps raw-dispatched symbols; scanner = early lint. Asked for F7.
- t35-bpprofile LAUNCHED (lane/codex-bpprofile from origin/dev 2a94e8ee5; coordinator-approved host/native/bp.lisp
  exception, ONE function): explicit FN_BP_TEST_PROFILE parser, no reader; raw-Lisp test incl. "#.(error ...)" refused.
  READY only after stage 0 lands.
- t35 AUDITED (Codex 349 s, 1 round): 438cd78b2 explicit parser + raw-Lisp test (reads the shipped defuns; #. payloads refused, never signalled; cached refusal logs once). Liaison fix 1 commit: ASCII-only digits (SBCL digit-char-p accepts Unicode digits) + case. hbox test OK; interface_emit/harness_check exit 1 identical before/after (pre-existing). Pushed lane/codex-bpprofile; READY HELD until stage 0 is on dev (coordinator).
- stage-0 fc3deeecd delta: fn-owner-retire-step now cites fn-ort-* counted-drain keystones (true subject: host calls fn-ort-drain-step-counted ... t nil). NOTE: with producers-settled = nil the cited -waits-before-window-without-fenced-zero antecedent always holds -> retire always waits then ends :deadline (= master-list S9, owned by RETIRE-FENCE-2 after stage 0); the citation is honest, the served behaviour is still S9.
- r32 follow-up 278835d20 (assurance-remainder): F1 closed honestly (book header + PRF-1224 now MODEL-LEVEL, host join named OPEN for AUTHORITY-FIELD); F4 renamed -by-definition, KEYSTONE marker removed. F2/F3 = lane NEXT 0. Verified by diff.
- r35 paged-catalog-8 12874a773 (base b7a3e51f8) LAUNCHED (coordinator stream A ask: trie equality, insert/read bounds, teeth).
- r35 paged-catalog-8 12874a773 (gpt-6-astra): raised 2 teeth claim-gaps, CONFIRMED 2, rejected 0. Trie equality
  proved for any natural/order/duplicates; insertion O(depth) path copy; read O(nodes+k) (not O(k): sparse {2^64}
  = 259 calls); D26 clean. F1 cpt-corr-evidence surrogate never implies fn-cat$pcorr (corrupted NEXT entry for a
  withdrawn key passes it); F2 no duplicate-withdraw-attempt witness. -> main (lane handed off).
- r36 assurance-remainder 954572191 (vs 278835d20; gpt-6-astra): raised 2, CONFIRMED 2, rejected 0, + 2 liaison.
  r32 F2/F3 CLOSED (real NNTP positive, per-hypothesis removals + mutations x4, stringp weakening proved). PKT-370
  premise non-vacuous and = fn-cp-register-within's admission. F1 "differ on every reachable drain" needs an
  in-flight->open-connection invariant (theorem hypothesizes open conn); F2 PKT-370 positive not served-producer-built;
  L1 no producer theorem discharges fn-crb-registers-within for host-written logs; L2 specs/storage.md field 8 /
  profile-rises drift. -> lane aa0816ffd099bbab5 + main.
- r37 gate-b 1f203bf9c (base 82ded73a0) and r38 assurance-remainder f7b9d2eb5 (base 954572191: r36 closure + PKT-399) LAUNCHED in parallel.
- r38 assurance-remainder f7b9d2eb5 (vs 954572191): raised 2 (1 claim-gap, 1 nit), CONFIRMED 2, rejected 0. r36 all
  closed. PKT-399 "exactly" holds both directions given a redeeming plan; teeth complete except F1 positive built by
  unconditional fn-cfg-apply-delta (no admission/publish/replay). F2: field numbers — max-consumers is FIELD 8,
  max-credentials FIELD 11 (*fn-bs-profile-field-names*); book "field 12" and consumer-replay-bound/PRF-167 "field 9"
  wrong. LIAISON ERROR: my r36 L2 implied storage.md's "field 8" was stale; it was right (corrected to the lane).
- r39 deputy3/paged-catalog 597ebf62c (base 12874a773) LAUNCHED (deputy-3 ae1996e822f0452b5 ask).
- r37 gate-b 1f203bf9c (vs 82ded73a0; gpt-6-astra): raised 3 (1 claim-gap, 2 nits), CONFIRMED 3, rejected 0. Meaning
  unchanged (flat-view corr = old adt-corr; paged vs columnar expansions identical on the abstract side); page
  arithmetic clean at every boundary; growth: no page copy, admitted table doubling Θ(K). F1 octets ops unbounded
  per call (D27 quantum); F2 -BRIDGE naming; F3 book-scope codec enable. 13 statements' teeth table supplied.
- r39 deputy3/paged-catalog 597ebf62c (vs 12874a773): raised 1 teeth claim-gap (fn-cat$p-livep-is-live has no witness), CONFIRMED 1, rejected 0. Plan sims sound without posp (live-rowp has it); deleted scans: non-live NEXT/PREV now 0 but only liveness-gated callers, no served divergence; r35 F1/F2 closed on built states. -> deputy-3 ae1996e822f0452b5 + main.
- r39 F1 fix 0338b90ef spot-checked: cpt-livep asserts livep vs live-numberp at 1/8/2 on the writer-built probe state + two CORRUPTED removals (erase NEXT; bind dead 2) with conclusion and evidence failing; tuples coherent. (Positive still asserts the cpt-corr-evidence surrogate, not fn-cat$pcorr itself — the r35 F1 caveat, scoped to built states.)
- r40 gate-b-2 f6e996446 (vs 1f203bf9c) LAUNCHED (tree instances paged incl. fn-crow; collision check vs deputy-3's two-tree fn-crow).
- r40 gate-b-2 f6e996446: raised 3 claim-gaps, CONFIRMED 3, rejected 0 (r37 F3 survives in tree-walk.lisp:38-40; drt-t1 snapshot is a projection a wrong table resize passes; 3 new tree keystones lack witnesses). Meaning/boundaries/write-once clean; deputy-3 two-tree fn-crow compatible. -> gate-b-2 aa0987d97e41cae69 + main.
- stage-0 9ce057847 delta: fnn-log-writer-stop now answers :absent/:joined/:timeout (was NIL -> fn-ort-log-close-action :held -> every owner exit 3). Single caller (fnn-owner-log-settlement); OK. Natives s0j were red on this; stage 0 converging.
- r41 stage-0 DELTA 99b9f30e5..9ce057847 LAUNCHED (pre-READY; r31 F1/F2 status, all host changes since, READY claims, retire S9 honesty).
- r41 stage-0 delta 99b9f30e5..9ce057847 (gpt-6-astra): raised 5 (2 bug = r31 F1/F2 surviving, 3 claim-gap), CONFIRMED 5, rejected 0. F3 READY evidence lacks tested sha; F4 owner-retire.lisp host-call prose false (counted drain, always :deadline); F5 counted-drain keystones without witnesses. Delta itself clean. -> stage-0-3 + main.

## HAND-OFF liaison-5 -> liaison-6 (2026-10-01 ~15:40 local, ~135 tool uses)
Tally liaison-5 reviews (raised / confirmed / rejected): r31 8/8/0 (+2 liaison), r32 4/4/0, r33 3/3/0, r34 7/7/0,
r35 2/2/0, r36 2/2/0 (+2 liaison; my L2 field-number direction was wrong, corrected in r38), r37 3/3/0, r38 2/2/0,
r39 1/1/0, r40 3/3/0, r41 5/5/0 = 40 raised, 40 confirmed, 0 rejected. Highest value: r31/r41 the :direct cold line
(2 served bugs, still open), r34 raw_dispatch_rule's 6 bypasses (-> coordinator's image-trap redesign, raw-dispatch-3).
Tasks: t34 testiso READY (d660b3d39, stacked on genscan c6aa40479; runner holds both until stage 0); t35 bpprofile
AUDITED (lane/codex-bpprofile e97440bc7: Codex 438cd78b2 + liaison ASCII-digit fix), READY HELD until stage 0 on dev.
No Codex session is live at hand-off. Runner BI af0c83681089d902e. Stage-0 owner stage-0-3 a6b69e38199226492.
### NEXT (in order)
0. STAGE 0 READY (lane/stage-0; at hand-off 9ce057847, natives converging, no READY yet): delta review from 9ce057847
   to the READY sha with build/coordinator/queue/codex-review-stage0-READY-delta-q.md (launcher codex-review.sh
   rNN-stage0-ready <READY> 9ce057847 <that file>). Check r31/r41 F1/F2 (direct cold line) are fixed or named as known
   served defects with an owner, F3 (READY evidence names the tested sha), F4 (books/owner-retire.lisp host-call prose),
   F5 (counted-drain keystone witnesses).
1. After stage 0 is on dev: (a) codex-bpprofile: merge origin/dev, rerun `python3 -m unittest tests.test_native_bp_profile`
   on a box, READY to runner + main; (b) t28 declare rerun against the post-stage-0 host (TASK:
   build/lanes/codex-declare/build/codex/t28-declare/TASK.md; supersede codex-declare2 af569f48d); (c) t30 dangling hints
   (lane/codex-danglefix2) once CERT-ROOTS clears the closure reds; (d) t16 figure-docs WITH the coordinator's
   A-SBCL-INTERNALS decision (queue/codex-t16-figure-docs-AFTER-STAGE0.md, appended section); (e) t08 umbrella rerun.
2. raw-dispatch-3 (image traps raw-dispatched symbols; scanner = early lint): fresh trust-critical review when it lands.
3. Reviews requested by lanes arrive by SendMessage; launch each in its own codex-r-<rid> worktree (3-5 parallel).
### Lessons (liaison-5): (1) zsh: `$S:path` is a history modifier — write `${S}:path` in git show; (2) I launched one
  review with `( ... &)` (4th liaison): it happened to survive reparented to init — still never do it; (3) verify a
  field/constant NUMBERING against the project's own naming table before asserting which side is stale (my r36 L2);
  (4) a pre-READY review of a long-running lane (r31, r41) is cheap and found the served bugs early — do it while waiting.
### Worktrees added: codex-testiso (t34), codex-bpprofile (t35), codex-r-r31..r41 (read-only reviews).

## Liaison-6 log (codex-liaison-6, Opus)
- r38 follow-up 4e0ccd2b5 (assurance-remainder-3) verified by diff: F1 closed (four fn-cfg-delta-reason nil asserts
  match arct-v1..v4's deltas/generations exactly; positive relabelled ADMITTED, not published/replayed); F2 closed for
  the lane's own text (field 8 max-consumers, field 11 max-credentials); books/consumer-position.lisp "field 9" and
  PRF-167's title left for their owner (honestly stated).
- r42 gate-b-2 superseding READY ea4a68a36 (vs r40's f6e996446; on dev batch 17) LAUNCHED: paged :scalar/:generic by
  default, adt-pg-corr-set-scalar, drt-t2 two trees, lib now includes def-representation-paged (theory leak?), r40
  F1-F3 status. Questions: queue/codex-review-r42-gateb2-q.md.
- r42 gate-b-2 ea4a68a36 (vs f6e996446; gpt-6-astra ~3 min): raised 3 claim-gaps, CONFIRMED 3, rejected 0 (+1 liaison
  nit). All 3 = r40 F1-F3 UNCHANGED (tree-walk.lisp:38-40 local book-scope codec enable; drt-t1 snapshot projection —
  a mutant with one extra rows resize passes; the 3 paged tree keystones have 0 test files). Liaison: new
  adt-pg-corr-set-scalar also 0 witnesses. Delta clean: scalar/generic meaning kept, :paged nil = old events, two-tree
  cursor threading right, write-once both trees, drt-pay witness = creator image; only production instance fn-crow
  (already paged). -> main (forward to gate-b-3).
- (post-hand-off) r42 msgid-linear-hash-2 a02af2d52 (vs efaf27dd2): raised 3 claim-gaps, CONFIRMED 3, rejected 0. Split
  refinement + STUCK semantics clean (STUCK named, refuses by name, needs an operator consumer at the switch). F1
  "three pages whatever the table holds" false: fn-mlh-grow resizes the page-pointer array +1 per split (O(P) copy);
  F2 fold step O(R) (len/nth) -> O(R²); F3 new keystones lack teeth. Lane accepted all (its NEXT 0).
- r43 stage-4 6806a5610 (base efaf27dd2) NOT launched: coordinator assigned it to liaison-6 a7f91a72963996bbf. Prepared
  questions at build/coordinator/queue/codex-review-r43-stage4-q.md. Liaison-5 tally final: 12 reviews, 43/43/0.
- NUMBERING: liaison-5 ran its own "r42" = msgid-linear-hash-2 a02af2d52 after hand-off (3/3: page-pointer array +1
  resize O(P^2); fold step O(R); teeth) — my r42 is gate-b-2. My duplicate msgid2 run (r43-msgid2) STOPPED unfinished
  at the coordinator's word. Next free id: r45.
- r44 stage-4 6806a5610 (vs efaf27dd2; PRF-1227 dense map; gpt-6-astra ~5 min): raised 4 (1 cost bug, 3 claim-gap),
  CONFIRMED 4, rejected 0. F1 fn-dmap$c-alloc doubles the page array + grows pt hash in one put (Θ(pages)/step, D27);
  "N/256" comment wrong for sparse groups; pages never freed. F2 escape-empty prose only (sentinel 2^64-1, count
  unbounded, no corr carries a bound). F3 dmap keystones no literal teeth. F4 cpt-links-ok 1..n misses an off-range
  lnext binding (construction: key 9) — liaison-5's worry, confirmed. Logic clean (semantics exact, owner check sound,
  attachment reaches the host commit). -> stage-4 a1262024acde6d985 + main.
- r45 stage-0 PRE-READY 15483810d (stage-0-4 af5a75a4294bfebb8; vs 9ce057847; questions queue/codex-review-r45-stage0-pre-q.md):
  raised 3 (2 bug = r31 F1/F2 still live owner.lisp:4213/4401, 1 nit), CONFIRMED 3, rejected 0, + 2 liaison. Codex's
  sub-claim "LANEDUMP does not disclose" PARTLY wrong: coordinator lanedumps/stage-0-3.md "Known, not this lane" names
  r31 F1/F2; the worktree LANEDUMP (stale, stage-0-2's) does not. F3 current.md:110 renders old fn-ccp-publish subject.
  L1 assumptions-pgs-host-io.lisp:172 "raw definition not yet present" stale; L2 worktree LANEDUMP stale. Clean:
  reconfigure = 7aad body + proposal clear (no served consumer); fill-frame meets all A-PGS-HOST-IO constraints (raw
  redefinition, same as list realizer); .retire- sweep safe under writer flock; counted-drain teeth complete; chunk
  stubs scoped. -> stage-0-4 + main.

## HAND-OFF liaison-6 -> next (2026-10-01 ~21:20 local, ~80 tool uses; yielded at ember's question while idle-waiting)
Tally liaison-6: r42 gate-b-2 3/3/0 (+1), r44 stage-4 4/4/0, r45 stage-0 pre-READY 3/3/0 (+2) = 10 raised, 10
confirmed, 0 rejected (one Codex sub-claim in r45 partly wrong: disclosure exists in lanedumps/stage-0-3.md).
r43-msgid2 stopped (duplicate of liaison-5's). No Codex session live. Next free review id: r46.
State at hand-off: dev 22c904e26 (stage-4 + msgid2 landed); lane/stage-0 3537b158c (stage-0-4 af5a75a4294bfebb8,
natives running, no READY); stage-4's r44 fixes on lane/ccf-dmap (F2/F1 scoped at ea07f63e9; F4/F3 next);
assurance-remainder-4 at 2036f65b7 (no READY yet); gate-b-3 a17faad2756da962b owns r40/r42 F1-F3.
### NEXT (in order)
0. STAGE 0 READY: delta review from 15483810d (r45's sha) to the READY with
   queue/codex-review-r45-stage0-pre-q.md (or the base READY-delta file): check (1) r31 F1/F2 named as KNOWN SERVED
   DEFECTS owned by COLD-READ-OWNERSHIP, S9 by retire-fence; (2) evidence bound to the READY sha, per-module counts,
   run ids; (3) no keystone cited without witnesses; plus r45 F3 (current.md:110 regen) and L1 (assumptions-pgs-host-io
   :172 stale comment).
1. After stage 0 on dev: codex-bpprofile e97440bc7 (merge dev, rerun tests.test_native_bp_profile on a box, READY);
   codex-testiso d660b3d39 lands with genscan c6aa40479; declare2 rerun (t28 TASK in build/lanes/codex-declare);
   t16 figure-docs; t08 umbrella; t30 dangling hints after CERT-ROOTS.
2. Reviews as READYs arrive: assurance-remainder-4 (2036f65b7+: PRF-1228 PKT-217 over the log crash model, Q3h FNLS
   guard chain), ccf-dmap (r44 F3/F4 closure), gate-b-3 (r40/r42 F1-F3), raw-dispatch-3 (trust-critical, fresh).
### Tool: scratchpad watch.sh (refs vs a saved baseline) — the per-window snapshot I used first missed changes
  that landed between windows; diff against a persistent baseline instead.

## Liaison-7 log (codex-liaison-7, Opus)
- Start: dev 22c904e26; lane/stage-0 3537b158c (only a dev merge since r45's 15483810d; no READY). No Codex live.
- r46 assurance-remainder-4 2036f65b7 (vs 4e0ccd2b5: PRF-1228 PKT-217 over the log crash model; Q3h FNLS guard chain)
  and r47 gate-b-3 e61ad6d88 (vs ea4a68a36: two-level page table, r37 F1 bounds, r37/r40 F3 codec-in-hints) LAUNCHED
  pre-READY in parallel. Questions: queue/codex-review-r46-assurance4-q.md, -r47-gateb3-q.md.
- r46 assurance-remainder-4 2036f65b7 (vs 4e0ccd2b5; gpt-6-astra 259 s): raised 6 claim-gaps, CONFIRMED 6, rejected 0.
  F1 native recover interns via fn-ssr-intern-step (io.lisp:1581) + opens via fn-store-sn-recover-rows, not the book's
  fn-srs-intern-step/fn-store-sn-recover — no bridge; F2 acked-prefix premise has no producer and is missing from
  PRF-1228's not-discharged list; F3 positive log seeded (fn-lg-log + recover), not writer-published; F4 removals for
  2/10 conjuncts; F5 "O(1) per article" false (fn-rcl-verdict-heldp list walk per article -> quadratic); F6 "bounded by
  profile" is no D27 quantum (unyielding walk under owner-serialized; inspector-binding nil, never set). Clean: Q3h
  guard work, Makefile, MODEL-LEVEL. -> main (forward to assurance-remainder-5).
- r47 gate-b-3 e61ad6d88 (vs ea4a68a36; gpt-6-astra 418 s): raised 6 (1 cost bug, 4 claim-gap, 1 nit), CONFIRMED 6,
  rejected 0. F1 directory doubles in one call past 4,194,304 rows (def-representation.lisp:469-470, Θ(NP/64)) vs
  paged:1986 "bounded by the record, not by the count" (liaison pre-read found the same); F2 pages-bounds are capacity
  only, profile link prose -> r37 F1 open; F3 corr strictly stronger (adt-pg-dokp) under unchanged text; F4 no teeth on
  view/dadd/bounds keystones (tests: renames only) + inherited tree/scalar gaps; F5 drt-t1 snapshot omits directory
  (extra resize mutant passes); F6 nit three codec defuns enabled on the chain (liaison checked: the arena disable is
  not on tree-walk's chain). -> main (SendMessage to a17faad2756da962b failed: not in this session; main forwards).
- ccf-dmap ea07f63e9 (r44 F1/F2 scoping) verified by diff: catalog-dense-map.lisp header now states Theta(pages) per
  allocating put, sparse groups = G pages, never freed, OPEN D27; escape NOT proved empty (count unbounded, >= 2^64-1
  lands there). Honest. r44 F3/F4 still to come from the lane.
- IDS (coordinator, after rotation): stage-0-5 ac872778c25c20db7, catalog-commit-flat-2 ad69b3840f9779026, gate-b-4
  a579239cb5d43d332 (r47 forwarded by main), assurance-remainder-5 a4463378fd9c1b46b (r46 sent direct), runner BJ
  a493597942120e8ba. Pre-rotation ids are dead.
- stage-0 3fbc68b2a (stage-0-5, not READY) verified by diff: owner.lisp comments only — r31 F1/F2 named KNOWN SERVED
  DEFECTS at the direct line + cold-issue, owner COLD-READ-OWNERSHIP (READY check 1 met in source); r45 L1 fixed
  (assumptions-pgs-host-io names extent.lisp fn-pgs-fill-frame); fn-pgs-frame-put :kinds ((base natp)); r45 F3 done in
  3537b158c. No behaviour change.
- gate-b-4 READY 807747dd7 (liaison diff review, no Codex; coordinator ask): r47 F1 CLOSED IN THE LIBRARY
  (adt-pg-append-step-bound correct + positive/3 removals; reserve-c only grows to 1+floor(n/(R*T)) >= ceil(NP/T));
  NOT on the served path: no caller of fn-crow-reserve, and CLEAR resizes directories to 0, so fn-cat$p-clear-w /
  clear-keyed drop a reservation (stated in book; NEXT 1 -> catalog-commit-flat-2: reserve at open and after clear;
  suggested CLEAR keep the width). F2 scoping honest; F3 stated; F5 fixed (whole-state witness incl. directory +
  resize mutation); F6 fixed. -> main + runner BJ: OK to land.
- r48 catalog-commit-flat-2 READY 6aee97795 (vs dev 22c904e26, gate-b files excluded; gpt-6-astra 398 s): raised 6
  (2 cost bug, 3 claim-gap, 1 nit), CONFIRMED 6, rejected 0. F1 fn-cat$p-reserve no caller (served open/clears never
  reserve); F2 eql cells hash-table rehash Θ(cells) per put, unstated; F3 fn-mlh-grow +1 pointer copy now on commit
  (= r42-msgid2 F1); F4 no teeth for cells/OLEN boundary (catalog-paged-tests unchanged); F5 must-fail-checked used as
  removal, saturated-is-not-indexed no positive; F6 nit 14 sim hyps len->OLEN (liaison counted). Coordinator Qs
  answered by liaison reading: equalities exact; :mpx-saturated named refusal; STUCK on the health line; O(R²) fold only
  in the other-key fallback, not the recovery path; fn-mlh-wfp O(1). Codex sub-claim corrected MY brief: EQL compares
  integers by value (no bignum miss). -> main (for ccf-3), runner BJ (OK to land), ccf-2.
- stage-0 c2a4baad8 (not READY) diff-read: no host change; fn-omr-checkpoint-file-words "none" -> "absent" (= live
  status word); two test fixtures follow real callees. s0l at 3fbc68b2a: most modules green; state_checkpoint 32 fail
  (fixed here), over_pins 0/4 routed to paged-catalog natives (served reader not on catalog cursor arm) — READY must
  name over_pins as a known served defect with that owner.
- r49 assurance-remainder-5 delta 2036f65b7..f1a3d968e (r46 fixes; gpt-6-astra 274 s): raised 3 claim-gaps, CONFIRMED 3,
  rejected 0, + 1 liaison. r46 F1/F2/F3/F5/F6 closed (subject = io.lisp seed/:resident exactly; decodedp dropped by
  fn-brlc-open-ok-implies-decoded; writer-built, ACKED via finish-one); F4 5/9 removals. F1 csi/tears-p/open-okp/
  configured-before unwitnessed (configured-before: one positive is not redundancy); F2 "no payload read" false
  (tomb-length reads bytes); F3 chunks-are-one-step tested via test-local brlct-chunks-a (liaison found: not the
  subject) + rows projection only. Note: 24b003d48 adds a guard (not verify-guards only). -> lane + main.
- assurance-remainder-5 97637bad4 verified by diff: r49 F2 closed (prose names the tomb read + catalog-miss fallback);
  F3 closed (fn-brlc-chunks-intern made an executable stobj defun, test calls it, whole accumulator, true-list-listp,
  (r1 . 5) removal with :bad vs placed). r49 F1 (4 conjuncts) = successor's NEXT 0; delta review HELD until it lands.
- r50 catalog-commit-flat-3 READY 330c859ec (vs 6aee97795; fn-mlh two-level directory; gpt-6-astra 327 s): raised 2
  claim-gaps, CONFIRMED 2, rejected 0 (liaison pre-read found F1 independently). Logic clean: page-level scan /
  find-empty = logical loops at every mbe site (absent=0, bit-60 strip, tag-0 empty, 2-page probe bound); keystones
  unchanged; fn-mlh-pgsp weakened to natp (wfp O(1)). F1 "O(1) per split" unscoped in commit subject + :1786 "the open
  reserves" false (fn-mlh-reserve only in a test); first doubling at 8,388,608 rows copies 256 + 256 headers; 63 is
  prose, no cost theorem. F2 no teeth for the page-level equalities. Pre-existing: :2449 "THE STEP IS BOUNDED" vs O(R²)
  fold. -> main + runner BJ (OK to land).
- r51 served-incremental-1 READY 85c5d5315 (vs stage-0 c2a4baad8; SERVED; gpt-6-astra 490 s): raised 5 (4 claim-gap,
  1 nit), CONFIRMED 5, rejected 0. Replies EXACT (whole-result equalities under V + freshness; RFC empty-group form,
  420/421/422/423/430 branches checked); subjects host-called (owner.lisp:4161 -> ... -> fn-scr-command -> -cat
  dispatcher; keystone over fn-ovw-expanded effects); dispatcher explicit, :live report-only. F1 OVER<msgid> "O(1)" =
  flat in N only (seq-list reverse+walk, membership walk); F2 LIST flat only at top view (older pinned view: G*D scan);
  F3 reader teeth partial; F4 relay transfer equalities 0 witnesses (book-only, not host-called, verify-guards nil);
  F5 nit :live stale. -> main (relay to lane) + runner BJ (OK after stage 0).
- stage-0 63bf81a9e (not READY; SERVED host io.lisp fnn-state-checkpoint-stage) liaison-verified: stage unlinked on
  fnn-os-error AND fnn-store-io-refusal (owner-stopping yield), then re-signal; condition types disjoint (both direct
  error subtypes) so neither clause dead; fd closed by write-staged-at's unwind-protect before the handler; O_EXCL +
  pid/random name = own file only. Residual (nit): any other error type (fnn-fault) still leaves the stage to the sweep,
  as does death. edae84967 fixture-only. s0n: 11/13 modules, over_pins routed.
- r52 stage-0 PRE-READY delta 15483810d..1c9b507fd (first-parent only; gpt-6-astra 265 s): raised 3 (1 bug, 1
  claim-gap, 1 nit), CONFIRMED 3, rejected 0. F1 fnn-state-checkpoint-stage os-error clause covers the O_EXCL open:
  EEXIST -> unlinks a stage not created by this attempt (low probability; LIAISON ERROR: my 63bf81a9e note above said
  "own file only" — wrong); F2 stage-0-5.md "see the READY below" dangling + state_checkpoint not re-run since
  63bf81a9e; F3 nit assumptions-pgs-host-io claims direct pread (still forward, extent.lisp:1163 list/put). READY
  checks 1-3 met at 1c9b507fd. -> stage-0-5 ac872778c25c20db7 + main.

## HAND-OFF liaison-7 -> next (2026-10-01 late, ~136 tool uses)
Tally liaison-7 (raised / confirmed / rejected): r46 6/6/0, r47 6/6/0, r48 6/6/0, r49 3/3/0 (+1), r50 2/2/0,
r51 5/5/0, r52 3/3/0 = 31 / 31 / 0. Plus liaison diff reviews: gate-b-4 807747dd7 (F1 closed in library, not on served
path), ccf-dmap ea07f63e9, assurance-remainder-5 97637bad4, stage-0 3fbc68b2a/c2a4baad8/edae84967/63bf81a9e.
Liaison errors: (1) logged 63bf81a9e "own file only" — r52 F1 showed the EEXIST path; (2) a SendMessage to a handed-off
lane id RESUMES it (ccf-2 woke and edited its lanedump) — after the rotation, route lane messages via main unless the
coordinator names a live id; (3) my r48 brief wrongly claimed EQL misses bignums (EQL compares integers by value).
IDS (coordinator, post-rotation): runner BJ a493597942120e8ba; stage-0-5 ac872778c25c20db7; gate-b-4 a579239cb5d43d332;
assurance-remainder-5 a4463378fd9c1b46b; catalog-commit-flat-3 and served-incremental-1 via main. No Codex session live.
Next free review id: r54 (r53 used after hand-off; see below).
State: dev 136712317 (batch 20: gate-b-4 + ccf-2) and batch 21 (ccf-3 330c859ec) landing; lane/stage-0 1c9b507fd, no
READY yet (r52 sent; expect F1 handler fix + a state_checkpoint rerun + the READY).
### NEXT (in order)
0. STAGE 0 READY: review ONLY the delta from 1c9b507fd to the READY sha (codex-review.sh r53-stage0-ready <READY>
   1c9b507fd <questions>); check r52 F1 fixed (unlink only after a successful create), F2 (READY binds evidence to the
   tested sha, state_checkpoint rerun at/after 63bf81a9e, known defects r31 F1/F2 + S9 + over_pins with owners), F3.
   READY checks (1)-(3) were met at 1c9b507fd (r52 Q1/Q2/Q4).
1. After stage 0 is on dev: codex-bpprofile e97440bc7 (merge dev, rerun tests.test_native_bp_profile on a box, READY to
   runner BJ + main); codex-testiso d660b3d39 with genscan c6aa40479; declare2 rerun (t28 TASK in
   build/lanes/codex-declare); t16 figure-docs; t08 umbrella; t30 dangling hints after CERT-ROOTS.
2. assurance-remainder-5's successor: delta review when its NEXT 0 lands (the 4 unwitnessed keystone conjuncts: csi,
   tears-p, open-okp, configured-before — each a weakened theorem or a counterexample); base 97637bad4.
3. Fix-forward follow-ups to watch for (no review yet): ccf-3 successor (r48 F1/F2/F4/F5, r50 F1/F2, keep-width CLEAR +
   reserve wiring); gate-b-4 NEXT 2 teeth (batched cleanup per coordinator); served-incremental-1 r51 F1-F5.
4. raw-dispatch-3 (image traps) when it lands: fresh trust-critical review.
### Tools: scratchpad watch.sh (persistent baseline) — but a stage-0-only loop (`git rev-parse origin/lane/stage-0` vs a
  saved sha, 30 s) is quieter; READYs from other lanes arrive by message.

## Liaison-8 log (codex-liaison-8, Opus)
- Start: dev dd76ea5e6; lane/stage-0 still 1c9b507fd (no READY; watching). No Codex live.
- Coordinator ask: served-incremental-2 f16221f01. r53-si2-item5 (a661ebe98, fn-mlh-build-tail; base ce30977e0) and
  r54-si2-item1 (PRF-1230, commits 4bad5f24d 00cd55e2e 05e0ca101 8f374243b; base 136712317) LAUNCHED in parallel.
  Liaison pre-read item 5: keystone body matches build-from step for step; BUT r50 F1 still stands: fn-mlh-reserve
  has no caller outside tests/acl2/msgid-linear-exec-tests.lisp:352, prose at msgid-linear-exec.lisp :15/:256/:1787/
  :2066 says the open reserves.
- (after hand-off note) stage-0 ca5550b3a verified: r52 F1 closed (fnn-write-staged-at :unlink-on-failure inside the
  unwind-protect after the O_EXCL open — a failing open unlinks nothing; caller unlinks only when WRITTEN); also covers
  other error types now. r52 F3 closed (list/put path described, pread forward). Remaining for the READY: F2.
- r53 served-incremental-2 f16221f01 (lane commits only, base 136712317) LAUNCHED at runner BJ's ask. Next free: r54.
- r53b = liaison-7's leftover codex-r-r53-servedinc2 (f16221f01 vs 136712317): died at 20:12, no FINDINGS; superseded.
- r53-si2-item5 a661ebe98 (gpt-6-astra 440 s): raised 2 claim-gaps, CONFIRMED 2, rejected 0. Logic clean (whole mv
  equality over the :exec; bodies identical; guards; unreachable-in-composition recorded at catalog-logic:3823 /
  PRF-1037, host key traces agree). F1 no teeth for fn-mlh-build-tail (no test names it; manifest has no test book);
  F2 r50 F1 still open (fn-mlh-reserve only in tests; open never reserves; clear shrinks to 0). -> main: OK to land.
- r54-si2-item1 try 1 failed "model at capacity" (242 s); relaunched.
- r55-stage0-delta 1c9b507fd..ca5550b3a launched (LIAISON SLIP: launched with a bare & by mistake; orphan pid tracked
  with a kill -0 loop). Liaison read of ca5550b3a: F1 fixed — open precedes unwind-protect (failing open unlinks
  nothing), unlink after close only when not DONE; caller unlinks only when WRITTEN; SIGKILL fault leaves the stage
  (no unwind) for the sweep; F3 prose matches. stage-0-5.md still says "see the READY below" (r52 F2 open; s0o at
  63bf81a9e, not the head).
- r53 served-incremental-2 READY f16221f01 (lane commits only; gpt-6-astra): raised 3 claim-gaps, CONFIRMED 3,
  rejected 0, + L1 liaison. Item 5 correct (build-tail = build-from whole result under natp i; mbe :exec; other-key
  unreachable natively). F1 item 1 no manifest at any candidate; F2 PRF-1230 teeth partial + owner teeth book blocked by
  PRE-EXISTING arity bug owner-advance-carried-tests:159 (fn-own-sub-make 4 of 5 args; on dev + stage-0; Makefile root
  -> CERT-ROOTS); F3 no tests of the cursor equality. L1 equality only under fn-snt-relation, host carries
  fn-cst-relation: on reconfigured nodes only "no old staging lost" proved (*pdt-bad-cap* stages where reference
  refused) -> coordinator ruling. -> runner BJ (item 5 OK after stage 0; item 1 after manifest + ruling) + main.
  UPDATED TALLY liaison-7: 34 raised / 34 confirmed / 0 rejected (+2 liaison). Next free id: r54. NEXT unchanged
  (stage-0 READY delta now from ca5550b3a: only r52 F2 remains).
- (coordinator) r53 DUPLICATED liaison-8's own review of served-incremental-2; L1 ruled by the coordinator. liaison-7 stopped here; liaison-8 owns the channel and the review numbering.
- r55-stage0-delta 1c9b507fd..ca5550b3a: raised 0 (clean; liaison read agrees). r52 F1 FIXED, F3 FIXED. Residual
  (pre-existing): named non-os fault at staged-durable / close error leave the stage to the sweep. READY must still
  bind natives to a sha including ca5550b3a (s0o ran at 63bf81a9e). -> main.
- r54-si2-item1 (retry; PRF-1230): raised 2 claim-gaps, CONFIRMED 2, rejected 0. Lane's Q (unconfigured gate scope)
  ACCURATE: host invariant gives fn-cst-relation not fn-snt-relation; staging-where-reference-refuses covered by
  fn-cst-deferred-linkp preservation; Codex construction (cap 20 -> undertake 5/release -> cap 2) = non-corrupt
  divergence fixture. F1 teeth gaps (no topic store witness; removals consumer-only; owner book red, no retention
  / idrp witness; not stated in PRF-1230); F2 retention gate also scans all releases (O(P+R+bindings)). Notes: idrp
  grant theorem restated to pdc; fn-sn-statep guard still per call (named). -> main: OK to land after stage 0.
- stage-0 ad5de4c94 (diff-read): drops a local disable of fn-cne/fn-cae-event-shape (runes gone with D46's revert);
  comment-only otherwise. Fine.
- r56 evidence-out a0ff1fc73 (coordinator light ask; gpt-6-astra 364 s): raised 11 (10 bug, 1 claim-gap), CONFIRMED 11,
  rejected 0. Readers verify hashes on object reads (good) BUT F1 local working-tree file shadows the index hash
  unchecked and counts certified_archived; F2 unreadable object swallowed -> older green wins; F3 cut_release /
  cite_check accept index rows by name; F4 existing objects never verified (store_object, rsync --ignore-existing,
  tar --skip-old-files); F5 no fsync; F6 index RMW race; F7 index-tree --write indexes without archiving; F8
  materialize trusts existing plain file; F9 fetch skips present objects; F10 sync --add drops exit 3 +
  EvidenceUnavailable uncaught; F11 non-hex 64-char hash path traversal. -> main: fix F1-F4/F7/F11 + verify --archive
  + index-tree at the frozen sha BEFORE the history rewrite.
- r57 si-4 configured iff (0cff0a3cb) and r58 si-4 PRF-1231 withdrawal index (a30cc0e03) LAUNCHED (coordinator ask).

## Liaison-9 log (codex-liaison-9, Opus; successor to liaison-8, which died at the usage limit)
- Start: dev 1ada049f1; lane/stage-0 afc91ca40. No Codex exec live. r57/r58/r59 had completed (FINDINGS on disk), untriaged.
- stage-0 delta ca5550b3a..afc91ca40 diff-read: CLEAN (catalog-paged drops disable of the gone fn-cne/fn-cae-event-shape
  runes; fixtures to the 11-arg fn-record-make, records-shape.lisp:528; ledger.md line shifts). -> main: OK to land.
- r57 si-4 PRF-1230 configured iff (0cff0a3cb vs a30cc0e03): raised 1 nit, CONFIRMED 1. Both directions sound; hyps =
  host-carried cst-relation + :reserved + literal gate conjuncts; held/hstxa discharged by psrv kinds lemmas. F1 summaries
  :33-36/:200-204 drop the kind/projection restriction (duplicate-bootstrap construction).
- r58 si-4 PRF-1231 withdrawal index (a30cc0e03 vs f16221f01): raised 3 (2 claim-gap, 1 nit), CONFIRMED 3. F1 no removal
  witness for fn-wix-existing-action-cat itself; F2 fn-wix-refresh unbounded per call (full rebuild on tlock rewrite; D27,
  owed before wiring); F3 header counts the uncalled fn-owner-existing-action-buffer as per-POST.
- r59 si-4 PRF-1232 NEWNEWS (8ed54cb4e vs 0cff0a3cb): raised 3 (2 claim-gap, 1 nit), CONFIRMED 3. Byte equality clean.
  F1 lines-at-most-q cited as an article-visit bound; F2 no teeth for fn-nnw-scan-nil-past-bound / residual removal;
  F3 PRF prose on :none horizon and tombstone probe scope wrong. Wiring notes: arena not pinned across quanta; wildmat/
  group selection unquantized. -> main (all 7, one message).
- STAGE 0 ON DEV 89e0f4f7e (batch BK).
- codex-bpprofile: merged dev -> 72bd9269e (pushed); hbox tests.test_native_bp_profile 1/1 OK. READY -> runner BK + main.
  Runner BK took it into batch 23 together with codex-genscan + codex-testiso (their held READYs).
- t08 (umbrella drift) rerun at 72bd9269e (= dev 89e0f4f7e + bpprofile): hbox `tools/extract/world.py --check` 0, tls_check 0.
  No drift after stage 0. The proposed fast check already exists (Makefile check list; hbox_native step world-check). CLOSED.
- codex-declare2 rerun (liaison, no Codex): stage 0 declared 30 of the lane's 32 entries with identical class/kinds
  (host/interfaces.lisp ~5026 block). The other 2 (fn-cad-action-kind, fn-cado-result-action) are dispatched only by
  the parked host/native/auth-adoption-parked.lisp. Lane reduced to Part B (interface_emit refuses :raw-with (:carried)
  while any dispatch is undeclared, + test): 35316c5a7 merge, ff0879c82 drop. Box check running.
- t16 figure-docs LAUNCHED (Codex, worktree build/lanes/codex-t16, lane/codex-t16 from 89e0f4f7e). TASK reduced to
  M9/M10 truth, A-SBCL-INTERNALS move (runtime-collector unloaded after stage 0, build.lisp:578-589), fn-rov decision row.
  The MiB pin was dropped as ungrounded (r12 FINDINGS are gone with the removed worktree).
- t08: see above. t16 AUDITED: Codex 1166 s, 1 round. It stopped correctly on a scope conflict (the generated counts block
  24->23 fell outside its scope); the liaison regenerated it (resource_contract --write). Claims verified (owner.lisp:4400
  per-miss make-thread; join-thread with timeout leaves the thread). D47 claimed. READY lane/codex-t16 d48afee4d -> runner BK.
- r60 raw-dispatch-3 f7757bba7 (def-carried requirement table; coordinator priority; 325 s): SOUNDNESS CLEAN. Raised 1
  nit, CONFIRMED 1, rejected 0 (refusal priority with two failing opens). Hardening note: an unknown kind is
  default-allow (unreachable). Liaison pre-read agreed (fn-cd-problem:791 subsumes the deleted atom check). -> main.
- r61 evidence-out-3 41ec96a81 (re-check of r56 F1-F11 + glob drop coverage Q7) LAUNCHED (coordinator).
- t30: on dev 89e0f4f7e, hint_names over the 2 books leaves 1 finding:
  admission-semantic-census-prefix.lisp:161 FN-RCCAP-ACTUAL-RESIDENT-OFFER-ESTABLISHES-SAME-MAPPED-ROW. consumer-
  publication-budget's hint is now valid (D46 restored fn-cpe-is-disjoint-...), so danglefix2's half of that book is
  obsolete and wrong. Pending: the census include (danglefix2's other half) needs a cert of the census chain.
- r61 evidence-out-3 41ec96a81 (vs a0ff1fc73): raised 11 (9 bug, 2 claim-gap), CONFIRMED 11, rejected 0. The REWRITE is
  BLOCKED: F11 history_blobs lacks --full-history (reproduced: 3 evidence blobs missing from the default walk); Q7 glob/
  regex drop entries are not expanded (3 versions of planning/backlog-2026-09-25.md, 4b897170/99495a67/b9328104, are in
  no ledger); F5 verify matches by filename (shard not checked); F8 completeness evidence uncommitted and stale. Plus F1
  fsync swallowed, F2 cite_check/check_scaffold local shadow, F3 refused==unavailable, F4 zlib.error escapes
  (reproduced), F6 lock under the cache dir, F9 chain_schedule, F10 manifests check name-only. r56: F1/F2/F7/F8/F10/F11
  closed; F3/F4/F5/F6/F9 partial. -> main.
- r62 served-incremental-5 56b82e7ee (vs 89e0f4f7e, 7 lane commits; SERVED): raised 4 claim-gaps, CONFIRMED 4, rejected
  0, + L1. Tag proved bit-identical (whole result, all strings); transfer wiring whole equality under host-maintained
  relations; outcome codes unchanged. F1 "one probe" comment false (W withdrawal walk, raw-list fallback, refresh
  rebuild); L1 (equal arts (fn-own-view-raw view)) is O(1) only if both are the same object; F2 r51 F3 still partial (LIST
  freshness/statep removals, no mutations); F3 live-owner keystone has no literal-antecedent witness; F4 no tests of
  blake3-string / msgid-tag-exec. -> main: OK to land.
- t36 retain-disjoint (coordinator ask; Codex 510 s, 1 round; lane/codex-retain 033054e60 from 89e0f4f7e): fn-retain-statep's
  pin/release disjointness goes through an enabled nonrecursive mbe wrapper fn-retain-ids-disjointp (:logic = the old
  conjunct exactly; :exec = a local fn-keyset hash set when R >= 8, else a walk); whole-result equality theorems for both
  arms. Teeth: reached positives (admit/release) in both arms, corrupted overlap in both, labelled mutation. hbox:
  100k old conjunct 144.7 s -> full recognizer 0.065 s/call, but 44 MB consed per call (temporary hash table; noted).
  AUDITED (diff in scope). Dependents cert (26 direct + retention-tests) on hbox running.
- t36 registry: PRF-173 carries fn-retain-ids-disjointp with the coordinator's scope sentence (d874158f0 on lane/codex-retain).
- t37 retain-noalloc LAUNCHED (Codex, same worktree build/lanes/codex-retain, on top of d874158f0). Investigate first:
  with-global-stobj / epoch stamping / carried sorted ids. Stop with evidence if none works without a trust tag.

## HAND-OFF liaison-9 -> next (2026-10-02 ~02:10Z, ~155 tool uses)
Tally liaison-9 (raised / confirmed / rejected): r57 1/1/0, r58 3/3/0, r59 3/3/0, r60 1/1/0, r61 11/11/0, r62 4/4/0
= 23 / 23 / 0 (+1 liaison note, r62 L1). Tasks: t16 AUDITED + READY (d48afee4d; liaison regenerated the counts block);
t36 AUDITED (READY pending cert); declare2 rerun READY (ff0879c82, liaison); bpprofile READY (72bd9269e); t08 CLOSED
(no drift; check already wired); stage-0 delta verdict clean.
NEXT FREE REVIEW ID: r63.
LIVE CODEX: none. t37 DONE: no admissible option (with-global-stobj needs state; doc + REPL error in build/lanes/codex-retain/build/codex/t37-retain-noalloc/REPORT.md); nothing committed; -> main.
PENDING:
0. t36 LANDED-READY: lane/codex-retain 74810d36d -> main (cert certify-20261002T020107Z-3870871, 169/0, manifest
   committed; ledger/cv/reach OK on persvati after the dev merge). Nothing pending unless the runner reports a red.
1. raw-dispatch-3 TRAP READY (033136411, "THE TRAP: fnn-install-raw-dispatch captures each raw-dispatched function
   object..."): fresh trust-critical review when its READY arrives (r60 covered only the table, f7757bba7).
2. evidence-out-4 re-review (GATES THE HISTORY REWRITE): re-check r61's F1-F11 + Q7. Must see: --full-history in
   history_blobs; glob/regex drop entries expanded via `git log --all -m --no-renames --raw`; the 3 backlog blobs
   (4b897170, 99495a67, b9328104) archived and read back; canonical-shard check in verify; zlib.error caught; a pinned,
   committed completeness summary at the frozen ref set. Question file template: scratchpad q/r61-evidence-out3.md
   (copied below as the r61 REVIEW.md in build/lanes/codex-r-r61-evidence-out3/build/codex/r61-evidence-out3/).
3. Served wiring READYs (SERVED-INCREMENTAL-WIRING: PRF-1230/1231/1232 host wiring; owed per r58 F2 a bounded
   fn-wix-refresh, per r59 the arena pin across quanta) and cold-read-ownership: full Codex reviews.
4. t30 dangling hints: on dev, hint_names over the 2 books leaves 1 finding (admission-semantic-census-prefix.lisp:161).
   lane/codex-danglefix2's consumer-publication-budget half is now WRONG (D46 restored fn-cpe-is-disjoint-...): drop it,
   keep the census include, cert the census chain, then READY. Low priority.
5. Batched cleanup candidates (book-only teeth): r57 F1, r58 F1/F3, r59 F1-F3, r62 F2-F4.
Worktrees added: codex-t16, codex-retain, codex-r-r60..r62. codex-declare2 and codex-bpprofile are done once landed.
LIAISON NOTE: zsh gotcha: `echo ====` fails (=word expansion). farm.py roots go without .lisp, and a $VAR list needs a
--recertify-from file.

## Liaison-10 log (codex-liaison-10, Opus; successor to liaison-9)
- Start 2026-10-01 22:20 EDT: dev 6d50e45b5 (origin). No Codex live. evidence-out-4 has 7831c93d0 (23 repro tests) +
  28e18380c (r61 F1-F11 fixes), completeness run in progress (build/ev4/complete-1.txt lists MISSING rows): no READY yet.
- r63-rd3-trap LAUNCHED: lane/raw-dispatch-3 0702840c0 vs 6d50e45b5 (focus 033136411 THE TRAP, db542a2b5, c62875cf2,
  f555d5dab, 0702840c0). Questions: scratchpad q/r63-raw-dispatch3-trap.md (copied as REVIEW.md in build/lanes/codex-r-r63-rd3-trap).
- Next free review id: r64 (reserved for evidence-out-4 when its READY lands; questions drafted).
- r63-rd3-trap 0702840c0 vs 6d50e45b5 (361 s): raised 6 (2 bug, 4 claim-gap), CONFIRMED 6, rejected 0. F1 fnn-raw-captured /
  *fnn-raw-captured* expose the bare body; F2 pre-install captures (crypto.lisp + io.lisp load-time forms precede install);
  F3 *fnn-in-core* ambient + reusable fixed-callback closures; F4 (bug) reinstall after redefinition re-blesses; F5 (bug)
  raw-traps probe lacks unwind-protect; F6 unknown-kind refusal unwitnessed. Empty served table: none live. -> main.
- r64-cold-read d81f54f36 vs 89e0f4f7e (PRE-READY, 358 s): raised 4 (2 bug, 2 claim-gap), CONFIRMED 4, rejected 0. F1
  heap-reservation-tests :929/:1120 stale 30-thread totals (2180->2200, 996->1016); F2 native_owner_chunk_loop_raw.lisp:442
  declares deleted fnn-extent-prefetch-direct; F3 page_io funded pool refused (fixed by lane e6a83c620); F4 happens-once
  removal witness changes inputs. Served logic clean. -> main.
- evidence-out-4 pre-check (liaison, 28e18380c): own ls-tree enumeration (400 random commits + 1481 tips) 0 missed by lane
  walk; own hbox check of all 19185 walked blobs: 19179 OK, 6 MISSING (542eaa92 5a41497d 6723ab4d 328c7887 9e8fece9 e15e416f);
  backlog 3 OK. Scripts: liaison-10 scratchpad spot.py / full.py. Next free id: r65 (evidence-out-4).
- r65-evidence-out4 28e18380c vs 41ec96a81 (PRE-READY, 485 s; questions scratchpad q/r63-evidence-out4.md): raised 5 (4 bug,
  1 claim-gap), CONFIRMED 5, rejected 0. Walk agrees with independent enumeration (19185 = 19185, both -m and separate).
  r61: F2/F4/F5/F6/F10/F11 CLOSED; F1/F3/F7/F9 PARTIAL; F8 OPEN. F1 no committed completeness json, no index pin, no
  rewrite-time drift check, plan:90-92 still old commands; F2 filter-repo implicit `<glob>/*` for globs not ending in *
  (0 current extras); F3 make_dirs retry leaves archive-root entry unsynced; F4 cut_release g_closure folds 3/4 into 1;
  F5 chain_schedule cached summary unverified. + L1 reflog-only objects unmeasured. -> main. Rewrite still BLOCKED.
- c01-listview CONSULTATION (coordinator ask, for ember; gpt-6-astra 600 s, worktree build/lanes/codex-c01-listview at
  adbf57435): answer pasted verbatim + liaison fact-check (8 code claims verified) into
  build/coordinator/decisions/list-view-2026-10-02.md "Astra's view". Verdict A (LIST/ACTIVE/COUNTS from the completed
  durable view, pin unchanged); 7.6.3 omission real; retired groups stay selectable under all options; low-water
  objection. -> main.
- evidence-out moved: 4d01f4624 "Codex r65 fixes" (no READY seen yet).
- r66-evidence-out4-delta 4d01f4624 vs 28e18380c (PRE-READY, 504 s; q/r66-evidence-out4-delta.md): raised 6 (5 bug,
  1 claim-gap), CONFIRMED 6, rejected 0. r65 F2/F3/F5/L1 closed; F4 partial. F1 tag->tree/blob and worktree-private tree
  refs unwalked (0 today); F2 index length dedup by sha; F3 runbook pins before index commit (self-refusal); F4 runbook
  :153-158 update-ref -d refs/codex + filter-repo lack -C (would hit the SHARED repo); F5 cut_release open masks refused;
  F6 ancestor fsync on retry. Completeness json still uncommitted. -> main.
- evidence-out-4 pin 61f7520a3 (19209/19209) INDEPENDENTLY VERIFIED by liaison: own ls-tree walk (600 random commits incl.
  reflogs + 1482 tips) 0 missed; own hbox check of all 19210 currently walked: 19209 OK, 1 MISSING = c6f8ad68
  (served-wiring LANEDUMP.md 1ac64168e, committed after the pin): drift, --check must refuse until freeze. -> main.
- c02 unlanded-branch triage (coordinator ask; READ-ONLY; 190 non-salvage branches from scratchpad notondev.txt) LAUNCHED as
  two parallel Codex sessions: build/lanes/codex-c02-unlanded-A (93 lane/*), -B (97 codex/* + others), TASK in
  build/codex/c02/. Output to merge: build/coordinator/unlanded-triage-2026-10-02.md.
- c02 unlanded triage DONE: build/coordinator/unlanded-triage-2026-10-02.md (parts A 953 s, B 1153 s). lane/*: 6 landed,
  3 superseded, 25 live/held, 3 class-5, 56 dead; codex/*+: 24/2/30 parked/1/33 class-5/7. Liaison spot-check 11
  branches: 3 class-1 + 8 class-5 CONFIRMED (2 nits: genfix2 file misnamed; transit-subject slice size). -> main.
- evidence-out-4 f3b243fc4 (r66 fixes) liaison diff-read: CLEAN; F1-F6 closed (runbook steps 6/7 rewritten with
  commit-pin-commit and absolute git -C). Nit: private-ref lookup silently skips an unpruned worktree whose dir is gone.
  Gate opens on READY with a fresh pin at frozen refs (current pin stale by c6f8ad68). -> main.
- r67-served-wiring LAUNCHED: lane/served-incremental-1 b32f40f4e vs 56b82e7ee (pre-READY; NEWNEWS -cat wiring 79741a764,
  transit-decide host call a17b1be7e, join-read fix, blake3 vectors). q/r67-served-wiring.md.
- r67-served-wiring b32f40f4e vs 56b82e7ee (PRE-READY, 838 s): raised 5 (3 bug, 2 claim-gap), CONFIRMED 5, rejected 0.
  F1 fn-splan-cursor-step guard fn-cat-handles-inp walks the catalog every quantum (counterpart; pre-existing for OVER);
  F2 NEWNEWS continuation tombstone probe does cold I/O under the owner mutex (no-io binding only on the first command);
  F3 cursor-only success result invisible to exposure (autologout not reset); F4 reads-at-most-q is output
  independence, not a visit bound; F5 removal witnesses omit retained hyps. -> main.
- r68-sf-success bcdfa55ec vs 77b7d258d (676 s): raised 2 (1 bug, 1 claim-gap), CONFIRMED 2, rejected 0. Equality sound
  (equal hash test; unconditional theorems). F1 empty-successes regression (fill n before checking successes; reopen
  state); F2 no exec-vs-logic differential teeth. Residual: fn-sn-statep O(n) per guard eval (record-listp, shapep,
  phase-shapep, materialization). -> main.
- r69-rd3-trap-delta c2b836ca2 vs 0702840c0 (trap READY delta): raised 7 (2 bug, 4 claim-gap, 1 nit), CONFIRMED 7 + L1.
  r63 F1/F2/F4/F6 closed, F3/F5 partial. F1 entry-guard fault now wrapped by fnn-call's handler (type+text change, zero
  entries); F2 io.lisp-alone fixtures broken (conditions moved, load-time hook); F3 public fnn-raw-dispatch-callback;
  F4 session extent via *fnn-image-profile* rebinding; F5 no escape teeth; F6 stale probe claim; F7 comments.
  L1 (liaison): call-in-core takes a :synchronized global hash table write+remhash per fnn-call (zero entries too). -> main.
## BACKLOG (for hand-off; coordinator 2026-10-02)
- fn-sn-statep remains an O(n)-per-call whole-state revalidation on every fn-owner-io guard evaluation
  (fn-sf-record-listp, fn-sf-shapep/fn-sl-canonp, fn-sf-phase-shapep candidate/membership, fn-sf-records
  materialization, fn-sn-verdict-listp, keyring snapshots). Real fix: raw dispatch for fn-owner-io over the carried
  invariant (stage 5). (r68 Q2 inventory: build/lanes/codex-r-r68-sf-success/build/codex/r68-sf-success/FINDINGS.md.)
- t38-sf-empty LAUNCHED (Codex, worktree build/lanes/sf-success, lane/sf-success from bcdfa55ec): r68 F1 empty-successes early answer + F2 differential teeth; REPL laptop or stop for liaison box run.
- cold-read-ownership delta d81f54f36..7c87956fa (coordinator ask; liaison diff-read, no Codex): CLEAN. Only lane
  host/books change = page-read-direct.lisp theorem (happens-once hypothesis dropped, stronger); r64 F1-F4 fixed;
  page_io retire-by-compaction fixture asserts fd held/close-held/replacement at another file/CANCELLED then closed/no
  late 220. Note: reclaimed file stays named until restart (lane's Q16 gap). -> main.
- t38-sf-empty: Codex 289 s, 1 round; commit 3291b99d3 (books/store-files.lisp :exec arm only: (if (consp successes)
  (fn-sf-ks-success-listp ...) (null successes)); + 9 guard-checked differential assert-events in
  store-files-teeth-tests). Codex's laptop REPL refused (toolchain mismatch) -> it stopped as instructed. Liaison hbox
  REPL (--source-deps): books/store-files 196/196 forms admitted; tests/acl2/store-files-teeth-tests 109/109 loaded
  (all new assertions pass). AUDITED (diff in scope; :logic body and equality theorem byte-identical).
- t38 measured (hbox REPL time$): S=0 0 bytes at 1k/10k/100k; S=n 0.16 / 1.1 / 11.9 MB (0.04 s at 100k).
  READY lane/sf-success 3291b99d3 (origin/dev 77b7d258d up to date; pushed) -> main (coordinator relays to the runner).
- evidence-out-4 new pin 30534f955 (19235 at f3b243fc4) + 4b3c94a19 crosscheck --source: liaison CLEAN. Origin
  (github) heads all present locally; no refs/pull. Own walk 0 missed; own hbox check of 19240 now-walked: 19235 OK,
  5 MISSING (post-pin LANEDUMP-type blobs). Rewrite needs a real freeze before migrate/write/check/crosscheck. -> main.

## HAND-OFF liaison-10 -> next (2026-10-02 ~01:15 local, ~130 tool uses)
Tally liaison-10 reviews (raised / confirmed / rejected): r63 6/6/0, r64 4/4/0, r65 5/5/0 (+L1), r66 6/6/0,
r67 5/5/0, r68 2/2/0, r69 7/7/0 (+L1) = 35 / 35 / 0. Consultation c01 (LIST view) pasted + fact-checked; c02
unlanded-branch triage written + spot-checked (build/coordinator/unlanded-triage-2026-10-02.md). Tasks: t38 AUDITED
+ READY (lane/sf-success 3291b99d3). Diff-reads: evidence-out f3b243fc4 + 4b3c94a19 CLEAN; cold-read delta CLEAN.
NEXT FREE REVIEW ID: r70. NEXT FREE TASK ID: t39. LIVE CODEX (mine): none.
PENDING:
0. EVIDENCE-OUT-4: no code finding open. The rewrite needs a FREEZE: the pin drifts by a LANEDUMP blob every few
   minutes (5 missing at 00:55 vs pin 30534f955). At freeze: lane runs complete --migrate --write at frozen refs, then
   --check and crosscheck --source origin; liaison reruns scratchpad scripts (liaison-10 scratchpad spot.py = own ls-tree
   sample vs lane walk; full.py = own hbox check of every walked blob at the canonical object) — copy them from
   /private/tmp/claude-501/-Users-ember-dev-fn/700aaf5a-8922-4967-81c4-780af0acd71d/scratchpad/ (spot.py writes
   lane-walk-blobs.json that full.py reads; run spot.py first).
1. RD3-TRAP (lane/rd3-trap c2b836ca2): r69 F1 (entry-guard fault wrapped by fnn-call's handler: test_native_entry_guard /
   image_floor should go red) and F2 (io.lisp-alone fixtures broken) must be fixed before the trap READY; F3-F7 claim
   gaps; L1 call-in-core's :synchronized hash table per fnn-call (measure vs 0702840c0). Delta-review the fix commit.
2. SERVED-WIRING (lane/served-incremental-1 ceaea8d7c, handed off): r67 F1-F3 are served blockers for NEWNEWS
   (guard walk per quantum, cold I/O under the owner mutex, exposure not refreshed); review the fix when it comes.
3. SF-SUCCESS: READY sent; if the runner reports red, look first at store-files-teeth-tests (REPL'd on hbox 109/109).
4. Batched book-only teeth/claim gaps (from liaison-9's list, still open): r57 F1, r58 F1/F3, r59 F1-F3, r62 F2-F4;
   plus r67 F4/F5, r68 F2 (done by t38), r69 F5/F6.
5. BACKLOG above (fn-sn-statep O(n) per call; raw dispatch for fn-owner-io).
Worktrees added (all read-only reviews/consults): codex-r-r63..r69, codex-c01-listview, codex-c02-unlanded-A/-B.
LIAISON NOTES: zsh: `$B:h...` in "git show $B:host/..." is a history modifier -> use "${B}:path". proof_repl on the
laptop refuses (toolchain bf681d75 vs cache fcedce7e); persvati cache lacks many store books; hbox with --source-deps
works (store-files ~15 min). remote_check --ship a script under build/codex/<task>/.

## LIAISON-11 (2026-10-02, Opus) log
- r70 LAUNCHED (idle audit, read-only): build/lanes/codex-r-r70 detached at origin/dev 4aa332295; brief build/codex/r70/REVIEW.md
  (Q1 tree readers of planning/evidence, Q2 writers expecting tracking, Q3 cited-but-missing tracked paths, Q4 dead md
  links/anchors, Q5 unrewritten shas, Q6 ignore/baseline/fixture config). Output FINDINGS.md; every finding to be verified in source.
NEXT FREE REVIEW ID: r71. NEXT FREE TASK ID: t39.
- STANDING (coordinator 2026-10-03): consultations per build/coordinator/decisions/README.md take priority over idle audits.
- c03 LAUNCHED (coordinator's "c02"; liaison-10 already used c02): decisions/group-count-after-reclaim-2026-10-03.md;
  worktree build/lanes/codex-c03-groupcount at 4aa332295, brief build/codex/c03/CONSULT.md, output ANSWER.md.
- c04 LAUNCHED: generators-2 sketch (lanedumps/generators-2.md); worktree build/lanes/codex-c04-generators at 4aa332295,
  brief build/codex/c04/CONSULT.md, output ANSWER.md. Paste under "Astra's view" in the lanedump with fact-check.
NEXT FREE CONSULTATION ID: c05.
- c05 BRIEF WRITTEN, QUEUED behind c03/c04 (coordinator's order): def-holder inventory + sketch (lanedumps/def-holder.md);
  worktree build/lanes/codex-c05-holder, build/codex/c05/CONSULT.md. Launch: the same codex exec line as c04 with c05.
- c06 BRIEF WRITTEN, QUEUED behind c05: def-entry sketch (lanedumps/def-entry.md); worktree build/lanes/codex-c06-entry,
  build/codex/c06/CONSULT.md.
NEXT FREE CONSULTATION ID: c07.
- c05, c06 LAUNCHED (five sessions live = protocol maximum: r70, c03, c04, c05, c06). Launcher for consultations:
  <liaison-11 scratchpad>/consult.sh CID WORKTREE (codex exec on build/codex/CID/CONSULT.md -> ANSWER.md).
- c07 BRIEF WRITTEN, QUEUED (launch when a slot frees): command-view policy (decisions/command-view-policy-2026-10-03.md)
  + def-command sketch (lanedumps/def-command.md); worktree build/lanes/codex-c07-cmdview, build/codex/c07/CONSULT.md.
  c03 was already running, so c07 is its own session; its brief carries the c03 question file for consistency.
NEXT FREE CONSULTATION ID: c08.
- COORDINATOR: persvati disk 100% full: write NOTHING there (no remote_check / REPL on persvati); hbox only (--host hbox,
  not auto) until ember frees space. Delete nothing.
- c08 LAUNCHED (PRIORITY, blocks ARENA-FORGET host wiring): decisions/arena-forget-2026-10-03.md; worktree
  build/lanes/codex-c08-forget detached at lane/arena-forget 45bab6a65; build/codex/c08/CONSULT.md -> ANSWER.md.
  Six sessions live (r70, c03-c06, c08); c07 still queued. Fact-check c08 FIRST when it returns.
NEXT FREE CONSULTATION ID: c09.
- r70 DONE (1356 s): 13 raised / 12 confirmed + 1 confirmed-with-correction (F8: receipt_recovery test exists; ion_ltp test
  missing) / 0 rejected. Ranked list sent to main. Extra, found while verifying F3: tests.test_build_lists_check has 8
  failures on origin/dev unrelated to the rewrite (build_lists_check: 4 findings; DTN image misses owner-control-turn.lisp).
  Removed ~470 MB scratch JSON from build/lanes/codex-r-r70/build/codex/r70 (kept FINDINGS.md, scan.py, refine.py, report.py).
- c03 DONE (976 s): pasted + fact-checked in decisions/group-count-after-reclaim-2026-10-03.md. Astra: option 2' (exact
  available count, true endpoints, allocation watermark separate); fixture survivors are {1,34}, not a prefix. Sent to main.
- PROTOCOL: "Astra as an empowered peer" section added to codex-protocol.md (ember 2026-10-03).
- LAUNCHED: w01 (independent whole-system answer; build/lanes/codex-w01-wholesystem; copy ANSWER.md to
  decisions/whole-system-correctness-astra-2026-10-03.md), r71 (standing review: owner.lisp + mux.lisp; next r72 = io.lisp +
  extent.lisp, r73 served-incremental books, r74 def-carried), o01 (work offer -> CHOICE.md; then write tNN TASK from it).
  Stage 0 in the rewritten history = 6eb7d166a (old 89e0f4f7e). Launcher: <scratchpad>/run.sh ID WORKTREE BRIEF.
LIVE: c04 c05 c06 c07 c08 w01 r71 o01. NEXT FREE: r72, t39, c09.
- c03 DECIDED by the coordinator (AGREED, Astra's 2'); assigned to SERVED-CATALOG-LIVE.
- t39 LAUNCHED (Astra's first workstream, assigned by the coordinator): the r70 fixes. Worktree
  build/lanes/codex-t39-rewrite-dangling, branch lane/codex-t39-rewrite-dangling from 4aa332295; TASK
  build/codex/t39/TASK.md (10 items, one commit each, a failing-before test per fix). AUDIT per protocol, then READY to main.
  The build_lists_check red (8 failures, 4 findings) is the runner's, not t39's.
LIVE: c04 c05 c06 c07 c08 w01 r71 o01 t39. NEXT FREE: r72, t40, c09.
- c06 DONE (879 s): pasted + fact-checked at the end of lanedumps/def-entry.md. c04 DONE (1149 s): pasted + fact-checked at
  the end of lanedumps/generators-2.md. Summary to main. Confirmed on dev: fn-splan-cursor-step's guard walks every catalog
  row per OVER quantum under the owner mutex (no raw dispatch on dev; guard-checking t).
- o01 DONE (334 s): Astra claims (a) log-cut coverage, CORRECTED: the 7 rotation/drop cuts are modelled
  (books/store-log-segments.lisp) and mapped (native_cuts.py SEGMENT_PROGRAM_HOSTS); the real gap is fnn-log-at accepting any
  name and no both-direction inventory check (native_program_check does not call the segment check). Verified. Then (b) the
  lock-discipline check, then (c) small harvests (wire-scan full-state, pull-login; profile-seal already on dev;
  sol-ltp-completion ref absent). def-holder F2 is thereby REFINED: fail-open validation, not missing models.
- t40 LAUNCHED: Astra's own TASK (CHOICE section 3), worktree build/lanes/codex-t40-log-cuts, branch lane/codex-log-cut-coverage.
  Acceptance 4 (native log tests) is mine on hbox.
- COORDINATOR: c04 and c06 ADOPTED in full (routed to GENERATORS, DEF-ENTRY, STAGE-5B as decisions). Astra's rulings are
  now the design: every future Astra brief that touches generators/def-entry says so and cites both lanedumps' "Astra's view".
- QUEUED REVIEW for served-catalog-live's READY (fix at origin/lane/served-catalog-live 0566b362f): Astra reviews exactly the
  claim that no function on the quantum's path uses fn-cat-handles-inp (fn-splan-cursor-step guard cut to (natp w)): any
  theorem, guard proof or def-carried row relying on it as a guard-derived fact, plus the host change. Next id r72.
- Priorities (coordinator): c08, then w01 and r71.
- COORDINATOR approved t40 + Astra's order. NEXT FOR ASTRA after t40: (b) lock-discipline check, scope coordinated with w01
  and the COMPOSITION deputy's answer (decisions/whole-system-correctness-2026-10-03.md; Astra may read it ONLY after w01 is
  delivered); start with the narrowest rule that would have caught r31 F1 (an off-lock read with no declared pin), then grow.
  Then the two harvests. Triage corrected (appended section): profile-seal landed; sol-ltp-completion preserved in
  hbox archive at 92a4c1337 (not lost).
- c07 DONE (761 s): pasted + fact-checked at end of decisions/command-view-policy-2026-10-03.md. NEW: DATE answers the accept-time clock (served.lisp:172-178).
- COORDINATOR adopted ALL c07 rulings (by-id: pin first then completed; no second round). Told Astra in the t42 brief.
- t42 LAUNCHED (parallel to t40; no file overlap): DATE reads the current observation; worktree
  build/lanes/codex-t42-date-current, branch lane/codex-date-current. Astra may use tools/proof_repl.py --host hbox ONLY.
  t41 = lock-discipline check, after t40. LIVE: c05 c08 w01 r71 t39 t40 t42.
- c09 LAUNCHED: delta on TEETH CONTRACT v1 (generators-2.md:529-616), worktree build/lanes/codex-c09-teeth at lane head 319c1da87 (committed defteeth is 6036c954a; only def-carried-view.lisp uncommitted). One page. NEXT FREE: c10, r72, t43.
- COORDINATOR: persvati recovered (105 GB free). New briefs may say --host auto; keep remote trees bounded, remove each when its work lands. (t42's brief still says hbox-only: fine, no change needed mid-run.)
- c05 DONE (1358 s): pasted + fact-checked at end of lanedumps/def-holder.md. Headline FALSE (exhaustive); liveness UNSAFE as stated; F1 claim-gap (image id never retired today), F2 nit, F5 liveness gap (pins identified by cid; window deadline frees stalled sockets), F3 premise contradicted.
- c08 DONE (1304 s): pasted + fact-checked at end of decisions/arena-forget-2026-10-03.md. NEW rows: deferred reclaim leaks interned tombstone payloads (owner.lisp:5726-5729 vs 5792-5799); release-extents swallows close errors (owner.lisp:5011 vs extent.lisp:1243).
- c09 DONE (234 s): DOES NOT CLOSE; pasted at end of generators-2.md. NEXT FREE: c10, r72, t43.
- c08 ADOPTED (coordinator). t43 LAUNCHED: ambiguous close fences the owner + handler inventory (feeds t41); worktree build/lanes/codex-t43-close-fence, branch lane/codex-close-fence. LIVE: w01 r71 t39 t40 t42 t43.
- c10 LAUNCHED (gates ARENA-FORGET): BP workflow node rebind at the swap; worktree build/lanes/codex-c10-bpnode at lane/arena-forget head; answer goes under "Astra's view (c10)" in decisions/arena-forget-2026-10-03.md. NEXT FREE: c11, r72, t44.
- COORDINATOR: COMPOSITION deputy delivered decisions/whole-system-correctness-2026-10-03.md (first slice = lock_discipline_check R1-R6 = t41's scope). t41 HELD until w01 is delivered AND reconciled: after w01 lands, resume/new session gives Astra the deputy's file and asks for a reconciliation section (agree / differ / what it would change); then t41 implements the reconciled rule set (one check). Do NOT show the deputy's file to w01 before delivery.
- c10 DONE (211 s): REBIND SAFE IF reclaim excludes live BP dependencies -- NOT today: fn-rcl-store-holders BP slot is nil, retention pins ignored by reclaim selection (confirmed). Pasted under "Astra's view (c10)".
- r71 DONE (1302 s): owner.lisp + mux.lisp standing review: 16 raised. Verified by me in source: F1 F2(=t43) F3 F4 F5 F6 F8
  F9 F10 F11 F12 F15 F16 (13 confirmed); F7 F13 F14 accepted on Astra's chain, partly checked (F14's rpin alist scan
  confirmed earlier in c05). 0 rejected. Ranked list to main.
- t44 LAUNCHED: index-backing-request-adoption 1800 s timeout (REPL --host auto); worktree build/lanes/codex-t44-ibra-timeout. t40 DONE -> auditing.
- r71 ROUTING (coordinator): 1+2 -> Astra, widening t43 into "every owner quantum under one shared fence boundary"; t43 is
  mid-run, so this is t45 (after t43 lands, same files). 3,5,9-13 -> new Opus lane HOST-LIFECYCLE. 4,6,7,8 wait for the
  reconciled whole-system design + t41. 14 -> COST-GATE + DEF-HOLDER; 15 -> DEF-ENTRY; 16 -> GENERATORS. r72 = io.lisp +
  extent.lisp now.
- t40 AUDIT in progress: diff read (9 files, all in its claimed scope; host change = fnn-log-at validation + segment declaration); local acceptance rerun by me: test_native_cut_map + test_native_program_check 30 OK; native_program_check exit 0 'log cut inventory: PASS (13 cuts; 7 segment cuts)'; NativeOwnerHandlerStructureTests selector test OK. Native acceptance 4 submitted: persvati native-714930557a11 (developer,production; test_native_log, test_native_log_compaction, NativeOwnerHandlerStructureTests). r72 LAUNCHED.
- SWEEP (coordinator): build/coordinator/inspection-sweep-2026-10-03.md, 147 findings routed. t45 (launch when t43 lands) =
  r71 F1/F2 widening + S015 S016 S017 S019 S020 S023 (copy their sections into the t45 brief). r72 was already running when
  the sweep arrived: at triage, DROP every r72 finding duplicating sweep slices io-a / io-b / mux-extent (grep the sweep by
  file:line and function) and report only additions. SWEEP-PEER / -GATES / -STORE / -OPS READYs come to me for review.
- t39 AUDITED (1863 s, 1 round, 10 commits): 31 files, all in scope (Makefile: comment only; docs/books regenerated with
  tools/book_navigator.py --write; planning/coverage.json left per the generator exception). evidence_store add_to_index /
  put refuse different bytes (EvidenceConflict) unless replace=True; the only replace=True caller is index-tree --write
  (tracked-file transition: justified). Reran: 129 unit tests, 1 FAIL test_the_command_line_reports_the_four_counts
  (archive objects absent on the laptop; fails identically on origin/dev; Astra reported it). build_lists_check: 0 ERROR,
  8 FAIL (runner's). registry_paths_report --check: 134 unresolved = baseline. New tests fail on origin/dev's code (ran
  them in the r70 tree). Nit: commit_map.resolve tries rev-parse first, so a short OLD sha that happens to prefix a NEW
  object resolves to it silently (low probability; prefer the map when the input matches a map key). Pushed; READY sent.
- t39 follow-up by me: 92b258739 (resolve prefers the map; refuses an old/new abbreviation collision; test fails before).
- w01 DELIVERED -> decisions/whole-system-correctness-astra-2026-10-03.md. Round 2 (reconciliation with the deputy's file)
  running as `codex exec resume 01a0feb4-db10-72c1-9f0a-63d3e07b4aa8` -> build/codex/w01/RECONCILE-ANSWER.md.
- t43 AUDIT (1240 s, 1 commit 459a7fc4a): diff read; in scope (host/native extent/owner/io/recovery-payload-view, docs,
  spec, tests). Removed its laptop-regenerated planning/current.md (d52815d5d). Logic checked: close->settlement->remhash under
  one handler; an fd present -> indeterminate; pending helper runs inside fnn-owner-shared-action-locked (fences under the
  held mutex) and skips when stopping; release-extents: indeterminate -> fence, store-fault/serious -> fault-service,
  store-error -> log+retry. Residual (t45): an indeterminate raised in release-extents OUTSIDE the pending helper is fenced
  after the gated quantum released the mutex. Structure tests 3 OK locally. Native: persvati native-d52815d5dcf6
  (ExtentCloseFenceTests, test_native_checkpoint_auto, NativeOwnerHandlerStructureTests).
- !!! CODEX USAGE LIMIT HIT (2026-10-02 23:12Z): "try again at Oct 8th, 2026 6:49 PM". t45 died with no commits; w01 round 3
  not run (ROUND3.md ready); t41 blocked. Told main; asked who takes t41/t45 and whether credits are ember's call.
- w01 round 2 (RECONCILE-ANSWER.md) appended to decisions/whole-system-correctness-astra-2026-10-03.md.
- t42 AUDIT: removed tracked build/codex/t42/REPORT.md and regenerated planning/current.md; made books/served-date-current +
  2 witness books Makefile roots (5e580daf6); pushed; farm submitted auto -> hbox (status pending).
- COORDINATOR (a-d): t41 -> Opus lane LOCK-CHECK; lifecycle protocol + t45 -> Fable deputy FAILURE-SCOPE; DECISION block written in whole-system-correctness-2026-10-03.md; credits = ember's call. WITHOUT CODEX: I review READYs myself + ONE independent fresh-context Opus reviewer (told to refute) per served-path/trust-boundary READY.
- r72 DONE (codex finished before the limit): 11 raised; F2=S019/t45, F10=S013 dropped as dups; 9 new sent to main (F1 OpenBSD zero-fill over a misaligned committed segment CONFIRMED; F3 checkpoint header loop; F4 seal I/O under owner; F6 node-secret fsync-dir -> fault not uncertain; F7 SIGHUP fd swaps unbounded; F8 whole-tail vector CONFIRMED; F9 quadratic length CONFIRMED; F5 export parent fence; F11 fd leak).
- REVIEW RULE (ember 2026-10-03, decisions/host-into-acl2-2026-10-03.md): in every review flag NEW host code that decides or coordinates (not a primitive) and ask whether it could be ACL2. TCB-SHRINK (Fable) plan comes to me for independent review.
- host-model plan REVIEW (by me) -> lanedumps/host-model-review-1.md: BUILD WITH 4 MUST-FIXES (lease reads unlabelled; definitional theorems; realization unchecked = half of r31 F1; P10 cut set wrong + complete-rotation uncut). Sent to main.
- FAILURE-SCOPE sketch REVIEW (by me, from the coordinator's summary; sketch not on disk) -> lanedumps/failure-scope-review-1.md: 4 must-fixes (typecase fail-open to :refusal; os-error after a durable effect; non-condition exits; pending-extent release after fence contradicts t43). Sent.
- t44 READY sent (persvati certify-20261002T231403Z-689726 157/0). HOST-LIFECYCLE item 3 reviewed: CLEAN.
- t42 RED at affected-root certify (certify-20261002T231742Z-1964379: 671/80): fn-otm-closed-posting-answers-the-generic-440
  antecedent named fn-post-reader-env; repaired by me (0bcd9a338: antecedent over fn-post-command-env; REPL hbox 54/54);
  recertifying the 79 failed roots: hbox run-20261003T020606Z-9728.
- t40/t43 natives on persvati died at host-ld (image-world-dtn uncertified: dev's DTN red, fixed by 45e05c7fd). Merged
  origin/dev into both (t40 80839588a, t43 aef47ab90); rerun on hbox: native-80839588a0a8, native-aef47ab90f17.
- LESSON (coordinator): a REPL of the changed book's closure is not enough when a definition many books expand through
  changes; the affected-root certify is the evidence.
- DEF-ENTRY c1d69fb6a REVIEWED (by me, no reruns): LAND; should-fix: fn-cw-conjunct-class skips predefined-headed argument conjuncts before the :argument refusal; mirror reads top-level source forms (local/encapsulate/dup/bridge-conflict divergences). MUST-FIX pre-existing definterface: fn-di-defined-conjuncts drops ALL predefined-headed conjuncts (<, equal, consp) before fn-cd-uncovered-conjunct, so raw-with can skip an unproved conjunct; latent until the first raw_with row.
- TCB-SHRINK REVIEW (by me) -> lanedumps/tcb-shrink-review-1.md: sound; must-fix *inside-absstobj-update* race, per-thread catch, torn actor stobjs, definterface raw-with gap; acceptance misses S003/r71 F5 and S014; seal conflict w/ OWNER-OFFLOCK; B8 = make check red (host_loaded_check exit 1).
- REPAIR LEDGER adopted (build/coordinator/repair/repair.py; my lane name = liaison). Discovery FROZEN: review READYs only, findings via repair.py add with the file's owner. Added L01 L02 (def-entry), L03 (composition). X07 = t42 in-progress.
- MERGE-ALL (ember): pushed + sent runner t42 0bcd9a338, t40 80839588a, t43 aef47ab90, t39 92b258739, t44 ef08768cb. Reviews no longer gate merges; findings -> ledger against dev.

## HAND-OFF liaison-11 -> next (2026-10-03, wind-down ordered by ember)
STATE: Codex (gpt-6-astra) is OUT OF USAGE until 2026-10-08 18:49. Discovery is FROZEN (repair ledger:
build/coordinator/repair/repair.py, lane name "liaison"). Reviews no longer gate merges (ember: everything onto dev).
PUSHED and sent to the runner (a8c1198f67920c411) for merge onto dev:
- t42 lane/codex-date-current 0bcd9a338 (X07, ready). IN FLIGHT: hbox farm run-20261003T020606Z-9728 recertifying the 79
  roots that failed in certify-20261002T231742Z-1964379 (cause was fn-otm-closed-posting-answers-the-generic-440,
  repaired by me). Check: `cd build/lanes/codex-t42-date-current && python3 tools/farm.py wait hbox run-20261003T020606Z-9728`;
  any red -> repair.py add against dev.
- t40 lane/codex-log-cut-coverage 80839588a. IN FLIGHT: hbox native-80839588a0a8
  (`tools/hbox_native.sh status 80839588a0a8`).
- t43 lane/codex-close-fence aef47ab90. IN FLIGHT: hbox native-aef47ab90f17 (`tools/hbox_native.sh status aef47ab90f17`).
- t39 lane/codex-t39-rewrite-dangling 92b258739 (takes over 1f1e91667). t44 lane/codex-ibra-timeout ef08768cb (certify 157/0).
NOT STARTED (needs Codex or a lane): t45 = FAILURE-SCOPE's (brief build/lanes/codex-t45-fence-boundary/build/codex/t45/);
t41 = LOCK-CHECK lane; w01 round 3 brief ready (build/lanes/codex-w01-wholesystem/build/codex/w01/ROUND3.md).
REVIEWS WRITTEN: lanedumps/host-model-review-1.md, failure-scope-review-1.md, tcb-shrink-review-1.md; DEF-ENTRY c1d69fb6a
reviewed (LAND; L01 L02 + X06). Ledger items added by me: L01, L02 (def-entry), L03 (composition).
NEXT: collect the three in-flight results, ledger any red against dev, then review incoming READYs only.
Worktrees to remove once merged: build/lanes/codex-{r-r70,r-r71,r-r72,c03-groupcount,c04-generators,c05-holder,c06-entry,
c07-cmdview,c08-forget,c09-teeth,c10-bpnode,o01-offer,w01-wholesystem,t39-*,t40-*,t42-*,t43-*,t44-*,t45-*}.
- POST-HANDOFF: t42 recertify finished: certify-20261003T020918Z-2995402 59 passed / 20 failed. Three roots fail the same way
  as the repaired theorem (they still state the post step under fn-post-reader-env): owner-control-read
  FN-OCTL-DISPATCH-ARCHIVE-COMMAND, productive-read-chain FN-PCR-POST-DELEGATES-A-READ-WITHOUT-OFFER-BY-DEFINITION,
  served-head-bridge FN-SHD-POST-DELEGATES-A-READ-WITHOUT-OFFER-BY-DEFINITION; the other 17 include them. Ledger X07b (high,
  owner liaison); X07 back to in-progress. Fix = restate each over fn-post-command-env, recertify those 20 roots.
