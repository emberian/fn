# SWEEP-OPS lanedump (wind-down 2026-10-03)

Branches (pushed, sent to runner a8c1198f67920c411 for merge-all):
- lane/sweep-ops cc4ef2db6 (base 4aa332295): S002 8aa451848 + e5e8b2e5c (measure max-bytes per gate class;
  tests/test_native_bounds_join.py PostHeapUnderMutexTests), S028/S034/S104/S105 8acfdeba7, S029 15c695ceb
  (books/native-control-kinds.lisp), S038 book half 196428f6d + cc4ef2db6.
- lane/sweep-ops-auth (S044, sub-agent a06953af7839d2501): head as pushed; it reports its own READY.
- lane/sweep-ops-cfg (S033, sub-agent a4a5ec329c6a50131): paused/messaged separately.
- lane/sweep-ops-base acd6f1ce9: origin/dev + measurement only (S002 "before" image).

State: REPL-admitted only; not certified; no native at these shas. Generated files NOT regenerated in
lane/sweep-ops (interfaces.json, ledger, proofs.json, current-view, books/image-world*.lisp,
tools/extract/world*.lisp: native-control-kinds must enter the umbrella) -- runner regenerates on merge.

NEXT (after merge, rebase on origin/dev, fix forward):
1. S002 heap numbers: hbox_native s002-base3 (acd6f1ce9, images production,dtn-developer) is the BEFORE;
   run AFTER at dev head: `tools/hbox_native.sh --box hbox --images production,dtn-developer --mem 32G
   --allow-skips <sha> tests.test_native_bounds_join.PostHeapUnderMutexTests`. Report largest-hold bytes/held-us.
2. Natives for the merged batch: test_native_protected_peering (S034), test_native_friends_feed (S105),
   test_native_slow_disk (S029 keys-redecide BUSY), test_native_raw_scripts (S028 raw), owner/auth/reader core.
   Certify closure: books/article-buffer, books/native-control-kinds, books/owner-reclaim (+ tests).
3. S038 host half (after RECLAIM-RETENTION 37456df07 on dev): fn-owner-orc-capture asks fn-orc-capture-slot,
   refusal (:refused WORD) writes nothing; fn-owner-orcp-capture checks admission before reserving credit,
   answers (:deferred WORD nil); publication-done / orc-finish clear via fn-orc-release-slot with the holder.
   Driver lines (owner.lisp reclaim-pass `unless captured`, dry-run capture) handed to ARENA-FORGET.
4. r72-F7 (io.lisp fnn-log-swap-fd: count swap fds in the sink bound, ACL2 decision, many-SIGHUP test).
5. Ledger open: S067 S068 S079-S083 S102 S103 S113-S115 S120-S123 S143-S146 (S032/S031 -> HOST-LIFECYCLE).

## S044 (sub-lane sweep-ops-auth, wound down 2026-10-03)

State: branch lane/sweep-ops-auth at a9e9a9c46 (pushed, tree clean; worktree build/lanes/sweep-ops-auth).
Done: books/nntp-auth.lisp has a 9th auth-session field `failures`, *fn-auth-failure-limit* = 3,
fn-auth-failed (failed PASS and failed SASL arms) and fn-auth-close-reader (closes the reader session as QUIT does).
KEYSTONES fn-auth-failed-pass-below-the-limit-is-481-and-keeps-the-connection and
fn-auth-failed-pass-at-the-limit-is-481-400-and-closes; the fold half cites fn-served-step-stops-at-quit.
Teeth tests/acl2/nntp-auth-failure-budget-tests.lisp (a Makefile root): REPL-green on hbox, including a
fn-served-step read of ten wrong pairs that answers 381 481 x3, then 400, then close. nntp-auth, nntp-auth-invariants
and nntp-auth-fold all load from source; fold's big theorem took 3.14M steps vs 3.13M at base.
Every constructor site updated (tests too). specs/nntp.md section "Authentication failures (NNT-1002)",
requirements NNT-1002, proofs PRF-1249 (ids claimed). Native test
tests/test_native_auth.py test_ten_pipelined_wrong_passwords_get_three_481s_then_400_and_eof.
NEXT (exact):
1. `python3 tools/farm.py wait hbox run-20261003T021813Z-8184` in the worktree (707 books affected by
   books/nntp-auth; never waited). Fix any red book forward; nntp-auth-teeth-tests / nntp-auth-tests /
   nntp-auth-sasl-tests were NOT REPL-loaded and are the likeliest reds (sessions with a 9-field shape;
   any test that fails three times on one session now closes).
2. Fast checks: `tools/remote_check.sh attach hbox` (log hbox:/tank/fn/scratch/sweep-ops-auth-check.log;
   interface_emit --check, host_check --read/--books, ledger, reach --strict, merge_registry, spec_cite,
   test_roots, next_id check).
3. Native: `tools/hbox_native.sh status s044` (tests.test_native_auth, test_native_sasl, test_native_conformance
   on a9e9a9c46); attach and read.
4. Then READY to the coordinator. Open, out of scope: the stored verifier is one fast salted digest per guess
   (offline guessing of a leaked verifier); an iterated/memory-hard verifier is unimplemented.
