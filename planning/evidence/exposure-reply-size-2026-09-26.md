# exposure-reply-size: a served reply of several MiB no longer stops the owner (PKT-481, fix half)

Lane exposure-reply-size (Opus 5.5), launched by deputy 3 on 2026-09-26 from
the qualification qual-dfa810fc's finding: on every image since
public-exposure (34c2ba45) the served ARTICLE of an article of 2 MiB or more
stopped the owner with exit 4, `owner core/store fault; process stopped: ACL2
error in fn-owner-chunk: Control stack exhausted`. Branch
`lane/exposure-reply-size` from dev d7b997d6. PRF-161 extended (no new PRF),
SCN-111 new, PKT-481's fix half, PKT-491 for what remains.

## 1. The cause, proved

Not the suspect the brief named. `fn-served-reply-octets` recurses once per
EFFECT (one `(:reply octets)` per command answered in the step), and
`fn-ag-append`'s executable has been the iterative `fn-ag-append-exec` since
large-article (2026-09-25, books/acceptance-alloc.lisp); both ran on every
step before public-exposure, when 3 MiB was served. The recursion that is
non-tail on the reply's LENGTH is `fn-exp-481-count`
(books/public-exposure.lisp), `(+ head (fn-exp-481-count (cdr octets) ...))`:
one control-stack frame per octet of the step's reply, called by
`fn-exp-observe` from host/owner-host.lisp `fn-owner-exposure-observe`
inside `fn-owner-chunk` after every served step.

Evidence (persvati REPL over books/public-exposure, toolchain w25, the same
`--control-stack-size 64` as the images):

- `fn-served-reply-octets` of two 2 MiB `:reply` effects returns (length
  4,194,304); `fn-exp-481-count` of 1 MiB returns 0; of 2 MiB: `Control stack
  exhausted`.
- `fn-exp-observe` over a registered connection and a 2 MiB reply, with
  `(set-debugger-enable :bt)`: the backtrace's frames 10 to 999 are all
  `FN-EXP-481-COUNT`
  (planning/evidence/exposure-reply-size/cause-backtrace.txt).
- Native, dev d7b997d6's developer image (sha256 866d45bb...): the 1 MiB
  ARTICLE is served identical, the 2 MiB ARTICLE stops the owner, exit 4,
  `ACL2 error in fn-owner-chunk: Control stack exhausted`
  (bigart-pre.log fe15d0a6...); and an OVER of about 4 MB (2,000 articles
  with about 2,000 octets of References each) stops it the same way
  (bigover-pre-dev.log a9145278...). So the class is the step's reply size,
  ARTICLE or OVER alike.

## 2. The fix and what the observation reads

The brief assumed the exposure charges a step by its reply's length. It does
not: `fn-exp-observe` reads exactly two facts of the reply, ANSWERED
(`(consp output)`: progress for the RFC 3977 section 3.1 timers, and the
entry's answered flag) and FAILURES (`fn-exp-481-count output t`: the RFC
4643 section 2.3.2 481 replies at a line start, for the failed-login limit).
No length. So the fix computes those two facts from the step's effects, with
no copy of the reply, and the exposure's decisions are unchanged by theorem.

- books/public-exposure.lisp: `fn-exp-observe`'s body moved verbatim into
  `fn-exp-observe-facts (xs lim id now answered failures consumed subject
  submitted)`; `fn-exp-observe` is that function of `(consp output)` and
  `(fn-exp-481-count output t)`. Every existing PRF-161 theorem about
  `fn-exp-observe` certifies unchanged (8.48 s; it was 9.33 s quiet).
- books/public-exposure-reply.lisp (new, 1.72 s): `fn-exp-481-scan`, a
  five-state recognizer of `481 ` at a line start (states: not at a line
  start; at one; after `4`, `48`, `481`), tail-recursive with an accumulator;
  `fn-exp-effects-scan`, the same recognizer carried ACROSS effects (a reply
  split between effects is one stream on the wire; a per-effect restart
  would be wrong, see the mutation witness), also computing ANSWERED; and
  `fn-exp-observe-effects (xs lim id now effects consumed subject
  submitted)`: `mbe :logic (fn-exp-observe ... (fn-served-reply-octets
  effects) ...)`, `:exec` the facts from one `fn-exp-effects-scan`. Guard
  verified: the executable is the definition.
- host/owner-host.lisp `fn-owner-exposure-observe`: calls
  `fn-exp-observe-effects` with the step's EFFECTS (was `fn-exp-observe`
  with `(fn-served-reply-octets effects)`). Its caller `fn-owner-chunk` is
  untouched, and so is the reply the host writes: `fn-owner-install-effects`
  still puts `(fn-served-reply-octets effects)` in `fn-owner-output`, so the
  served bytes are the pre-fix bytes by construction (no line of the output
  path changed). host/native/build.lisp includes the new book.

Allocation: the scan conses one pair per reply effect and nothing per octet
(8 MiB reply in the REPL: the only allocation measured was building the
test list). The step's reply is still materialized ONCE, for the wire
(`fn-owner-output`), as before public-exposure; the second copy the
observation made is gone.

## 3. Theorems (PRF-161 events; subject = the host's call)

The host line: host/owner-host.lisp `fn-owner-exposure-observe` calls
`fn-exp-observe-effects`; it is called from `fn-owner-chunk`, which
host/native/owner.lisp `fnn-owner-handle-chunk` calls through
`fnn-owner-action 'fn-owner-chunk` for every served read.

- `fn-exp-481-scan-counts-the-481-replies` (keystone, no hypotheses):
  `(car (fn-exp-481-scan octets 1 0)) = (fn-exp-481-count octets t)`. From
  the local lemma: for every state ST and numeric ACC, the scan's count is
  ACC plus `fn-exp-481-count` of the octets ST has read since the line start
  prepended to OCTETS.
- `fn-exp-effects-scan-is-the-reply-scan` (keystone, no hypotheses): the
  scan over EFFECTS equals `fn-exp-481-scan` over `(fn-served-reply-octets
  effects)` in count and final state, and its ANSWERED is `(or answered
  (consp (fn-served-reply-octets effects)))`.
- `fn-exp-observe-effects-is-the-observation-of-the-reply` (keystone, no
  hypotheses): the executable's result, `fn-exp-observe-facts` of the scan's
  two facts, equals `fn-exp-observe` of `(fn-served-reply-octets effects)`:
  the exposure's decisions (continue or the 400 close, the connection entry,
  the failed-login and post windows, the counters) are unchanged.
- `fn-exp-observe-effects-unfolds` (not cited: a definition restatement,
  `ledger.py` refuses it as an event): the host subject is `fn-exp-observe`
  of the reply octets, so every PRF-161 keystone about `fn-exp-observe`
  (`fn-exp-observe-keeps-the-connection-ids`,
  `fn-exp-limits-never-drop-a-connection`,
  `fn-exp-observe-closes-only-on-a-failed-login`) is about the host's call.
  Their statements did not move.

Teeth (tests/acl2/public-exposure-reply-tests.lisp, 1.62 s): the keystones
have no hypotheses, so a reachable non-degenerate witness each: a stream
with two 481 replies and a mid-line `X481 ` that neither side counts (count
2); `481 ` split over three `:reply` effects with a `:close` between them
(count 1, state and ANSWERED equal); the second failed login in the minute,
split over effects, closing with the 400 exactly as `fn-exp-observe` over the
concatenation. MUTATION witnesses (labelled, `must-fail`): the recognizer
started off a line start misses the first reply; a scan that restarts at each
effect counts `X` + `481 ` as a reply. SERVED SIZE witness: the executable
over a 3 MiB reply plus the terminator, the size that stopped the owner:
`:continue`, progress stamped, answered, no failures.

Manifest: persvati run-20260926T135251Z-2fe1,
planning/evidence/manifests/certify-20260926T135318Z-2532226.json, green:
the six roots affected by books/public-exposure.lisp and the new book
(owner-store-indexed and its tests, public-exposure and its tests,
public-exposure-reply and its tests; 203 books in the closure, 197 from the
cache); no book over 10 s.

## 4. Native (hbox; SHA-256 prefixes, full sums in the logs' directory)

Images: fix tree (worktree 2578e029, then + the standing test) developer
9fcc7886... and production 2395cb45...; pre-fix dev d7b997d6 developer
866d45bb...

| case | pre-fix d7b997d6 dev | fix developer | fix production |
|---|---|---|---|
| ARTICLE 1 MiB (bigart.py) | 220, identical | 220, identical, owner alive, exit 0 | same |
| ARTICLE 2 MiB | owner stopped, exit 4, Control stack exhausted | 220, identical, exit 0 | same |
| ARTICLE 3 MiB | (not reached) | 220, identical, exit 0 | same |
| OVER over 2,000 articles, 3,954,943 octets (bigover.py, tmpfs store) | owner stopped, exit 4 | 224, 2,000 lines, terminator, STAT 223, exit 0 | same |

Logs: planning/evidence/exposure-reply-size/bigart-pre.log (fe15d0a6...),
bigart-fix.log (dd2bcdc4...), bigover-pre-dev.log (a9145278...),
bigover-fix-fn-host-developer.log (70bffc32...), bigover-fix-fn-host.log
(e9451003...); the harnesses bigart.py (the qualification's, reused) and
bigover.py beside them. OVER line hashes differ between the two fix images
because each store injects its own Date and Path.

Modules (tools/hbox_native.sh --no-build --label fix at 08ca81eb, the
images built from 2578e029, whose books and host code 08ca81eb does not
change; FN_NATIVE_HOST set by hand to each image, the script's trap):

| module | production fn-host (core 2395cb45...) | developer (core 9fcc7886...) |
|---|---|---|
| tests.test_native_bounds_join (LargeArticleTests 3 MiB re-read, LargeReplyTests; DeployRehearsal skipped: no FN_FORMAT7_IMAGE) | OK, 3 ran, 1 skipped, 27.7 s (5b0bbeda...) | OK, 24.4 s (b7e07152...) |
| tests.test_native_public_exposure (the flood campaign, SCN-091) | OK, 53.9 s (aa7b2750...) | OK, 53.7 s (5941bc7d...) |

run.log per image: run.08ca81eb.fn-host.log (7d0ff74e...),
run.08ca81eb.fn-host-developer.log (17daae42...). The standing case on the
pre-fix dev d7b997d6 developer image FAILS at the 2 MiB ARTICLE (the owner
gone, the next POST gets no 340): standing-case-on-pre-d7b997d6.log
(49435d12...).

Harness trap found on the way (not the fault): the operator-verbs fixture
starts the owner with stderr on a pipe nobody reads until it stops; about
500 POSTs fill the pipe's 64 KiB, the logging thread blocks in pipe_write
holding the owner's log mutex, and the owner stops answering (512
transactions; `health` fenced, owner-unanswering). The first runs of the
standing case timed out on that; it now drains the owner's stderr. Any
native test that posts more than about 500 articles through
`start_owner` meets the same wedge.

## 5. The standing cases (the coordinator's addition)

tests/test_native_bounds_join.py `LargeReplyTests.
test_article_of_1_2_3_mib_and_a_4_mb_over_leave_the_owner_serving`: a 4 MiB
profile, POST and ARTICLE of 1, 2 and 3 MiB on one connection (each identical
suffix), the owner still running; 2,000 POSTs with about 2,000 octets of
folded References; OVER over the whole group (224, 2,003 lines, more than 3
MiB, the terminator); STAT 223 on a new connection; SIGTERM exit 0. Why here
and not tools/throughput_gate.py's served phase: this module already runs the
operator profile large enough to hold a 3 MiB article and asserts identity
and the owner's clean exit, which is what this class breaks; the throughput
gate measures time on small articles over a scale store and a multi-MiB step
would distort its phase budgets without saying why a step died. The existing
`LargeArticleTests` 3 MiB re-read (the gate that went red) stays as it was.
The case runs in about 25 s on hbox because the fixture's store is on
tmpfs (/tmp); on a disk store the 2,000 POSTs cost about 0.36 s each.

## 6. Assurance chain

native entry `fnn-owner-handle-chunk` -> `fn-owner-chunk` ->
`fn-owner-exposure-observe` -> executed ACL2 subject `fn-exp-observe-effects`
(guard-verified; its :exec is the effects scan) -> refinement
`fn-exp-observe-effects-is-the-observation-of-the-reply` (with
`fn-exp-effects-scan-is-the-reply-scan` and
`fn-exp-481-scan-counts-the-481-replies`): the executable equals
`fn-exp-observe` of the reply octets -> PRF-161's behavioural keystones over
`fn-exp-observe` (unchanged) -> observed: section 4. No maintained relation
is introduced: the observation is a function of one step's effects and the
exposure state.

## 7. Not done, and PKT-491

- `fn-exp-481-count` itself is still the per-octet recursion; it is now only
  the logical specification and is not executed on the served path
  (`fn-exp-observe` is not called by any host). Giving it an `mbe` twin would
  put the recognizer into public-exposure.lisp (about 0.3 s); left as is.
- A step's reply is still materialized once as an octet list for the wire
  (`fn-owner-output`, a list of 3 MiB is 48 MiB of conses). D27's concrete
  representation for the reply (a buffer range the writer drains) is the
  reply-side twin of ingress-span's S2 and is PKT-491.
- `fn-served-reply-octets` recurses per effect; a step's effect count is
  bounded by the commands in one host read, so this is not a data-size
  fault, but it is not a constant-stack loop either (PKT-491).
- An OVER over 2,000 articles took about 6.8 s to serve on both images;
  that is throughput, not this fault (PKT-491 notes it for the served-path
  scale lanes).
- A Subject of 900 octets appeared shortened in the OVER line in a probe on
  the pre-fix image (198 octets for two lines), and a References header of
  8,000 octets or more is refused `441 the article is not valid syntax`;
  neither was examined here (PKT-491 names both for the header-bound owner).
- The owner blocks on a full stderr pipe while holding its log mutex (the
  harness trap in section 4). Under systemd stderr is the journal and does
  not fill, but a wedged log sink wedges the owner; PKT-491 names it.
- PKT-481: the qualification lane owns the finding's line; this lane's fix
  half is retired by 2578e029 (the fix) and 08ca81eb (the standing case
  and registry), with this record.
