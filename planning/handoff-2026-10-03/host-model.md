# LANEDUMP host-model (COMPOSITION deputy, Fable 5.1), 2026-10-03

Worktree /Users/ember/dev/fn/build/lanes/host-model, branch lane/host-model from origin/dev 4aa332295.
Deliverables, each a READY: (1) books/host-model.lisp, the concurrent host model HM with its first
all-schedules theorem T1(b); (2) the reply-equals-reference keystones (P2, M6, P8) restated under the
carried relation; (3) P10's keystone re-pointed at the reachable program, current.md regenerated.
Claimed ids: PRF-1242, PRF-1243, PRF-1244 (ledger, lane host-model). Prefix: `fn-hmc-` (tests `hmct-`).

## 1. The HM plan (one page; for Astra)

Under decisions/host-into-acl2-2026-10-03.md the HM is the SPECIFICATION of the thin primitive layer:
its labels are the primitives' oracle steps (layer P) and the coordination steps that will be executable
ACL2 (layer C). A schedule is any list of labels from any actors; a label whose precondition fails is a
refused no-op (the model refuses exactly what the generated code must refuse). The host's existing books
are the C-steps' bodies, called by name, not rewritten.

STATE `(fn-hmc-make LOCKS FDS REQS ARPN OWNERS ROWS WORKERS NEXT RESULTS CLOSED)`:
LOCKS an alist lock -> holder tid or nil (:owner :extent :pins); FDS an alist fd -> incarnation (the OS
binding; a number may be rebound after close); REQS the reads in flight ((TOKEN . INC) ...), INC the
incarnation the fd was bound to at :io-begin; ARPN the `fn-arpn` state (CUR PINS PEND); OWNERS the
`fn-rpin` alist (cid . G); ROWS the `fn-pio` rows (the issued table); WORKERS the `fn-pxe` rows; NEXT the
read counter; RESULTS token -> verdict held by a returned worker; CLOSED the incarnations closed.

LAYER P (one primitive each, one named assumption each, A-PRIM-*):
  (:acquire TID L)   enabled iff L free; (:release TID L) iff TID holds L           [A-PRIM-MUTEX]
  (:fd-open TID INC) binds a fresh or reused fd number to INC                        [A-PRIM-FD]
  (:io-begin TID FD TOKEN) records (TOKEN . INC-bound-to-FD-now) in REQS; the device later
  (:io-complete TOKEN VERDICT) delivers the bytes of THAT incarnation and makes the running worker
  :returned with VERDICT -- any time, any order, duplicated, after a cancel, after a crash    [A-PRIM-PREAD]
  (:fd-close TID FD) unbinds FD (called only by the C-step :close)                  [A-PRIM-FD]
  (:crash) every in-flight request, row, worker, pin and lock is gone; CLOSED and FDS cleared.
LAYER C (ACL2 today, generated ACL2 under TCB-SHRINK; precondition = TID holds the named locks):
  :owner+:extent  (:issue TID CID INC EOFF ELEN TRAILER) = `fn-pio-direct-admit` on the first idle
                  worker (refused unless INC is bound by some fd and not CLOSED); then the actor's
                  (:io-begin TID FD TOKEN)
                  (:settle TID TOKEN) = `fn-pio-direct-settle` with RESULTS' verdict: :publish |
                  :cancelled | (:fault V) | :stale
  :extent         (:cancel TID TOKEN) = `fn-pio-cancel` (the deadline); (:return TID TOKEN) =
                  `fn-pxe-return` (the worker after its :io-complete)
  :pins           (:pin TID) (:unpin TID G) = `fn-arpn-step`; (:capture TID CID) (:drain TID CID) =
                  `fn-rpin-step`; (:retire TID ITEMS) (:release TID) = `fn-arpn-step`
  :owner+:extent+:pins
                  (:close TID INC) enabled iff INC is an item of a retirement `(:release)` answered
                  AND `(fn-pio-file-clear-p INC ROWS)`; then the primitive :fd-close of INC's fds
                  (:swap TID G ITEMS) enabled iff `(fn-arpn-count PINS)` <= 1 with the pass's own pin
                  at G; it is `(:retire ITEMS)` of the old generation

THEOREMS (as I intend to write them; `(fn-hmc-run st sched)` folds `fn-hmc-step`; every theorem is over
EVERY sched, from `(fn-hmc-init)`):

  (defthm fn-hmc-run-keeps-invp                                                   ; PRF-1242
    (fn-hmc-invp (fn-hmc-run (fn-hmc-init) sched)))
  ;; fn-hmc-invp: fn-arpn-okp; OWNERS funded (every (cid . g): (fn-arpn-pins-of g PINS) >= count at g);
  ;; every row fn-pio-rowp with distinct ids below NEXT; every worker fn-pxe-rowp; a :running/:returned
  ;; worker's token names an unsettled row; an unsettled row's incarnation is bound by an fd and not
  ;; CLOSED; every REQS entry's token names an unsettled row and its INC is that row's; FDS binds an
  ;; incarnation to at most one fd; LOCKS holders are tids.

  (defthm fn-hmc-an-unsettled-read-keeps-its-incarnation-open                    ; PRF-1243, T1(b).1
    (let ((st (fn-hmc-run (fn-hmc-init) sched)))
      (implies (and (member-equal r (fn-hmc-rows st)) (not (eq (nth 6 r) :settled)))
               (and (fn-hmc-boundp (nth 2 r) (fn-hmc-fds st))
                    (not (member-equal (nth 2 r) (fn-hmc-closed st)))))))
  ;; retirement, release, close and swap interleaved arbitrarily never close a file an issued or
  ;; cancelled read names: r31 F1 is unreachable in the model; fn-pgs-fill-realize (no row) is not an
  ;; instance of :issue and so is not covered -- stated in the book.

  (defthm fn-hmc-close-is-refused-while-a-read-names-the-file
    (let ((st (fn-hmc-run (fn-hmc-init) sched)))
      (implies (and (member-equal r (fn-hmc-rows st)) (not (eq (nth 6 r) :settled))
                    (equal (nth 2 r) inc))
               (equal (fn-hmc-step st (list :close tid inc)) st))))

  (defthm fn-hmc-a-request-in-flight-reads-its-own-incarnation                   ; PRF-1243, T1(b).2
    (let ((st (fn-hmc-run (fn-hmc-init) sched)))
      (implies (member-equal req (fn-hmc-reqs st))
               (and (equal (fn-hmc-fd-of (cdr req) (fn-hmc-fds st)) ...)        ; the fd still bound
                    (equal (nth 2 (fn-hmc-row-of (car req) (fn-hmc-rows st))) (cdr req))))))
  ;; no fd number named by an in-flight read is rebound before its completion: an :io-complete always
  ;; delivers the incarnation the row names (the OS-reuse half of r31 F1).

  (defthm fn-hmc-settle-publishes-only-its-own-token-once                        ; PRF-1244, T1(b).3
    (let* ((st (fn-hmc-run (fn-hmc-init) sched))
           (st1 (fn-hmc-step st (list :settle tid token))))
      (and (implies (equal (fn-hmc-answer st1) :publish)
                    (let ((row (fn-hmc-row-of token (fn-hmc-rows st))))
                      (and (fn-pio-rowp row) (equal (fn-pio-token row) token) (eq (nth 6 row) :issued)
                           (equal (nth 2 (fn-hmc-worker-of token (fn-hmc-workers st))) :returned)
                           (equal (cdr (assoc-equal token (fn-hmc-results st))) :ok))))
           (equal (fn-hmc-answer (fn-hmc-step st1 (list :settle tid2 token))) :stale)
           (equal (fn-hmc-rows (fn-hmc-step st1 (list :settle tid2 token))) (fn-hmc-rows st1)))))
  ;; page-read-direct's four settle keystones lifted through the run: the uniqueness of the token's
  ;; row (invariant) is what makes "its own" meaningful across every interleaving.

  (defthm fn-hmc-release-postdates-every-live-pin                                ; PRF-1244
    (let* ((st (fn-hmc-run (fn-hmc-init) sched))
           (rel (fn-hmc-answer (fn-hmc-step st (list :release tid)))))
      (implies (and (member-equal e rel)
                    (< 0 (fn-arpn-pins-of h (second (fn-hmc-arpn (fn-hmc-step st (list :release tid)))))))
               (< (car e) h))))
  ;; fn-arpn-release-postdates-every-live-pin with :pin/:capture/:swap interleaved: a generation pin,
  ;; a reader's or a response's, is never invalidated by a release.

  (defthm fn-hmc-a-held-response-refuses-the-swap
    (let ((st (fn-hmc-run (fn-hmc-init) sched)))
      (implies (consp (fn-hmc-owners st))
               (equal (fn-hmc-step st (list :swap tid g items)) st))))

  (defthm fn-hmc-crash-forgets-every-request
    (let ((st (fn-hmc-step (fn-hmc-run (fn-hmc-init) sched) '(:crash))))
      (and (null (fn-hmc-reqs st)) (null (fn-hmc-rows st))
           (equal (fn-hmc-answer (fn-hmc-step st (list :io-complete token v))) :stale))))

TEETH (tests/acl2/host-model-tests.lisp): the reached run is r31's schedule as labels -- issue A on inc
11, io-begin, cancel (deadline), retire 11, release, close 11 attempted (refused), io-complete A :ok,
return, settle (:cancelled; no publish), close 11 (now permitted); the response-pin/swap schedule
(capture cid 7, swap refused, drain, swap proceeds); a reused fd number after close bound to inc 12
with A's completion arriving late (:stale, nothing published). One hypothesis-removal per conjunct;
a labelled mutation (a :close that ignores fn-pio-file-clear-p publishes a torn read).

REALIZATION (stated in the book, never a theorem): each C-label is one host call site today
(:issue extent.lisp fnn-extent-issue-direct :988 from owner.lisp:4213; :cancel :912; :return the
executor loop :512-522; :settle :1016 from owner.lisp:4276; :pin/:unpin io.lisp:6787; :capture/:drain
owner.lisp:504; :retire/:release io.lisp:6845-6861; :close extent.lisp:1225; :swap owner.lisp:5745)
and becomes generated ACL2 under TCB-SHRINK; each P-label is one primitive of the thin layer with its
A-PRIM-* row; LOCK-CHECK's R3 polices the hand-written remainder until then.

NOT COVERED by v1 (next increments, in order): the semantic state and replies (T1(a): `fn-ocfg-run`
as the :owner section's step; the plan/render labels); the barrier ledger `fn-otb` as :io-begin/
:io-complete of the fsync; the reader view `fn-ocvm`; crash as cuts of the byte programs (T1(c));
liveness. Effort for v1: 1-2 weeks, ~800-1,200 lines of book + tests, certified on hbox.

## 2. P2 / M6 / P8 under the carried relation (deliverable 2)

The bridge carried => static CANNOT be proved: `fn-own-conn-okp` (owner-invariants-relation.lisp:130)
replays the connection's prefix with the Store's CURRENT groups and capacity (`fn-own-prefix-archive
groups capacity records version frontier`); `fn-ocl-conn-historyp` (config-owner-live-complete.lisp:145)
replays the config history (`fn-cst-replay-node config-prefix event-prefix frontier`); after a live
reconfiguration they differ, which is why the host carries the historical one (owner-tls-prefix.lisp:376).
So RESTATE, do not bridge:
- M6/P8: `fn-lgoc-own-read-is-served-step-on-pinned-prefix`: under `fn-ocl-relation`, `(car (fn-own-read
  (fn-ocfg-owner oc) id octets fn-arena))` = `fn-served-step` at the connection's archive, the archive
  being `fn-ctl-visible-state-of` of the acceptance of `fn-cst-replay-node` over the pinned config and
  event prefixes (the static theorem's proof with `fn-ocl-conn-historyp`'s `fn-ctl-projectionp` in place
  of `fn-own-conn-okp`'s); M6's and P8's keystones re-chain through it unchanged; current-view.json's
  bridge field moves to the new theorem.
- P2: `fn-lgoc-240-follows-consumed-completion` under `fn-lgoc-invariantp` (`fn-cst-relation` for
  `fn-snt-relation`; the session shape from `fn-ocl-conn-historyp`); the outcome half already exists
  carried (`fn-acar-own-outcome-is-reference-under-ocl-relation`, owner-advance-carried.lisp:483).
Order: M6/P8's read theorem first (one theorem, two rows re-chain), P2 second. 1-2 weeks; a second
lane could take P2 in parallel.

## 3. P10 (deliverable 3)

Keystone -> `fn-lg-open-program-keeps-the-relation-at-every-cut` (new; `fn-lg-recover-program-
establishes-the-relation` store-log-programs.lisp:183 composed with `fn-lg-open-suffix-keeps-the-
relation` store-log-route-programs.lisp:97 over `fn-lg-run` of the whole `fn-lg-open-program`, whose
cuts are tests/campaign/native_cuts.py RECOVERY_CUTS); bridge -> `fn-lgoc-recover-installs-invariant`
(owner-log-ocl.lisp; host fn-ock-recover-extended, the sidecar's host function already); PRF-041's
per-file events get the `unreachable-in-composition` disposition (planning/reach-baseline.json) and the
registry note names the log route; the sidecar's "latest" drops the marker program; current.md
regenerated on a box. Half a day plus a certify of the two books' closure.

## State
- 2026-10-03: worktree made; ids claimed; plan sent to the coordinator; starting the book.

## CONTINUATION (written by the coordinator, 2026-10-03; the COMPOSITION deputy's context ran out mid-work)
- Branch lane/host-model @ 9300e2a7d (pushed). Finished before that: the P10 replacement (open-program keystone,
  its events registered, teeth at floor 0) in c173884ba and earlier.
- WIP, UNVERIFIED: books/host-model.lisp (1,779 lines, HM v1) and tests/acl2/host-model-tests.lisp (7 lines, a stub).
  Never admitted as a whole, never certified. Next: admit it in a REPL, apply host-model-review-1.md's must-fixes
  (M1 lease labels, M2 -by-definition names, M3 the *fn-hmc-realization* defconst in LOCK-CHECK's format, M4 the
  P10 cut coordinates) if not already in, write the teeth, certify, then the carried read theorem (P2/M6/P8).

## Runtime primitive observation consumer, 2026-10-03

The actual generated actor reserves its existing physical gensym before the
thread maker. `fnn-native-observed-thread-thunk` carries its exact symbol-name
string into the child; observation-only executor startup can use the same
reservation primitive once before its maker. This is a native trace identity,
not a semantic actor identity, resource generation or accounting claim.

The current shared site is `fnn-section-envelope` through
`fnn-with-observed-owner`, rather than the historical `fnn-owner-gated`
realization-table row. Acquire is recorded after physical owner acquisition.
Release gets its producer position while O is held and is marked complete
only after physical unlock. An observer reader exposes only the completed
prefix in that reservation order. It never sorts timestamps or reconstructs
thread aliases. The only nested observer lock is O -> private observer mutex;
there is no callback, I/O, ACL2 evaluation or acquisition of O under that
private mutex. Direct stop/fault O entries and other locks remain outside
this first producer slice.

`fnn-native-observe(EVENT)` accepts an already measured literal label when
`*fnn-native-observer*` is dynamically present. The explicit developer capacity
preallocates record rows before children start. NIL identity, overflow or an
observer condition makes comparison unavailable; no fn fault or admission
decision follows from instrumentation.

`tests/test_native_observation_raw.sh` runs actual generated actor/section
code and forces a first actor to pause after unlock before release completion
while a second actor enters and leaves O. The reader reports the first
acquire as a pending prefix, then the completed reservation order
acquire1/release1/acquire2/release2. It also checks actual observation-only
child startup, failed maker, invalidation and preservation of section values.
It writes literal `assert-event` forms to
`build/runtime-tests/native-observation-hm.lsp` for the loaded HM machine:
exact held/released answers and `fn-hmc-invp` at every observed prefix.
Finite replay is not an all-schedules proof or an image qualification.
Empirical owns the next actual extent-label consumer on this frozen seam.

Groundwork replayed all four exact producer-emitted assertion packets in the
clean protected `hmc-direct-read` world: PASS, <0.01 seconds and zero proof
steps. Startup reused ten exact cached dependencies (0.87 seconds / 532,452
steps). The source producer is d4cb69168; the native log, literal replay-input
transcript and machine/packet hashes are filed under
`planning/evidence/runtime-observation-2026-10-03/`. This first packet checks
finite O-only behavior. It does not qualify the image or missing PageIO/pins
primitive sites, and leaves PRF-1254 planned.

The next actual-image consumer activation is in `fnn-owner-run` before
`fnn-owner-install`, gated by the existing developer-only
`FN_NATIVE_PAGE_IO_HOLD` selector. It creates an explicit 4096-row observation
profile and binds a physical reservation in the current main thread. Actual
mux startup captures a fresh identity through the shared observed child thunk.
After owner unwind the bounded stderr readout is
`NATIVE-HM (STATUS REASON EVENTS)`. Activation allocation/readout failures do
not classify the service; failed activation reports comparison unavailable.
Native scope tests preserve startup values and supplied inactive context.
Actual image/PageIO composition remains pending; unknown plain threads still
invalidate comparison rather than receiving inferred identities.
