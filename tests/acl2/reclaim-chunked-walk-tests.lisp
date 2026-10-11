; fn: witnesses and teeth for books/reclaim-chunked-walk.lisp over the owner
; fixture's store (*rpt-s*, its arena *rpt-payloads*) and the expiring
; context over it (*xt-ctx*, books/expiry-instant: every article expired).
(in-package "ACL2")
(include-book "../../books/reclaim-chunked-walk")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")
(include-book "arena-lift")
(include-book "expiry-tests")
; Ground terms below reach the record codec seam: its attachment, and each
; constant through it as a make-event (books/codec-attach.lisp).
(include-book "../../books/codec-attach")

;; The accumulator steps are guarded by the carried invariant
;; (fn-rcw-acc-carriedp), whose fn-rii-okp is a defun-sk: no evaluator runs
;; it, and guard checking cannot be switched off for a whole book.  Every
;; ground call of a value function below therefore runs under
;; (with-guard-checking :none ...), as tests/acl2/acceptance-tests.lisp runs
;; its out-of-guard calls; the invariant itself is witnessed by proved ground
;; facts (:witness-lemma, :lemma).

(defconst *rcw-rows* (fn-sf-records (fn-sn-files *rpt-s*)))
(defconst *rcw-configs* (list *xt-star*))
(assert-event (with-guard-checking :none (<= 3 (len *rcw-rows*))))

; The rewritten history the pass 2/3 walks produce (the offline rewrite of
; every captured row), whole and in two chunkings.
(bpr-lift fn-orc-rewrite-rows 2)
(make-event `(defconst *rcw-new* ',(with-guard-checking :none (in-arena-fn-orc-rewrite-rows *rpt-payloads* *rcw-rows* *xt-ctx*))))
(defconst *rcw-c1* (list (take 1 *rcw-new*) (nthcdr 1 *rcw-new*)))
(defconst *rcw-c2* (list (take 2 *rcw-new*) nil (nthcdr 2 *rcw-new*)))
(assert-event (with-guard-checking :none (equal (fn-rcw-concat *rcw-c1*) *rcw-new*)))
(assert-event (with-guard-checking :none (equal (fn-rcw-concat *rcw-c2*) *rcw-new*)))

; -----------------------------------------------------------------------------
; 1. KEYSTONE fn-rcw-acc-steps-is-capture, reached: both chunkings finish to
; the capture of the whole rewritten history, and the capture is not the
; capture of nothing (the premise is inhabited by a real history).
(defconst *rcw-whole* (fn-sco-capture *rcw-configs* *rcw-new*))
(defmacro rcw-acc (chunks)
  `(fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*) *rcw-configs* ,chunks)))
(assert-event (with-guard-checking :none (equal (rcw-acc *rcw-c1*) *rcw-whole*)))
(assert-event (with-guard-checking :none (equal (rcw-acc *rcw-c2*) *rcw-whole*)))
(assert-event (with-guard-checking :none (not (equal *rcw-whole* (fn-sco-capture *rcw-configs* nil)))))
; Teeth (mutation): the chunks in another order are another history, and
; a dropped chunk is a shorter one.
(must-fail-checked
 (assert-event (with-guard-checking :none (equal (rcw-acc (list (nthcdr 1 *rcw-new*) (take 1 *rcw-new*))) *rcw-whole*))))
(must-fail-checked
 (assert-event (with-guard-checking :none (equal (rcw-acc (list (take 1 *rcw-new*))) *rcw-whole*))))
; The carried count is the record count, and the accumulator invariant holds.
(assert-event (with-guard-checking :none (fn-rcw-accp (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*) *rcw-configs* *rcw-c2*))))
(assert-event (with-guard-checking :none (equal (fn-rcw-acc-n (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*)
                                                     *rcw-configs* *rcw-c2*))
                     (len *rcw-new*))))

; -----------------------------------------------------------------------------
; 2. KEYSTONE fn-rcw-canon-acc-steps-is-the-checkpoint-capture, reached: the
; pass-2 steps over the chunks finish to the capture of the canonical rows
; of the whole history, handles from 0, and the final handle is the count of
; sealed payloads.
(bpr-lift fn-rcw-canon-acc-steps 4)
(defun rcw-canon-of (rows h fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-scka-canon-rows rows fn-arena h (fn-stxk-initial-context 0)))
(bpr-lift rcw-canon-of 2)
(bpr-lift fn-rcw-seal-count 1)
(make-event `(defconst *rcw-canon* ',(with-guard-checking :none (in-arena-rcw-canon-of *rpt-payloads* *rcw-new* 0))))
(assert-event (with-guard-checking :none (not (eq *rcw-canon* :bad))))
(make-event `(defconst *rcw-p2* ',(with-guard-checking :none (in-arena-fn-rcw-canon-acc-steps *rpt-payloads* (fn-rcw-acc-init *rcw-configs*)
                                                    *rcw-configs* *rcw-c2* 0))))
(assert-event (with-guard-checking :none (not (eq *rcw-p2* :bad))))
(assert-event (with-guard-checking :none (equal (fn-rcw-acc-finish (car *rcw-p2*))
                     (fn-sco-capture *rcw-configs* *rcw-canon*))))
(assert-event (with-guard-checking :none (equal (cadr *rcw-p2*)
                     (in-arena-fn-rcw-seal-count *rpt-payloads* *rcw-new*))))
(assert-event (with-guard-checking :none (< 0 (cadr *rcw-p2*))))
; Teeth: starting the second chunk's handles at 0 again (a host that did not
; carry H) is not the checkpoint's capture.
(make-event `(defconst *rcw-p2-reset* ',(with-guard-checking :none (let ((a (in-arena-fn-rcw-canon-acc-steps *rpt-payloads* (fn-rcw-acc-init *rcw-configs*)
                                            *rcw-configs* (list (take 2 *rcw-new*)) 0)))
    (in-arena-fn-rcw-canon-acc-steps *rpt-payloads* (car a) *rcw-configs*
                                     (list (nthcdr 2 *rcw-new*)) 0)))))
(must-fail-checked
 (assert-event (with-guard-checking :none (equal (fn-rcw-acc-finish (car *rcw-p2-reset*))
                      (fn-sco-capture *rcw-configs* *rcw-canon*)))))

;; -----------------------------------------------------------------------------
;; 1b. The carried invariant (R1-R3) reached.
;;
;; R2: each step's configuration fold is the checkpoint's resume
;; (fn-rcw-acc-step-cpr-is-resume); R3: a configured pause carries the tries
;; (fn-rcw-acc-step-carries-a-configured-pause).  The owner fixture's rewritten
;; rows fault the configuration fold in its first chunk, so R3's premise is
;; empty there; the store-finalize-incremental history below (an undertaking,
;; its release, five articles) holds the pause, and R3 is checked non-vacuously
;; on it.  Executable stand-ins: the invariant itself is a defun-sk.
(defun rcw-t-r2 (acc configs chunks)
  (declare (xargs :mode :program))
  (if (consp chunks)
      (and (equal (fn-sco-at 2 (fn-rcw-acc-step acc configs (car chunks)))
                  (fn-sco-cpr-resume (fn-sco-at 2 acc) configs (true-list-fix (car chunks))))
           (rcw-t-r2 (fn-rcw-acc-step acc configs (car chunks)) configs (cdr chunks)))
    t))

; (number of steps whose result is a configured pause, or :violated when one
; is a configured pause that carries no tries)
(defun rcw-t-r3 (acc configs chunks)
  (declare (xargs :mode :program))
  (if (consp chunks)
      (let* ((next (fn-rcw-acc-step acc configs (car chunks)))
             (r (fn-sco-at 2 next))
             (configured (and (fn-sco-pausedp r) (fn-cnode-statep (fn-sco-at 1 r))))
             (rest (rcw-t-r3 next configs (cdr chunks))))
        (cond ((or (eq rest :violated) (and configured (not (fn-rcw-acc-ix next)))) :violated)
              (t (+ (if configured 1 0) rest))))
    0))

(assert-event (with-guard-checking :none (rcw-t-r2 (fn-rcw-acc-init *rcw-configs*) *rcw-configs* *rcw-c2*)))
(assert-event (with-guard-checking :none (equal (rcw-t-r3 (fn-rcw-acc-init *rcw-configs*) *rcw-configs* *rcw-c2*) 0)))

(defconst *rcw-t-stamp* *fn-cfg-default-stamp*)
(defun rcw-t-article (sequence txid msgid obligation)
  (fn-held-plain (fn-record-make sequence txid txid msgid '(65) '("fn.test")
                                 obligation "subject" "evidence" 2 841000000)
                 sequence))
(defconst *rcw-t-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *rcw-t-stamp*)
        (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 20)) *rcw-t-stamp*)))
(defconst *rcw-t-rows*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-sfi" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-sfi" "subject" "evidence" 0)
        (rcw-t-article 2 7 "<sfi@example.invalid>" "archive-sfi")
        (rcw-t-article 3 8 "<sfi-2@example.invalid>" "archive-sfi-2")
        (rcw-t-article 4 9 "<sfi-3@example.invalid>" "archive-sfi-3")
        (rcw-t-article 5 10 "<sfi-4@example.invalid>" "archive-sfi-4")
        (rcw-t-article 6 11 "<sfi-5@example.invalid>" "archive-sfi-5")))
(defun rcw-t-singles (l) (if (consp l) (cons (list (car l)) (rcw-t-singles (cdr l))) nil))
(defconst *rcw-t-c1* (list (take 1 *rcw-t-rows*) (nthcdr 1 *rcw-t-rows*)))
(defconst *rcw-t-c2* (list (take 2 *rcw-t-rows*) nil (nthcdr 2 *rcw-t-rows*)))
(defconst *rcw-t-c3* (rcw-t-singles *rcw-t-rows*))
(assert-event (with-guard-checking :none (equal (fn-rcw-concat *rcw-t-c3*) *rcw-t-rows*)))

; the keystone on this history, three chunkings
(assert-event
(with-guard-checking :none  (and (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* *rcw-t-c1*))
             (fn-sco-capture *rcw-t-configs* *rcw-t-rows*))
      (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* *rcw-t-c2*))
             (fn-sco-capture *rcw-t-configs* *rcw-t-rows*))
      (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* *rcw-t-c3*))
             (fn-sco-capture *rcw-t-configs* *rcw-t-rows*)))))
(assert-event (with-guard-checking :none (rcw-t-r2 (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* *rcw-t-c1*)))
(assert-event (with-guard-checking :none (rcw-t-r2 (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* *rcw-t-c2*)))
(assert-event (with-guard-checking :none (rcw-t-r2 (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* *rcw-t-c3*)))
; R3 non-vacuous: every chunk's result here is a configured pause carrying tries
(assert-event (with-guard-checking :none (equal (rcw-t-r3 (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* *rcw-t-c3*) 7)))
(assert-event (with-guard-checking :none (equal (rcw-t-r3 (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* *rcw-t-c1*) 2)))

; The tries after the last chunk do not depend on the chunking.
(assert-event
(with-guard-checking :none  (equal (fn-rcw-acc-ix (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* *rcw-t-c3*))
        (fn-rcw-acc-ix (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* *rcw-t-c1*)))))

; TEETH-62 BEGIN
; The two PRF reclaim-chunked-walk keystones with their teeth (TEETH CONTRACT v1).
; The value fold's guard carries the invariant, which no evaluator runs: the
; witness and both mutants are proved ground facts (:witness-lemma, :lemma).
(defthm rcw-steps-is-capture-witness
  (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*) *rcw-configs* *rcw-c2*))
         (fn-sco-capture *rcw-configs* (fn-rcw-concat *rcw-c2*)))
  :hints (("Goal" :use ((:instance fn-rcw-acc-steps-is-capture
                                   (configs *rcw-configs*) (chunks *rcw-c2*)))
           :in-theory (disable (:executable-counterpart fn-rcw-acc-steps)
                               (:executable-counterpart fn-rcw-acc-finish)
                               fn-rcw-acc-steps fn-rcw-acc-finish fn-rcw-acc-init
                               fn-rcw-acc-steps-is-capture))))

(defthm rcw-steps-is-capture-mutant-empty
  (and (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*) *rcw-configs* *rcw-c2*))
              (fn-sco-capture *rcw-configs* (fn-rcw-concat *rcw-c2*)))
       (not (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*) *rcw-configs* *rcw-c2*)) (fn-sco-capture *rcw-configs* nil))))
  :hints (("Goal" :use ((:instance fn-rcw-acc-steps-is-capture
                                   (configs *rcw-configs*) (chunks *rcw-c2*)))
           :in-theory (disable (:executable-counterpart fn-rcw-acc-steps)
                               (:executable-counterpart fn-rcw-acc-finish)
                               fn-rcw-acc-steps fn-rcw-acc-finish fn-rcw-acc-init
                               fn-rcw-acc-steps-is-capture))))

(defthm rcw-steps-is-capture-mutant-reversed
  (and (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*) *rcw-configs* *rcw-c2*))
              (fn-sco-capture *rcw-configs* (fn-rcw-concat *rcw-c2*)))
       (not (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*) *rcw-configs* *rcw-c2*))
                   (fn-sco-capture *rcw-configs* (fn-rcw-concat (reverse *rcw-c2*))))))
  :hints (("Goal" :use ((:instance fn-rcw-acc-steps-is-capture
                                   (configs *rcw-configs*) (chunks *rcw-c2*)))
           :in-theory (disable (:executable-counterpart fn-rcw-acc-steps)
                               (:executable-counterpart fn-rcw-acc-finish)
                               fn-rcw-acc-steps fn-rcw-acc-finish fn-rcw-acc-init
                               fn-rcw-acc-steps-is-capture))))

(defteeth fn-rcw-acc-steps-is-capture
  :claim (()
          (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init configs) configs chunks))
         (fn-sco-capture configs (fn-rcw-concat chunks))))
  :subject fn-rcw-acc-steps
  :witness ((configs *rcw-configs*) (chunks *rcw-c2*))
  :witness-lemma rcw-steps-is-capture-witness
  :mutations ((empty-history
               (:conclusion (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init configs) configs chunks)) (fn-sco-capture configs nil)))
               ((configs *rcw-configs*) (chunks *rcw-c2*))
               :fault "the walk finishing to the capture of an empty history"
               :lemma rcw-steps-is-capture-mutant-empty)
              (chunks-reversed
               (:conclusion (equal (fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init configs) configs chunks)) (fn-sco-capture configs (fn-rcw-concat (reverse chunks)))))
               ((configs *rcw-configs*) (chunks *rcw-c2*))
               :fault "the chunks concatenated in the wrong order"
               :lemma rcw-steps-is-capture-mutant-reversed)))

;; fn-rcw-finish-of-step with the carried invariant as a hypothesis.  The
;; invariant is a defun-sk, so no evaluator runs it: the positive witness, the
;; mutation and both removals are proved ground facts (:witness-lemma, :lemma),
;; each the conjunction the teeth contract names.
;;
;; The invariant's removal: ACC holds the tries of a LATER state (the state
;; after five rows) while its fold is paused after three.  The step then
;; refuses the fourth row, which the checkpoint's resume admits, so the
;; finish differs from the checkpoint extension (rcw-finish-of-step-break-carried
;; proves it; the invariant fails, rcw-stale-is-not-carried).  An accumulator
;; holding the tries of an EARLIER state (the init's, after any chunk) does not
;; show the difference: the node refuses a duplicate on its own.
(defconst *rcw-t-acc3*
  (with-guard-checking :none
    (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* (list (take 3 *rcw-t-rows*)))))
(defconst *rcw-t-acc5*
  (with-guard-checking :none
    (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-t-configs*) *rcw-t-configs* (list (take 5 *rcw-t-rows*)))))
; the accumulator after three rows holding the tries of the state after five
(defconst *rcw-t-stale* (update-nth 7 (fn-rcw-acc-ix *rcw-t-acc5*) *rcw-t-acc3*))
(defconst *rcw-t-next* (list (nth 3 *rcw-t-rows*)))


(defthm rcw-carriedp-of-update-count
  (equal (fn-rcw-acc-carriedp (update-nth 1 v acc))
         (fn-rcw-acc-carriedp acc))
  :hints (("Goal" :in-theory (enable fn-rcw-acc-carriedp fn-rcw-acc-ix fn-sco-at))))

(defthm rcw-count-carried-fact
  (fn-rcw-acc-carriedp (update-nth 1 7 (fn-rcw-acc-init *rcw-configs*)))
  :hints (("Goal" :in-theory (disable (:executable-counterpart fn-rcw-acc-init)
                                      (:executable-counterpart fn-rcw-acc-carriedp)
                                      fn-rcw-acc-init fn-rcw-acc-carriedp)
           :use ((:instance fn-rcw-acc-carriedp-of-init (configs *rcw-configs*))))))

(defthm rcw-finish-of-step-break-accumulator
  (and (fn-rcw-acc-carriedp (update-nth 1 7 (fn-rcw-acc-init *rcw-configs*)))
       (not (fn-rcw-accp (update-nth 1 7 (fn-rcw-acc-init *rcw-configs*))))
       (not (equal (fn-rcw-acc-finish (fn-rcw-acc-step (update-nth 1 7 (fn-rcw-acc-init *rcw-configs*))
                                                       *rcw-configs* (take 1 *rcw-new*)))
                   (fn-sco-extend (fn-rcw-acc-finish (update-nth 1 7 (fn-rcw-acc-init *rcw-configs*)))
                                  *rcw-configs* (true-list-fix (take 1 *rcw-new*))))))
  :hints (("Goal" :use rcw-count-carried-fact
           :in-theory (disable (:executable-counterpart fn-rcw-acc-carriedp) rcw-count-carried-fact))))

(defthm rcw-stale-is-not-carried
  (not (fn-rcw-acc-carriedp *rcw-t-stale*))
  :hints (("Goal" :in-theory (enable fn-rcw-acc-carriedp fn-sfi-cpr-carriedp fn-rii-okp fn-rcw-acc-ix fn-sco-at))))

(defthm rcw-finish-of-step-break-carried
  (and (fn-rcw-accp *rcw-t-stale*)
       (not (fn-rcw-acc-carriedp *rcw-t-stale*))
       (not (equal (fn-rcw-acc-finish (fn-rcw-acc-step *rcw-t-stale* *rcw-t-configs* *rcw-t-next*))
                   (fn-sco-extend (fn-rcw-acc-finish *rcw-t-stale*) *rcw-t-configs*
                                  (true-list-fix *rcw-t-next*)))))
  :hints (("Goal" :use rcw-stale-is-not-carried
           :in-theory (disable (:executable-counterpart fn-rcw-acc-carriedp) rcw-stale-is-not-carried))))

(defthm rcw-finish-of-step-mutation
  (and (fn-rcw-accp (fn-rcw-acc-init *rcw-configs*))
       (fn-rcw-acc-carriedp (fn-rcw-acc-init *rcw-configs*))
       (equal (fn-rcw-acc-finish (fn-rcw-acc-step (fn-rcw-acc-init *rcw-configs*) *rcw-configs* (take 1 *rcw-new*)))
              (fn-sco-extend (fn-rcw-acc-finish (fn-rcw-acc-init *rcw-configs*)) *rcw-configs*
                             (true-list-fix (take 1 *rcw-new*))))
       (not (equal (fn-rcw-acc-finish (fn-rcw-acc-step (fn-rcw-acc-init *rcw-configs*) *rcw-configs* (take 1 *rcw-new*)))
                   (fn-rcw-acc-finish (fn-rcw-acc-init *rcw-configs*)))))
  :hints (("Goal" :use ((:instance fn-rcw-finish-of-step
                                   (acc (fn-rcw-acc-init *rcw-configs*)) (configs *rcw-configs*)
                                   (chunk (take 1 *rcw-new*)))
                        (:instance fn-rcw-accp-of-init (configs *rcw-configs*))
                        (:instance fn-rcw-acc-carriedp-of-init (configs *rcw-configs*))))))

(defthm rcw-finish-of-step-witness
  (and (fn-rcw-accp (fn-rcw-acc-init *rcw-configs*))
       (fn-rcw-acc-carriedp (fn-rcw-acc-init *rcw-configs*))
       (equal (fn-rcw-acc-finish (fn-rcw-acc-step (fn-rcw-acc-init *rcw-configs*) *rcw-configs* (take 1 *rcw-new*)))
              (fn-sco-extend (fn-rcw-acc-finish (fn-rcw-acc-init *rcw-configs*)) *rcw-configs*
                             (true-list-fix (take 1 *rcw-new*)))))
  :hints (("Goal" :use ((:instance fn-rcw-finish-of-step
                                   (acc (fn-rcw-acc-init *rcw-configs*)) (configs *rcw-configs*)
                                   (chunk (take 1 *rcw-new*)))
                        (:instance fn-rcw-accp-of-init (configs *rcw-configs*))
                        (:instance fn-rcw-acc-carriedp-of-init (configs *rcw-configs*))))))


(defteeth fn-rcw-finish-of-step
  :claim (((accumulator (fn-rcw-accp acc))
           (carried (fn-rcw-acc-carriedp acc)))
          (equal (fn-rcw-acc-finish (fn-rcw-acc-step acc configs chunk))
                  (fn-sco-extend (fn-rcw-acc-finish acc) configs (true-list-fix chunk))))
  :subject fn-rcw-acc-step
  :witness ((acc (fn-rcw-acc-init *rcw-configs*)) (configs *rcw-configs*) (chunk (take 1 *rcw-new*)))
  :witness-lemma rcw-finish-of-step-witness
  :breaks ((accumulator ((acc (update-nth 1 7 (fn-rcw-acc-init *rcw-configs*))) (configs *rcw-configs*) (chunk (take 1 *rcw-new*))) :logical "an accumulator whose carried count is not its record count: outside the guard of the invariant" :lemma rcw-finish-of-step-break-accumulator)
           (carried ((acc *rcw-t-stale*) (configs *rcw-t-configs*) (chunk *rcw-t-next*)) :logical "an accumulator holding the tries of a later state: the invariant fails, and the step refuses a row it should admit" :lemma rcw-finish-of-step-break-carried))
  :mutations ((chunk-not-extended
               (:conclusion (equal (fn-rcw-acc-finish (fn-rcw-acc-step acc configs chunk)) (fn-rcw-acc-finish acc)))
               ((acc (fn-rcw-acc-init *rcw-configs*)) (configs *rcw-configs*) (chunk (take 1 *rcw-new*)))
               :fault "a chunk step that leaves the capture where it was"
               :lemma rcw-finish-of-step-mutation)))

; Host fnn-owner-reclaim-pass: tests/test_native_reclaim_walk.py::
; test_a_pass_longer_than_two_chunks_installs_and_counts_the_available.
; The local arena is filled by sealing the owner fixture's payloads.
;
; The pass-2 steps are guarded by the carried invariant, whose defun-sk no
; evaluator runs: the positive witness runs under (with-guard-checking :none)
; (:witness-unguarded), and the mutation is a ground theorem (:logical) that
; names the faulty host's result at the specification level instead of running
; its steps.  IMPLEMENTATION MUTATION: fail to carry the next handle across
; chunks.  A host that did so would stage the capture of the first chunk's
; canonical rows from handle 0 and the second chunk's from handle 0 again,
; interned from the identity the first left; the mutant conclusion says the
; steps finish to that capture.  The check proves the keystone's instance at
; the mutation's witness (the steps finish to the capture of the whole canonical
; rows) and that the two captures differ.
(defteeth fn-rcw-canon-acc-steps-is-the-checkpoint-capture
  :claim (()
    (let ((r (fn-rcw-canon-acc-steps (fn-rcw-acc-init configs) configs chunks 0 fn-arena))
          (all (fn-scka-canon-rows (fn-rcw-concat chunks) fn-arena 0 (fn-stxk-initial-context 0))))
      (and (equal (eq r :bad) (eq all :bad))
           (implies (not (eq r :bad))
                    (equal (fn-rcw-acc-finish (car r)) (fn-sco-capture configs all))))))
  :subject fn-rcw-canon-acc-steps
  :witness ((configs *rcw-configs*) (chunks *rcw-c2*))
  :stobjs ((fn-arena (fn-arn-seal-many *rpt-payloads* fn-arena)))
  :witness-unguarded "the step's verified guard is the carried invariant, which holds a defun-sk (fn-rii-okp) the evaluator cannot run"
  :mutations ((reset-handle
               (:conclusion
                (let ((r (fn-rcw-canon-acc-steps (fn-rcw-acc-init configs) configs chunks 0 fn-arena)))
                  (equal (fn-rcw-acc-finish (car r))
                         (fn-sco-capture
                          configs
                          (append (fn-scka-canon-rows (car chunks) fn-arena 0 (fn-stxk-initial-context 0))
                                  (fn-scka-canon-rows (cadr chunks) fn-arena 0
                                                      (fn-replay-identity-loop
                                                       (fn-scka-canon-rows (car chunks) fn-arena 0
                                                                           (fn-stxk-initial-context 0))
                                                       (fn-stxk-initial-context 0))))))))
               ((configs *rcw-configs*) (chunks (list (take 2 *rcw-new*) (nthcdr 2 *rcw-new*))))
               :fault "the pass-2 loop restarts the second chunk at handle zero"
               :logical "the steps' guard reaches the carried invariant's defun-sk"))
  :hints (("Goal" :use ((:instance fn-rcw-canon-acc-steps-is-the-checkpoint-capture
                                   (configs *rcw-configs*)
                                   (chunks (list (take 2 *rcw-new*) (nthcdr 2 *rcw-new*)))
                                   (fn-arena (fn-arn-seal-many *rpt-payloads* (create-fn-arena)))))
           :in-theory (disable (:executable-counterpart fn-rcw-canon-acc-steps)
                               (:executable-counterpart fn-rcw-acc-init)
                               (:executable-counterpart fn-rcw-acc-finish)
                               fn-rcw-canon-acc-steps fn-rcw-acc-finish fn-rcw-acc-init
                               fn-rcw-canon-acc-steps-is-the-checkpoint-capture))))
; KEYSTONE fn-rcwacc-canon-steps-is-the-checkpoint-capture: the same pass over
; the host's stobj accumulator (fn-rcwacc), from the fresh stobj
; (fn-rcwacc-init).  The claim's multiple-value call is bound by a LET, which
; no executable conjunct can state, so the positive witness runs through a
; native checker (:stobj-checks) that the defteeth proves equal to the claim.
; It runs unguarded for the value keystone's reason.  The mutation is the value
; keystone's, on the stobj: the second chunk restarts at handle zero.
(defun rcw-t-canon-check (configs chunks fn-arena fn-rcwacc)
  (declare (xargs :stobjs (fn-arena fn-rcwacc) :verify-guards nil))
  (let ((fn-rcwacc (fn-rcwacc-init configs fn-rcwacc)))
    (mv-let (h fn-rcwacc)
      (fn-rcwacc-canon-steps configs chunks 0 fn-arena fn-rcwacc)
      (let ((all (fn-scka-canon-rows (fn-rcw-concat chunks) fn-arena 0 (fn-stxk-initial-context 0))))
        (mv (and (equal (eq h :bad) (eq all :bad))
                 (implies (not (eq all :bad))
                          (equal (fn-rcwacc-finish fn-rcwacc) (fn-sco-capture configs all))))
            fn-arena fn-rcwacc)))))

(defteeth fn-rcwacc-canon-steps-is-the-checkpoint-capture
  :claim (()
    (let ((e (fn-rcwacc-canon-steps configs chunks 0 fn-arena (fn-rcwacc-init configs fn-rcwacc)))
          (all (fn-scka-canon-rows (fn-rcw-concat chunks) fn-arena 0 (fn-stxk-initial-context 0))))
      (and (equal (eq (mv-nth 0 e) :bad) (eq all :bad))
           (implies (not (eq all :bad))
                    (equal (fn-rcwacc-finish (mv-nth 1 e)) (fn-sco-capture configs all))))))
  :subject fn-rcwacc-canon-steps
  :witness ((configs *rcw-configs*) (chunks *rcw-c2*))
  :stobjs ((fn-arena (fn-arn-seal-many *rpt-payloads* fn-arena))
           (fn-rcwacc fn-rcwacc))
  :stobj-checks
  (((let ((e (fn-rcwacc-canon-steps configs chunks 0 fn-arena (fn-rcwacc-init configs fn-rcwacc)))
          (all (fn-scka-canon-rows (fn-rcw-concat chunks) fn-arena 0 (fn-stxk-initial-context 0))))
      (and (equal (eq (mv-nth 0 e) :bad) (eq all :bad))
           (implies (not (eq all :bad))
                    (equal (fn-rcwacc-finish (mv-nth 1 e)) (fn-sco-capture configs all)))))
    (rcw-t-canon-check configs chunks fn-arena fn-rcwacc)
    :hints (("Goal" :in-theory (enable rcw-t-canon-check)))))
  :witness-unguarded "the steps' verified guard is the carried invariant, which holds a defun-sk (fn-rii-okp) the evaluator cannot run"
  :mutations ((reset-handle
               (:conclusion
                (let ((e (fn-rcwacc-canon-steps configs chunks 0 fn-arena (fn-rcwacc-init configs fn-rcwacc))))
                  (equal (fn-rcwacc-finish (mv-nth 1 e))
                         (fn-sco-capture
                          configs
                          (append (fn-scka-canon-rows (car chunks) fn-arena 0 (fn-stxk-initial-context 0))
                                  (fn-scka-canon-rows (cadr chunks) fn-arena 0
                                                      (fn-replay-identity-loop
                                                       (fn-scka-canon-rows (car chunks) fn-arena 0
                                                                           (fn-stxk-initial-context 0))
                                                       (fn-stxk-initial-context 0))))))))
               ((configs *rcw-configs*) (chunks (list (take 2 *rcw-new*) (nthcdr 2 *rcw-new*))))
               :fault "the pass-2 loop restarts the second chunk at handle zero"
               :logical "the steps' guard reaches the carried invariant's defun-sk"))
  :hints (("Goal" :use ((:instance fn-rcwacc-canon-steps-is-the-checkpoint-capture
                                   (configs *rcw-configs*)
                                   (chunks (list (take 2 *rcw-new*) (nthcdr 2 *rcw-new*)))
                                   (fn-arena (fn-arn-seal-many *rpt-payloads* (create-fn-arena)))
                                   (fn-rcwacc (create-fn-rcwacc))))
           :in-theory (disable (:executable-counterpart fn-rcwacc-canon-steps)
                               (:executable-counterpart fn-rcwacc-init)
                               (:executable-counterpart fn-rcwacc-finish)
                               fn-rcwacc-canon-steps fn-rcwacc-finish fn-rcwacc-init
                               fn-rcwacc-canon-steps-is-the-checkpoint-capture))))

(defteeth-check (fn-rcw-acc-steps-is-capture fn-rcw-finish-of-step
                 fn-rcw-canon-acc-steps-is-the-checkpoint-capture
                 fn-rcwacc-canon-steps-is-the-checkpoint-capture))
