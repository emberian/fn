(in-package "ACL2")
(include-book "../../books/post-transaction-sim")
(include-book "../../books/post-transaction-crash")
(include-book "../../books/frame-trailer")
(include-book "../../books/codec-attach")
(include-book "../../books/defkeystone")
(include-book "teeth-ground-lemma")
(include-book "post-acceptance-tests")

(defun ptxt-acc-begin (txid) (declare (xargs :guard t) (ignore txid)) nil)
(defun ptxt-acc-feed (a octets) (declare (xargs :guard t) (ignore a octets)) (mv nil nil))
(defun ptxt-acc-feed-cost (a octets) (declare (xargs :guard t) (ignore a octets)) 0)
(defun ptxt-acc-end (a blen) (declare (xargs :guard t) (ignore a blen)) (mv t nil nil 0 nil nil))
(defun ptxt-acc-max-state () (declare (xargs :guard t)) 1)
(defun ptxt-acc-out-max () (declare (xargs :guard t)) 0)
(verify-guards ptxt-acc-begin)
(verify-guards ptxt-acc-feed)
(verify-guards ptxt-acc-feed-cost)
(verify-guards ptxt-acc-end)
(verify-guards ptxt-acc-max-state)
(verify-guards ptxt-acc-out-max)
(defattach (fn-ptx-acc-begin ptxt-acc-begin) (fn-ptx-acc-feed ptxt-acc-feed) (fn-ptx-acc-feed-cost ptxt-acc-feed-cost)
  (fn-ptx-acc-end ptxt-acc-end) (fn-ptx-acc-max-state ptxt-acc-max-state) (fn-ptx-acc-out-max ptxt-acc-out-max))


(defun ptxt-step (m ev q)
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-rtc-st
    (mv-let (r fn-rtc-st)
      (mv-let (m2 reqs c) (fn-ptx-step m ev fn-rtc-st q) (mv (list m2 reqs c) fn-rtc-st))
      r)))

; =============================================================================
; The machine's states.  Every machine below is a literal fn-ptx-mk state over
; one entry of three spans (b1's 10 octets, the article's 5, b3's suffix and
; trailer's 32), in the phase named; each is a state the machine's invariant
; admits or (where a tooth needs one) a named corruption of one.  They are
; constants of this book, not reached from the open by a run: see the P4-2
; comment below for what that costs.
(defun ptxt-kd () (fn-ptx-kd-mk 4 (make-list 32 :initial-element 7) 8192 5 4))
(defun ptxt-geo () (list 4096 16777216 4096))
(defun ptxt-hs () (list 47 (make-list 32 :initial-element 9) 4065))
(defun ptxt-cur () (list 1 1 2 5 0 4 5 0 0))
(defun ptxt-mach (ph k evd)
  (fn-ptx-mk ph k (ptxt-cur) nil (ptxt-kd) 1048576 1048576 '(0 1 10 0) '(1 1 41 9) (ptxt-hs) nil evd (ptxt-geo) nil))
(defconst *ptxt-done3* '((:pwrite :done 10) (:pwrite :done 5) (:pwrite :done 32)))
; waiting for the barrier: all three writes whole
(defconst *ptxt-mc* (ptxt-mach :committing 0 *ptxt-done3*))
; one completion short of the barrier's evidence: the invariant is false of it
(defconst *ptxt-mc-short* (ptxt-mach :committing 0 (take 2 *ptxt-done3*)))
; waiting for the first entry write
(defconst *ptxt-mp* (ptxt-mach :payload-writing 0 nil))
; waiting for the extension
(defconst *ptxt-mx* (fn-ptx-mk :extending 0 (ptxt-cur) nil (ptxt-kd) 1048576 1048576 '(0 1 10 0) '(1 1 41 9)
                               (ptxt-hs) nil nil (ptxt-geo) nil))
; the payload-writing phase past its last span: false of the invariant
(defconst *ptxt-mp-over* (ptxt-mach :payload-writing 5 nil))
; the open's idle machine with a chain field that is not 32 octets: well shaped, false of the invariant
(defconst *ptxt-mbad* (fn-ptx-opened (fn-ptx-kd-mk 4 '(1 2 3) 8192 5 4) 1048576 (ptxt-geo)))
(defconst *ptxt-bogus* (fn-ptx-mk :bogus 0 nil nil nil 0 0 nil nil nil nil nil nil nil))
; events: (kind (tag n) id inc)
(defconst *ptxt-fsync-ok* '(:fsync (:done 0) 1 1))
(defconst *ptxt-fsync-bad* '(:fsync (:failed :eio) 1 1))
(defconst *ptxt-pwrite-bad* '(:pwrite (:failed :eio) 1 1))
(defconst *ptxt-pwrite-ok* '(:pwrite (:done 5) 1 1))
(defconst *ptxt-pwrite-zero* '(:pwrite (:done 0) 1 1))
(defconst *ptxt-extend-bad* '(:extend (:failed :eio) 1 1))
(defconst *ptxt-timer* '(:timer (:done 0) 1 1))

(defconst *ptxt-c-keeps-ok* '(((ok (fn-ptx-okp m))) (fn-ptx-okp (mv-nth 0 (fn-ptx-step m ev st q)))))
(defconst *ptxt-c-p1* '(() (fn-ptx-p1 m ev st q)))
(defconst *ptxt-c-p2* '(() (fn-ptx-p2 m ev st q)))
(defconst *ptxt-c-p3* '(() (fn-ptx-p3 m ev st q)))
(defconst *ptxt-c-p5* '(() (fn-ptx-p5 m ev st q)))

; =============================================================================
; L's ground log (tests/acl2/post-transaction-durable-tests.lisp's fixture, renamed): two records
; recovered at the open, then one post.

(defun ptxt-unit () (declare (xargs :guard t)) 4)
(defun ptxt-max () (declare (xargs :guard t)) 4096)
(defun ptxt-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun ptxt-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))
(defun ptxt-big () (declare (xargs :guard t)) (make-list 700 :initial-element 5))
(defun ptxt-store (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (ptxt-unit) (list (cons 0 content)) nil pending 1))
; The segment a crash left: two records logged, a torn unit, zeros.
(defun ptxt-content ()
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (ptxt-r 1) (ptxt-r 2)) (ptxt-genesis) (ptxt-unit))
          '(9 9 9 9 0 0 0 0 0 0 0 0)
          (fn-bs-zeros 512)))
; The string the open read (fn-lgd-octets of it is the content).
(defun ptxt-chars (octets)
  (declare (xargs :guard t))
  (if (atom octets) nil
    (cons (code-char (if (and (natp (car octets)) (< (car octets) 256)) (car octets) 0))
          (ptxt-chars (cdr octets)))))
(defun ptxt-s () (declare (xargs :guard t :verify-guards nil)) (coerce (ptxt-chars (ptxt-content)) 'string))
(defun ptxt-ks0 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgt-recover (fn-lgd-octets (ptxt-s)) (ptxt-genesis) (ptxt-unit) (ptxt-max) 0))
; The store the open's copy leaves: the read's prefix, then zeros.
(defun ptxt-bs0 ()
  (declare (xargs :guard t :verify-guards nil))
  (let ((f (fn-lgk-frontier (ptxt-ks0))))
    (ptxt-store (append (fn-bs-take f (ptxt-content)) (fn-bs-zeros (- (len (ptxt-content)) f))) nil)))
(defun ptxt-st0 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-ptd-init (ptxt-ks0) (len (fn-bs-durable-content (ptxt-bs0) 0))))
(defun ptxt-run (ins)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ptd-run (ptxt-st0) ins 0 (ptxt-unit) (ptxt-max)))
(defun ptxt-recovered (image)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image 0) (ptxt-genesis) (ptxt-unit) (ptxt-max) 0)))

(defconst *ptxt-post-one* (list (list :begin '(11 12 7)) '(:pwrite . :ok) '(:fsync . :ok)))
(defconst-eval *ptxt-k-bs0* (ptxt-bs0))
(defconst-eval *ptxt-k-ks0* (ptxt-ks0))
(defconst-eval *ptxt-k-ops1*
  (mv-let (st a ans ops) (ptxt-run *ptxt-post-one*) (declare (ignore st a ans)) ops))
(defconst-eval *ptxt-k-run1* (fn-lgu-host-run *ptxt-k-bs0* *ptxt-k-ks0* *ptxt-k-ops1* 0 4096))

; =============================================================================
; The ground lemmas below bind the theorems' ST to (create-fn-rtc-st), the
; abstract stobj's creator value: the claim's variable ST is an ordinary
; variable, so a closed binding is a ground value of the stobj's logic.  A
; ground lemma proves the claim's conjunction SATISFIABLE at the binding, never
; reachable; the machine's guards are not verified (landing 2), so these
; lemmas, not an executed witness, are the positive witnesses.  The prover does
; not see this book's attachment of the acceptance (the constrained
; fn-ptx-acc-*), so each state below is one whose step never reaches the
; acceptance (no post waits in the queue, nothing is being read), and the one
; fact the shape check needs of its constrained bound, (<= 1 (fn-ptx-acc-max-state)),
; is cited as fn-ptx-acc-max-state-pos.  The claims' own rewrite rules are
; disabled in the witness lemmas so that each is proved by computing the step,
; not by citing the theorem it witnesses.

; Executed alongside (the attachment above makes the machine run; the stobj is
; fresh and local): the committing step posts, committed flips, the machine is idle.
(assert-event
 (let* ((r (ptxt-step *ptxt-mc* *ptxt-fsync-ok* 4096)) (m2 (nth 0 r)) (reqs (nth 1 r)))
   (and (fn-ptx-okp *ptxt-mc*) (not (fn-ptx-committedp *ptxt-mc*))
        (fn-ptx-committedp m2) (equal (fn-ptx-ph m2) :idle)
        (equal (fn-ptx-cur-code *ptxt-mc* reqs) 0)
        (fn-ptx-okp m2))))

; -----------------------------------------------------------------------------
; P0: fn-ptx-step-keeps-ok.
(teeth-ground-lemma ptxt-gl-keeps-ok-witness *ptxt-c-keeps-ok*
  ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-step-keeps-ok))))
(teeth-ground-lemma ptxt-gl-keeps-ok-without-ok *ptxt-c-keeps-ok*
  ((m *ptxt-mbad*) (ev *ptxt-timer*) (st (create-fn-rtc-st)) (q 4096))
  :without ok
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-step-keeps-ok))))
(teeth-ground-lemma ptxt-gl-keeps-ok-shape-only *ptxt-c-keeps-ok*
  ((m *ptxt-mbad*) (ev *ptxt-timer*) (st (create-fn-rtc-st)) (q 4096))
  :mutation (:hypothesis ok (fn-ptx-wfp m))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-step-keeps-ok))))
(defteeth fn-ptx-step-keeps-ok
  :claim (((ok (fn-ptx-okp m))) (fn-ptx-okp (mv-nth 0 (fn-ptx-step m ev st q))))
  :subject fn-ptx-step
  :witness ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
  :witness-lemma ptxt-gl-keeps-ok-witness
  :breaks ((ok ((m *ptxt-mbad*) (ev *ptxt-timer*)) :lemma ptxt-gl-keeps-ok-without-ok))
  :mutations ((invariant-weakened-to-the-shape
               (:hypothesis ok (fn-ptx-wfp m))
               ((m *ptxt-mbad*) (ev *ptxt-timer*))
               :fault "the invariant weakened to the shape check alone: an idle machine whose chain field is not 32 octets passes it and the step leaves it so"
               :lemma ptxt-gl-keeps-ok-shape-only)))

; -----------------------------------------------------------------------------
; P1: fn-ptx-commit-is-the-barrier-completion (predicate form: no hypothesis).
; The inner antecedent is TRUE at the witness (not committed, then committed),
; so the conclusion it demands (phase :committing, a barrier :done) is checked.
(defthm ptxt-p1-inner
  (let ((m2 (mv-nth 0 (fn-ptx-step *ptxt-mc* *ptxt-fsync-ok* (create-fn-rtc-st) 4096))))
    (and (fn-ptx-okp *ptxt-mc*)
         (not (fn-ptx-committedp *ptxt-mc*))
         (fn-ptx-committedp m2)
         (equal (fn-ptx-ph *ptxt-mc*) :committing)
         (fn-rtc-fsync-done-p *ptxt-fsync-ok*)))
  :rule-classes nil
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos))))
; A step that does not commit (the record write's completion): the inner
; antecedent is false there; the machine moves to the barrier uncommitted.
(defthm ptxt-p1-no-commit-at-the-record-write
  (let ((m2 (mv-nth 0 (fn-ptx-step (ptxt-mach :log-writing 2 (take 2 *ptxt-done3*)) '(:pwrite (:done 32) 1 1)
                                   (create-fn-rtc-st) 4096))))
    (and (equal (fn-ptx-ph m2) :committing) (not (fn-ptx-committedp m2))))
  :rule-classes nil
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos))))
(teeth-ground-lemma ptxt-gl-p1-witness *ptxt-c-p1*
  ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-commit-is-the-barrier-completion))))
(teeth-ground-lemma ptxt-gl-p1-mutant *ptxt-c-p1*
  ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
  :mutation (:conclusion
             (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
               (declare (ignore reqs c))
               (implies (and (not (fn-ptx-committedp m)) (fn-ptx-committedp m2))
                        (and (equal (fn-ptx-ph m) :log-writing) (eq (fn-rtc-get 0 ev) :pwrite)))))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-commit-is-the-barrier-completion))))
(defteeth fn-ptx-commit-is-the-barrier-completion
  :claim (() (fn-ptx-p1 m ev st q))
  :subject fn-ptx-step
  :witness ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
  :witness-lemma ptxt-gl-p1-witness
  :mutations ((commit-at-the-record-write
               (:conclusion
                (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
                  (declare (ignore reqs c))
                  (implies (and (not (fn-ptx-committedp m)) (fn-ptx-committedp m2))
                           (and (equal (fn-ptx-ph m) :log-writing) (eq (fn-rtc-get 0 ev) :pwrite)))))
               ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
               :fault "the commit placed at the record write's completion instead of the barrier's"
               :lemma ptxt-gl-p1-mutant)))

; -----------------------------------------------------------------------------
; P2: fn-ptx-posted-has-durable-commit-evidence (predicate form).
; Inner antecedent TRUE at the witness: the machine is ok, the step answers
; code 0, and the evidence is the three writes then the barrier.
(defthm ptxt-p2-inner
  (let* ((r (fn-ptx-step *ptxt-mc* *ptxt-fsync-ok* (create-fn-rtc-st) 4096)) (reqs (mv-nth 1 r)))
    (and (fn-ptx-okp *ptxt-mc*)
         (equal (fn-ptx-cur-code *ptxt-mc* reqs) 0)
         (fn-ptx-posted-evidence-p (append (fn-ptx-evd *ptxt-mc*) (list (fn-ptx-summary *ptxt-fsync-ok*))) *ptxt-mc*)))
  :rule-classes nil
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos))))
; The inner okp is necessary (a machine one completion short of the barrier is
; not ok, still answers code 0 at the barrier, and its evidence is not the
; entry's): the conclusion fails there.  Not a defteeth removal: the predicate
; form declares no hypothesis.
(defthm ptxt-p2-needs-okp
  (let* ((r (fn-ptx-step *ptxt-mc-short* *ptxt-fsync-ok* (create-fn-rtc-st) 4096)) (reqs (mv-nth 1 r)))
    (and (not (fn-ptx-okp *ptxt-mc-short*))
         (equal (fn-ptx-cur-code *ptxt-mc-short* reqs) 0)
         (not (fn-ptx-posted-evidence-p (append (fn-ptx-evd *ptxt-mc-short*) (list (fn-ptx-summary *ptxt-fsync-ok*)))
                                        *ptxt-mc-short*))))
  :rule-classes nil
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos))))
(teeth-ground-lemma ptxt-gl-p2-witness *ptxt-c-p2*
  ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-posted-has-durable-commit-evidence))))
(teeth-ground-lemma ptxt-gl-p2-mutant *ptxt-c-p2*
  ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
  :mutation (:conclusion
             (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
               (declare (ignore m2 c))
               (implies (and (fn-ptx-okp m) (equal (fn-ptx-cur-code m reqs) 0))
                        (fn-ptx-posted-evidence-p (fn-ptx-evd m) m))))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-posted-has-durable-commit-evidence))))
(defteeth fn-ptx-posted-has-durable-commit-evidence
  :claim (() (fn-ptx-p2 m ev st q))
  :subject fn-ptx-step
  :witness ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
  :witness-lemma ptxt-gl-p2-witness
  :mutations ((posted-without-the-barrier
               (:conclusion
                (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
                  (declare (ignore m2 c))
                  (implies (and (fn-ptx-okp m) (equal (fn-ptx-cur-code m reqs) 0))
                           (fn-ptx-posted-evidence-p (fn-ptx-evd m) m))))
               ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
               :fault ":posted accepted with the barrier's completion missing from the evidence"
               :lemma ptxt-gl-p2-mutant)))

; -----------------------------------------------------------------------------
; P3: fn-ptx-step-makes-progress (predicate form).
; Inner antecedent TRUE at the witness: ok, the phase waits for an fsync, an
; fsync arrives, and the measure falls (the queue is empty: one step, to zero).
(defthm ptxt-p3-inner
  (let ((m2 (mv-nth 0 (fn-ptx-step *ptxt-mc* *ptxt-fsync-ok* (create-fn-rtc-st) 4096))))
    (and (fn-ptx-okp *ptxt-mc*)
         (equal (fn-ptx-expected *ptxt-mc*) :fsync)
         (eq (fn-rtc-get 0 *ptxt-fsync-ok*) (fn-ptx-expected *ptxt-mc*))
         (< (fn-ptx-measure m2) (fn-ptx-measure *ptxt-mc*))))
  :rule-classes nil
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos))))
; The inner okp is necessary: a payload-writing machine past its last span is
; not ok, waits for a pwrite and gets one, and the step moves it to the
; log-writing phase, whose measure is larger.
(defthm ptxt-p3-needs-okp
  (let ((m2 (mv-nth 0 (fn-ptx-step *ptxt-mp-over* *ptxt-pwrite-zero* (create-fn-rtc-st) 4096))))
    (and (not (fn-ptx-okp *ptxt-mp-over*))
         (equal (fn-ptx-expected *ptxt-mp-over*) :pwrite)
         (eq (fn-rtc-get 0 *ptxt-pwrite-zero*) (fn-ptx-expected *ptxt-mp-over*))
         (not (< (fn-ptx-measure m2) (fn-ptx-measure *ptxt-mp-over*)))))
  :rule-classes nil
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos))))
(teeth-ground-lemma ptxt-gl-p3-witness *ptxt-c-p3*
  ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-step-makes-progress))))
(teeth-ground-lemma ptxt-gl-p3-mutant *ptxt-c-p3*
  ((m *ptxt-mc*) (ev *ptxt-pwrite-ok*) (st (create-fn-rtc-st)) (q 4096))
  :mutation (:conclusion
             (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
               (declare (ignore reqs c))
               (implies (and (fn-ptx-okp m) (fn-ptx-expected m))
                        (< (fn-ptx-measure m2) (fn-ptx-measure m)))))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-step-makes-progress))))
(defteeth fn-ptx-step-makes-progress
  :claim (() (fn-ptx-p3 m ev st q))
  :subject fn-ptx-step
  :witness ((m *ptxt-mc*) (ev *ptxt-fsync-ok*) (st (create-fn-rtc-st)) (q 4096))
  :witness-lemma ptxt-gl-p3-witness
  :mutations ((measure-falls-on-any-event
               (:conclusion
                (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
                  (declare (ignore reqs c))
                  (implies (and (fn-ptx-okp m) (fn-ptx-expected m))
                           (< (fn-ptx-measure m2) (fn-ptx-measure m)))))
               ((m *ptxt-mc*) (ev *ptxt-pwrite-ok*) (st (create-fn-rtc-st)) (q 4096))
               :fault "the measure claimed to fall on an unexpected completion: a write's completion while the machine waits for its barrier changes nothing"
               :lemma ptxt-gl-p3-mutant)))

; -----------------------------------------------------------------------------
; P5: fn-ptx-uncertain-only-after-the-first-entry-write (predicate form).
; First witness: the barrier fails, the step answers code 2 from :committing and
; the machine is :fenced.  Second witness (a lemma next to the teeth): the
; extension fails before any entry write, the step answers code 1 from :extending.
(assert-event
 (let* ((r (ptxt-step *ptxt-mc* *ptxt-fsync-bad* 4096)) (m2 (nth 0 r)) (reqs (nth 1 r)))
   (and (equal (fn-ptx-cur-code *ptxt-mc* reqs) 2) (equal (fn-ptx-ph m2) :fenced)))
 :msg "P5: the failed barrier answers code 2 and fences")
(assert-event
 (let* ((r (ptxt-step *ptxt-mx* *ptxt-extend-bad* 4096)) (m2 (nth 0 r)) (reqs (nth 1 r)))
   (and (equal (fn-ptx-cur-code *ptxt-mx* reqs) 1) (equal (fn-ptx-ph m2) :fenced)))
 :msg "P5: the failed extension answers code 1 and fences")
(defthm ptxt-p5-inner-uncertain
  (let* ((r (fn-ptx-step *ptxt-mc* *ptxt-fsync-bad* (create-fn-rtc-st) 4096))
         (m2 (mv-nth 0 r)) (reqs (mv-nth 1 r)))
    (and (equal (fn-ptx-cur-code *ptxt-mc* reqs) 2)
         (member-eq (fn-ptx-ph *ptxt-mc*) '(:payload-writing :log-writing :committing))
         (equal (fn-ptx-ph m2) :fenced)))
  :rule-classes nil
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos))))
(defthm ptxt-p5-inner-refused
  (let* ((r (fn-ptx-step *ptxt-mx* *ptxt-extend-bad* (create-fn-rtc-st) 4096))
         (reqs (mv-nth 1 r)))
    (and (equal (fn-ptx-cur-code *ptxt-mx* reqs) 1)
         (not (member-eq (fn-ptx-ph *ptxt-mx*) '(:payload-writing :log-writing :committing)))))
  :rule-classes nil
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos))))
(teeth-ground-lemma ptxt-gl-p5-witness *ptxt-c-p5*
  ((m *ptxt-mc*) (ev *ptxt-fsync-bad*) (st (create-fn-rtc-st)) (q 4096))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-uncertain-only-after-the-first-entry-write))))
(teeth-ground-lemma ptxt-gl-p5-witness-refused *ptxt-c-p5*
  ((m *ptxt-mx*) (ev *ptxt-extend-bad*) (st (create-fn-rtc-st)) (q 4096))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-uncertain-only-after-the-first-entry-write))))
; the uncertainty bound to the barrier alone: false where a failed first
; entry write answers code 2 from :payload-writing
(teeth-ground-lemma ptxt-gl-p5-mutant-barrier-only *ptxt-c-p5*
  ((m *ptxt-mp*) (ev *ptxt-pwrite-bad*) (st (create-fn-rtc-st)) (q 4096))
  :mutation (:conclusion
             (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
               (declare (ignore c))
               (let ((code (fn-ptx-cur-code m reqs)))
                 (and (implies (equal code 2) (and (equal (fn-ptx-ph m) :committing) (equal (fn-ptx-ph m2) :fenced)))
                      (implies (equal code 1) (not (member-eq (fn-ptx-ph m) '(:payload-writing :log-writing :committing))))))))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-uncertain-only-after-the-first-entry-write))))
; a hashing machine (the digest done, the extension target past 2^64) refuses
; with no log action: code 1 from :hashing, which is not past the first entry write
(defconst *ptxt-mh*
  (fn-ptx-mk :hashing 0 (ptxt-cur) nil (fn-ptx-kd-mk 4 (make-list 32 :initial-element 7) (expt 2 70) 5 4)
             1048576 1048576 '(0 1 10 0) '(1 1 9 9) (list 0 nil) nil nil (ptxt-geo) nil))
(teeth-ground-lemma ptxt-gl-p5-mutant-no-refusal-in-hashing *ptxt-c-p5*
  ((m *ptxt-mh*) (ev *ptxt-timer*) (st (create-fn-rtc-st)) (q 4096))
  :mutation (:conclusion
             (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
               (declare (ignore c))
               (let ((code (fn-ptx-cur-code m reqs)))
                 (and (implies (equal code 2) (and (member-eq (fn-ptx-ph m) '(:payload-writing :log-writing :committing))
                                                   (equal (fn-ptx-ph m2) :fenced)))
                      (implies (equal code 1) (not (member-eq (fn-ptx-ph m) '(:hashing :payload-writing :log-writing :committing))))))))
  :hints (("Goal" :use (fn-ptx-acc-max-state-pos) :in-theory (disable fn-ptx-uncertain-only-after-the-first-entry-write))))
(defteeth fn-ptx-uncertain-only-after-the-first-entry-write
  :claim (() (fn-ptx-p5 m ev st q))
  :subject fn-ptx-step
  :witness ((m *ptxt-mc*) (ev *ptxt-fsync-bad*) (st (create-fn-rtc-st)) (q 4096))
  :witness-lemma ptxt-gl-p5-witness
  :mutations ((uncertain-only-at-the-barrier
               (:conclusion
                (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
                  (declare (ignore c))
                  (let ((code (fn-ptx-cur-code m reqs)))
                    (and (implies (equal code 2) (and (equal (fn-ptx-ph m) :committing) (equal (fn-ptx-ph m2) :fenced)))
                         (implies (equal code 1) (not (member-eq (fn-ptx-ph m) '(:payload-writing :log-writing :committing))))))))
               ((m *ptxt-mp*) (ev *ptxt-pwrite-bad*) (st (create-fn-rtc-st)) (q 4096))
               :fault "uncertainty claimed only from the barrier on: a failed first entry write, the entry possibly on disk, answers code 2 from :payload-writing"
               :lemma ptxt-gl-p5-mutant-barrier-only)
              (no-refusal-in-hashing
               (:conclusion
                (mv-let (m2 reqs c) (fn-ptx-step m ev st q)
                  (declare (ignore c))
                  (let ((code (fn-ptx-cur-code m reqs)))
                    (and (implies (equal code 2) (and (member-eq (fn-ptx-ph m) '(:payload-writing :log-writing :committing))
                                                      (equal (fn-ptx-ph m2) :fenced)))
                         (implies (equal code 1) (not (member-eq (fn-ptx-ph m) '(:hashing :payload-writing :log-writing :committing))))))))
               ((m *ptxt-mh*) (ev *ptxt-timer*) (st (create-fn-rtc-st)) (q 4096))
               :fault "the phase list of the code-1 clause widened to :hashing: the refusal an over-large extension forces at the end of the digest is no entry write"
               :lemma ptxt-gl-p5-mutant-no-refusal-in-hashing)))

; -----------------------------------------------------------------------------
; fn-ptx-closed-is-ok: the machine before the open satisfies the invariant (no
; hypothesis, no variable).  The attachment above makes fn-ptx-okp run, so the
; witness is executed.  A hypothesis-free, variable-free claim has no removal;
; the mutation is a closed machine that still carries one entry completion in
; its ghost log: the :closed phase demands an empty log, so the invariant is
; false of it (a stale completion surviving the close is the fault the
; invariant exists to rule out).
(defteeth fn-ptx-closed-is-ok
  :claim (() (fn-ptx-okp (fn-ptx-closed)))
  :subject fn-ptx-step
  :witness ((none nil))
  :mutations ((closed-with-a-stale-completion
               (:conclusion
                (fn-ptx-okp (fn-ptx-mk :closed 0 nil nil nil 0 0 nil nil nil nil
                                       (list (list :pwrite (list :done 10) 1 1)) nil nil)))
               ()
               :fault "the closed machine built with an entry completion still in its ghost log, as if a close had not cleared the finished transaction: the :closed phase demands no completions, so the invariant is false of it")))

; =============================================================================
; The ledger's checks of a copied claim: the statement below is read back from
; the world and compared with the copy.
(defmacro ptxt-claim-is-the-theorem (const name)
  `(make-event
    (mv-let (bad term) (fn-dt-translate (fn-dk-statement ,const) (w state))
      (if (and (not bad) (equal term (getpropc ',name 'theorem nil (w state))))
          (value '(value-triple :claim-is-the-theorem))
        (er soft 'ptxt-claim-is-the-theorem "~x0: the copied claim is not the stored theorem" ',name)))))

; =============================================================================
; P6: fn-ptx-split-crash-images-are-entry-crash-images, on L's ground log: the
; cut of one post where the 80-octet entry write is pending (the frontier 88),
; split into two writes of 40 octets and the first alone pending.
(defconst-eval *ptxt-k-g* (ptxt-genesis))
(defconst-eval *ptxt-p6-pair* (nth 3 *ptxt-k-run1*))
(defconst-eval *ptxt-p6-bs* (car *ptxt-p6-pair*))
(defconst-eval *ptxt-p6-ks* (cdr *ptxt-p6-pair*))
(defconst-eval *ptxt-p6-e* (fn-lg-log (fn-lgk-inflight *ptxt-p6-ks*) (fn-lgk-last *ptxt-p6-ks*) (fn-bs-unit *ptxt-p6-bs*)))
(defconst *ptxt-p6-ls* '(40 40))
(defconst-eval *ptxt-p6-ops* (fn-ptx-split-ops 0 (fn-lgk-frontier *ptxt-p6-ks*) *ptxt-p6-e* *ptxt-p6-ls*))
(defconst *ptxt-p6-new10* (make-list 10 :initial-element :new))
(defconst-eval *ptxt-p6-split1* (fn-ptx-with-pending *ptxt-p6-bs* (take 1 *ptxt-p6-ops*)))
; the first 40 octets of the entry landed
(defconst-eval *ptxt-p6-img* (fn-bs-crash *ptxt-p6-split1* (list *ptxt-p6-new10*)))
(assert-event (and (fn-lgk-relp *ptxt-p6-bs* *ptxt-p6-ks* 0 *ptxt-k-g* 4096)
                   (consp (fn-lgk-inflight *ptxt-p6-ks*))
                   (equal (len *ptxt-p6-e*) 80) (equal (fn-lgk-frontier *ptxt-p6-ks*) 88)
                   (equal (fn-bs-pending *ptxt-p6-bs*) (list (list :write 0 88 *ptxt-p6-e*)))
                   (fn-bs-crash-choicesp (list *ptxt-p6-new10*) (fn-bs-pending *ptxt-p6-split1*) 4)
                   (equal *ptxt-p6-img* (fn-bs-crash *ptxt-p6-bs* (list (append *ptxt-p6-new10* (make-list 10 :initial-element :old)))))
                   (not (equal *ptxt-p6-img* (fn-ptx-with-pending *ptxt-p6-bs* nil)))))

(defconst *ptxt-c-p6*
  '(((rel (fn-lgk-relp bs ks ino genesis max))
     (e (equal e (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
     (sum (<= (fn-ptx-sum ls) (len e)))
     (img (fn-bs-crash-imagep (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                              image)))
    (fn-bs-crash-imagep bs image)))
(ptxt-claim-is-the-theorem *ptxt-c-p6* fn-ptx-split-crash-images-are-entry-crash-images)

; the positive witness: the first piece's image is an image of the unsplit store
(teeth-ground-lemma ptxt-gl-p6-witness *ptxt-c-p6*
  ((bs *ptxt-p6-bs*) (ks *ptxt-p6-ks*) (ino 0) (genesis *ptxt-k-g*) (max 4096) (e *ptxt-p6-e*)
   (ls *ptxt-p6-ls*) (j 1) (image *ptxt-p6-img*))
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-bs-crash-imagep-suff (s *ptxt-p6-split1*) (image *ptxt-p6-img*) (choices (list *ptxt-p6-new10*)))
                 (:instance fn-bs-crash-imagep-suff (s *ptxt-p6-bs*) (image *ptxt-p6-img*)
                            (choices (list (append *ptxt-p6-new10* (make-list 10 :initial-element :old)))))))))
; without REL: the store with nothing pending (the write already issued and
; lost from the model): the first piece's image has octets no image of it has
(defconst-eval *ptxt-p6-bs-np* (fn-ptx-with-pending *ptxt-p6-bs* nil))
(defconst-eval *ptxt-p6-split1-np* (fn-ptx-with-pending *ptxt-p6-bs-np* (take 1 *ptxt-p6-ops*)))
(defconst-eval *ptxt-p6-img-np* (fn-bs-crash *ptxt-p6-split1-np* (list *ptxt-p6-new10*)))
(assert-event (and (not (fn-lgk-relp *ptxt-p6-bs-np* *ptxt-p6-ks* 0 *ptxt-k-g* 4096))
                   (not (equal *ptxt-p6-img-np* *ptxt-p6-bs-np*))))
(teeth-ground-lemma ptxt-gl-p6-without-rel *ptxt-c-p6*
  ((bs *ptxt-p6-bs-np*) (ks *ptxt-p6-ks*) (ino 0) (genesis *ptxt-k-g*) (max 4096) (e *ptxt-p6-e*)
   (ls *ptxt-p6-ls*) (j 1) (image *ptxt-p6-img-np*))
  :without rel
  :hints (("Goal" :in-theory (union-theories (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
                                             '(fn-bs-crash fn-bs-crash-select fn-bs-pending fn-bs-make))
           :use ((:instance fn-bs-crash-imagep-suff (s *ptxt-p6-split1-np*) (image *ptxt-p6-img-np*) (choices (list *ptxt-p6-new10*)))
                 (:instance fn-ptx-imagep-unpack (s *ptxt-p6-bs-np*) (image *ptxt-p6-img-np*))))))

; THE P6 TEETH.  The statement has four hypotheses (rel, e, sum, img).  It once
; had eight; the other four (the entry's tail zeros, j a natural, j at most
; (len ls), a record in flight) had no breaking value, and the book now
; discharges each by a case: a j past the end takes NIL operations, which
; fn-bs-apply-op and fn-bs-crash ignore (checked, executed, at the end of this
; section); a j that is no natural takes nothing; with no record in flight the
; entry is NIL and every piece writes no octets; and the entry's tail past the
; pieces is covered by one more piece.  What is left has teeth.  A piece that
; lands inside the entry's footprint is an octet the unsplit store's :garble
; selector can reproduce, so the images the unsplit store does NOT have are
; those with an octet OUTSIDE its write (fn-ptx-p6-image-keeps-the-tail: the
; durable content from the end of the entry on is untouched by every image of a
; related store) and those with operations still pending
; (fn-ptx-p6-pending-is-no-image).  Each removal below is one of those:
;   rel  a store with its write already lost from the model (above),
;   e    an entry one octet longer than the logged one: the second piece lands an
;        octet past the footprint,
;   sum  more piece octets than the entry has: take pads NIL, and the NIL octet
;        lands past the footprint,
;   img  an image with no write pending whose committed log has one octet changed:
;        a crash image keeps the durable content before the pending write.
(defconst-eval *ptxt-p6-e2* (append *ptxt-p6-e* (list 7)))
(defconst *ptxt-p6-ls2* '(40 41))
(defconst *ptxt-p6-new11* (make-list 11 :initial-element :new))
(defconst-eval *ptxt-p6-split2*
  (fn-ptx-with-pending *ptxt-p6-bs* (take 2 (fn-ptx-split-ops 0 (fn-lgk-frontier *ptxt-p6-ks*) *ptxt-p6-e2* *ptxt-p6-ls2*))))
(defconst-eval *ptxt-p6-img2* (fn-bs-crash *ptxt-p6-split2* (list *ptxt-p6-new10* *ptxt-p6-new11*)))
(defconst-eval *ptxt-p6-split3*
  (fn-ptx-with-pending *ptxt-p6-bs* (take 2 (fn-ptx-split-ops 0 (fn-lgk-frontier *ptxt-p6-ks*) *ptxt-p6-e* *ptxt-p6-ls2*))))
(defconst-eval *ptxt-p6-img3* (fn-bs-crash *ptxt-p6-split3* (list *ptxt-p6-new10* *ptxt-p6-new11*)))
(assert-event
 (let ((end (+ (fn-lgk-frontier *ptxt-p6-ks*) (len *ptxt-p6-e*))))
   (and (equal end 168)
        (not (equal *ptxt-p6-e2* *ptxt-p6-e*))
        (<= (fn-ptx-sum *ptxt-p6-ls2*) (len *ptxt-p6-e2*))
        (< (len *ptxt-p6-e*) (fn-ptx-sum *ptxt-p6-ls2*))
        (fn-bs-crash-choicesp (list *ptxt-p6-new10* *ptxt-p6-new11*) (fn-bs-pending *ptxt-p6-split2*) 4)
        (fn-bs-crash-choicesp (list *ptxt-p6-new10* *ptxt-p6-new11*) (fn-bs-pending *ptxt-p6-split3*) 4)
        (equal (nth end (fn-bs-durable-content *ptxt-p6-img2* 0)) 7)
        (equal (nth end (fn-bs-durable-content *ptxt-p6-img3* 0)) nil)
        (not (equal (nthcdr end (fn-bs-durable-content *ptxt-p6-img2* 0))
                    (nthcdr end (fn-bs-durable-content *ptxt-p6-bs* 0))))
        (not (equal (nthcdr end (fn-bs-durable-content *ptxt-p6-img3* 0))
                    (nthcdr end (fn-bs-durable-content *ptxt-p6-bs* 0)))))))
; no image of the related store has either of those octets past the entry
(defthm ptxt-p6-img2-no-image
  (not (fn-bs-crash-imagep *ptxt-p6-bs* *ptxt-p6-img2*))
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-ptx-p6-image-keeps-the-tail (bs *ptxt-p6-bs*) (ks *ptxt-p6-ks*) (ino 0)
                            (genesis *ptxt-k-g*) (max 4096) (e *ptxt-p6-e*) (image *ptxt-p6-img2*))))))
(defthm ptxt-p6-img3-no-image
  (not (fn-bs-crash-imagep *ptxt-p6-bs* *ptxt-p6-img3*))
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-ptx-p6-image-keeps-the-tail (bs *ptxt-p6-bs*) (ks *ptxt-p6-ks*) (ino 0)
                            (genesis *ptxt-k-g*) (max 4096) (e *ptxt-p6-e*) (image *ptxt-p6-img3*))))))
(teeth-ground-lemma ptxt-gl-p6-without-e *ptxt-c-p6*
  ((bs *ptxt-p6-bs*) (ks *ptxt-p6-ks*) (ino 0) (genesis *ptxt-k-g*) (max 4096) (e *ptxt-p6-e2*)
   (ls *ptxt-p6-ls2*) (j 2) (image *ptxt-p6-img2*))
  :without e
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-bs-crash-imagep-suff (s *ptxt-p6-split2*) (image *ptxt-p6-img2*)
                            (choices (list *ptxt-p6-new10* *ptxt-p6-new11*)))
                 (:instance ptxt-p6-img2-no-image)))))
(teeth-ground-lemma ptxt-gl-p6-without-sum *ptxt-c-p6*
  ((bs *ptxt-p6-bs*) (ks *ptxt-p6-ks*) (ino 0) (genesis *ptxt-k-g*) (max 4096) (e *ptxt-p6-e*)
   (ls *ptxt-p6-ls2*) (j 2) (image *ptxt-p6-img3*))
  :without sum
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-bs-crash-imagep-suff (s *ptxt-p6-split3*) (image *ptxt-p6-img3*)
                            (choices (list *ptxt-p6-new10* *ptxt-p6-new11*)))
                 (:instance ptxt-p6-img3-no-image)))))
; without IMG: an image the unsplit store does not have, with the entry's
; write NOT pending (every crash image has none) and octet-valued: the witness
; image with one durable octet changed OUTSIDE the entry's footprint, the first
; octet of the committed log (before the frontier 88).  A crash image of a
; related store keeps the durable content before the pending write
; (fn-ptx-p6-image-keeps-the-prefix), so it is no image of the unsplit store,
; and by the keystone itself no image of the split store either.
(defconst-eval *ptxt-p6-b0* (nth 0 (fn-bs-durable-content *ptxt-p6-img* 0)))
(defconst-eval *ptxt-p6-b0-new* (mod (+ 1 *ptxt-p6-b0*) 256))
(defconst-eval *ptxt-p6-img-pre*
  (fn-bs-make (fn-bs-unit *ptxt-p6-img*)
              (fn-bs-put-assoc 0 (fn-bs-splice (fn-bs-durable-content *ptxt-p6-img* 0) 0 (list *ptxt-p6-b0-new*))
                               (fn-bs-inodes *ptxt-p6-img*))
              (fn-bs-dirs *ptxt-p6-img*) nil (fn-bs-next-ino *ptxt-p6-img*)))
(assert-event
 (and (null (fn-bs-pending *ptxt-p6-img-pre*))
      (natp *ptxt-p6-b0*) (< *ptxt-p6-b0* 256)
      (natp *ptxt-p6-b0-new*) (< *ptxt-p6-b0-new* 256)
      (not (equal *ptxt-p6-b0* *ptxt-p6-b0-new*))
      (< 0 (fn-lgk-frontier *ptxt-p6-ks*))
      (true-listp (fn-bs-durable-content *ptxt-p6-img-pre* 0))
      (equal (len (fn-bs-durable-content *ptxt-p6-img-pre* 0)) (len (fn-bs-durable-content *ptxt-p6-img* 0)))
      ; it differs from the witness image in that one octet and no other
      (equal (cdr (fn-bs-durable-content *ptxt-p6-img-pre* 0)) (cdr (fn-bs-durable-content *ptxt-p6-img* 0)))
      (equal (fn-bs-make (fn-bs-unit *ptxt-p6-img-pre*)
                         (fn-bs-put-assoc 0 (fn-bs-splice (fn-bs-durable-content *ptxt-p6-img-pre* 0) 0 (list *ptxt-p6-b0*))
                                          (fn-bs-inodes *ptxt-p6-img-pre*))
                         (fn-bs-dirs *ptxt-p6-img-pre*) nil (fn-bs-next-ino *ptxt-p6-img-pre*))
             *ptxt-p6-img*)
      (not (equal *ptxt-p6-img-pre* *ptxt-p6-img*))))
(defthm ptxt-p6-img-pre-no-image
  (not (fn-bs-crash-imagep *ptxt-p6-bs* *ptxt-p6-img-pre*))
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-ptx-p6-image-keeps-the-prefix (bs *ptxt-p6-bs*) (ks *ptxt-p6-ks*) (ino 0)
                            (genesis *ptxt-k-g*) (max 4096) (e *ptxt-p6-e*) (image *ptxt-p6-img-pre*))))))
(teeth-ground-lemma ptxt-gl-p6-without-img *ptxt-c-p6*
  ((bs *ptxt-p6-bs*) (ks *ptxt-p6-ks*) (ino 0) (genesis *ptxt-k-g*) (max 4096) (e *ptxt-p6-e*)
   (ls *ptxt-p6-ls*) (j 1) (image *ptxt-p6-img-pre*))
  :without img
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-ptx-split-crash-images-are-entry-crash-images
                            (bs *ptxt-p6-bs*) (ks *ptxt-p6-ks*) (ino 0) (genesis *ptxt-k-g*) (max 4096)
                            (e *ptxt-p6-e*) (ls *ptxt-p6-ls*) (j 1) (image *ptxt-p6-img-pre*))
                 (:instance ptxt-p6-img-pre-no-image)))))
; the mutation: the conclusion's store with the whole entry already durable, so
; that nothing is pending and its one image is itself
(defconst-eval *ptxt-p6-bs-whole*
  (fn-bs-make (fn-bs-unit *ptxt-p6-bs*)
              (fn-bs-put-assoc 0 (fn-bs-splice (fn-bs-durable-content *ptxt-p6-bs* 0) (fn-lgk-frontier *ptxt-p6-ks*) *ptxt-p6-e*)
                               (fn-bs-inodes *ptxt-p6-bs*))
              (fn-bs-dirs *ptxt-p6-bs*) nil (fn-bs-next-ino *ptxt-p6-bs*)))
(assert-event (and (null (fn-bs-pending *ptxt-p6-bs-whole*)) (not (equal *ptxt-p6-img* *ptxt-p6-bs-whole*))))
(defthm ptxt-p6-whole-has-no-img
  (not (fn-bs-crash-imagep *ptxt-p6-bs-whole* *ptxt-p6-img*))
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-ptx-p6-idle-image (s *ptxt-p6-bs-whole*) (image *ptxt-p6-img*))))))
(teeth-ground-lemma ptxt-gl-p6-mutant-whole-entry-durable *ptxt-c-p6*
  ((bs *ptxt-p6-bs*) (ks *ptxt-p6-ks*) (ino 0) (genesis *ptxt-k-g*) (max 4096) (e *ptxt-p6-e*)
   (ls *ptxt-p6-ls*) (j 1) (image *ptxt-p6-img*))
  :mutation (:conclusion
             (fn-bs-crash-imagep (fn-bs-make (fn-bs-unit bs)
                                             (fn-bs-put-assoc ino (fn-bs-splice (fn-bs-durable-content bs ino) (fn-lgk-frontier ks) e)
                                                              (fn-bs-inodes bs))
                                             (fn-bs-dirs bs) nil (fn-bs-next-ino bs))
                                 image))
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-bs-crash-imagep-suff (s *ptxt-p6-split1*) (image *ptxt-p6-img*) (choices (list *ptxt-p6-new10*)))
                 (:instance fn-bs-crash-imagep-suff (s *ptxt-p6-bs*) (image *ptxt-p6-img*)
                            (choices (list (append *ptxt-p6-new10* (make-list 10 :initial-element :old)))))
                 (:instance ptxt-p6-whole-has-no-img)))))
(defteeth fn-ptx-split-crash-images-are-entry-crash-images
  :claim (((rel (fn-lgk-relp bs ks ino genesis max))
           (e (equal e (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
           (sum (<= (fn-ptx-sum ls) (len e)))
           (img (fn-bs-crash-imagep (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                                    image)))
          (fn-bs-crash-imagep bs image))
  :subject fn-ptx-split-ops
  :witness ((bs *ptxt-p6-bs*) (ks *ptxt-p6-ks*) (ino 0) (genesis *ptxt-k-g*) (max 4096) (e *ptxt-p6-e*)
            (ls *ptxt-p6-ls*) (j 1) (image *ptxt-p6-img*))
  :witness-lemma ptxt-gl-p6-witness
  :breaks ((rel ((bs *ptxt-p6-bs-np*) (image *ptxt-p6-img-np*)) :lemma ptxt-gl-p6-without-rel)
           (e ((e *ptxt-p6-e2*) (ls *ptxt-p6-ls2*) (j 2) (image *ptxt-p6-img2*)) :lemma ptxt-gl-p6-without-e)
           (sum ((ls *ptxt-p6-ls2*) (j 2) (image *ptxt-p6-img3*)) :lemma ptxt-gl-p6-without-sum)
           (img ((image *ptxt-p6-img-pre*)) :lemma ptxt-gl-p6-without-img))
  :mutations ((whole-entry-already-durable
               (:conclusion
                (fn-bs-crash-imagep (fn-bs-make (fn-bs-unit bs)
                                                (fn-bs-put-assoc ino (fn-bs-splice (fn-bs-durable-content bs ino) (fn-lgk-frontier ks) e)
                                                                 (fn-bs-inodes bs))
                                                (fn-bs-dirs bs) nil (fn-bs-next-ino bs))
                                    image))
               ()
               :fault "the conclusion's store with the whole entry already durable and nothing pending: its one image is itself, so a prefix of the entry's pieces landed is no image of it"
               :lemma ptxt-gl-p6-mutant-whole-entry-durable)))
; the NIL-operation fact behind the dropped j <= (len ls): take past the end pads
; NIL operations and crash images ignore them (executed)
(defconst-eval *ptxt-p6-ops-pad* (take 3 *ptxt-p6-ops*))
(assert-event (and (equal (len *ptxt-p6-ops-pad*) 3) (null (nth 2 *ptxt-p6-ops-pad*))
                   (equal (fn-bs-crash (fn-ptx-with-pending *ptxt-p6-bs* *ptxt-p6-ops-pad*) (list nil nil :apply))
                          (fn-bs-crash (fn-ptx-with-pending *ptxt-p6-bs* (take 2 *ptxt-p6-ops*)) (list nil nil)))))

; =============================================================================
; P4-2 (fn-ptx-posted-are-the-driver-posted) and the composition
; (fn-ptx-posted-records-are-recovered-at-every-later-cut): NOT covered here.
; This section constructs no trace.  Any future producer must supply
; (EV ST Q FO POST-ST), with POST-ST after the delivery AND its requests.
; The machine reads a post through fn-ptx-acc-begin / -feed / -end, a CONSTRAINED
; signature with no body.  The prover never uses an attachment, and the
; constraints admit an acceptance that refuses every post, so "this trace of the
; machine posts a record" is false in that model and no ground theorem states
; it: a positive witness with a posted record, and every hypothesis removal and
; conclusion mutation (each needs the machine's posted list to differ from the
; driver's), cannot be a lemma.  The executed route is closed too: both claims
; quantify over defun-nx functions (fn-ptx-trace-run, fn-ptx-trace-relies-p),
; which no evaluator runs.  A ground lemma over the acceptance-free fragment (the
; opened machine, one post handed in) was tried and sent the rewriter into a loop
; in the unfolding of fn-ptx-trace-run before any claim could be checked; it is
; not in this book.  The fix is the books', not this file's: an executable twin
; of the trace run, or an acceptance with a body.

; Draft-4 amendment 2: evaluated through the real step under this book's
; checked K=0 acceptance attachment. The theorem is about those captured outputs.
(with-guard-checking-event :none
 (encapsulate ()
 (defconst *ptxt-mhalf-charge-m*
  (fn-ptx-mk :reading 0 '(2 1 3 0 0 1 0 0 0) nil
   (fn-ptx-kd-mk 0 (make-list 32 :initial-element 0) 0 1 0)
   0 0 nil nil nil nil nil '(1 256 256) nil))
 (defconst *ptxt-mhalf-charge-e* '(:timer (:done 0) 1 1))
 (defun ptxt-mhalf-charge-execute (fn-rtc-st)
  (declare (xargs :guard t :stobjs fn-rtc-st))
  (mv-let (m2 rs cost)
    (fn-ptx-step1 *ptxt-mhalf-charge-m* *ptxt-mhalf-charge-e* fn-rtc-st 0)
   (declare (ignore m2))
   (mv fn-rtc-st
    (list (natp 0) (fn-rtc-size (fn-ptx-q *ptxt-mhalf-charge-m*))
     (fn-rtc-size (fn-ptx-kd *ptxt-mhalf-charge-m*))
     (fn-ptx-wfp *ptxt-mhalf-charge-m*) cost (fn-rtc-reqs-octets rs)
     (+ 0 9216 (* 10 (fn-ptx-acc-out-max)))
     (+ 0 9216 (* 10 (fn-ptx-acc-out-max)) (* 2 *fn-pctx-max*))))))
 (defun ptxt-mhalf-charge-local ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-rtc-st
   (mv-let (fn-rtc-st out) (ptxt-mhalf-charge-execute fn-rtc-st) out)))
 (make-event
  (value `(defconst *ptxt-mhalf-charge-observed* ',(ptxt-mhalf-charge-local))))
 (defthm ptxt-mhalf-old-charge-bound-is-refuted-and-new-bound-holds
  (let ((x *ptxt-mhalf-charge-observed*))
   (and (nth 0 x) (<= (nth 1 x) 21) (<= (nth 2 x) 75) (nth 3 x)
        (equal (+ (nth 4 x) (nth 5 x)) 20848)
        (equal (nth 6 x) 9216) (equal (nth 7 x) 29934)
        (< (nth 6 x) (+ (nth 4 x) (nth 5 x)))
        (<= (+ (nth 4 x) (nth 5 x)) (nth 7 x))))
  :rule-classes nil)))

; The old reader is a source copy from 0d6d79e83, with only its name and
; proof-side guard verification policy changed. It scans ENC as article bytes.
(with-guard-checking-event :none
 (encapsulate ()
 (defattach (fn-ptx-acc-begin fn-pacc-begin)
  (fn-ptx-acc-feed fn-pacc-feed) (fn-ptx-acc-feed-cost fn-pacc-feed-cost)
  (fn-ptx-acc-end fn-pacc-end) (fn-ptx-acc-max-state fn-pacc-max-state)
  (fn-ptx-acc-out-max fn-pacc-out-max)
  :hints (("Goal" :use
   (fn-pacc-meets-fn-ptx-acc-max-state-natp fn-pacc-meets-fn-ptx-acc-out-max-natp
    fn-pacc-meets-fn-ptx-acc-begin-bounded fn-pacc-meets-fn-ptx-acc-feed-bounded
    fn-pacc-meets-fn-ptx-acc-feed-cost-bounded fn-pacc-meets-fn-ptx-acc-feed-shape
    fn-pacc-meets-fn-ptx-acc-end-shape))))
(defun ptxt-v2-old-read (m q id inc fn-rtc-st)
  (declare (xargs :guard t :verify-guards nil :stobjs fn-rtc-st))
  (mbe :logic (let* ((cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
         (bp (fn-ptx-cur-bp cur)) (len (fn-ptx-cur-len cur)) (pos (fn-ptx-cur-hoff cur))
         (lim (min len (fn-ptx-hmax m)))
         (w (fn-ptx-read-w q))
         (m0 (fn-ptx-chg m :committed nil))
         (fresh (not (consp (fn-ptx-b1 m))))
         (h1 (if fresh (fn-ptx-free 0 nil id inc fn-rtc-st) (fn-ptx-buf-h (fn-ptx-b1 m))))
         (h3 (if fresh (fn-ptx-free 0 h1 id inc fn-rtc-st) (fn-ptx-buf-h (fn-ptx-b3 m))))
         (g1 (if fresh (+ 1 (fn-ptx-gen h1 id inc fn-rtc-st)) (fn-ptx-buf-g (fn-ptx-b1 m))))
         (g3 (if fresh (+ 1 (fn-ptx-gen h3 id inc fn-rtc-st)) (fn-ptx-buf-g (fn-ptx-b3 m))))
         (off (if fresh *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m))))
         ;; acquired, b3 is zeroed below its base (a write may not start past a buffer's
         ;; fill), so the suffix's head can be written just below the base at the end
         (acq (if fresh (list (list :acquire h1) (list :acquire h3)
                              (list :write h3 g3 0 (fn-bs-zeros *fn-ptx-sufhead-max*)))
                nil))
         (e (fn-ptx-head-end bp pos (min lim (+ pos w 3)) id inc fn-rtc-st))
         (cost0 (+ w 3 (* 3 (fn-ptx-acc-out-max)) 64)))
    (if (not (and h1 h3))
        ;; no workspaces: refused before any log action
        (mv-let (m2 r2 c2) (fn-ptx-end m0 :refused kd ext nil nil id inc fn-rtc-st)
          (mv m2 r2 (+ cost0 c2)))
      (let* ((m1 (fn-ptx-chg m0 :b1 (list h1 g1 0 0) :b3 (list h3 g3 off *fn-ptx-sufhead-max*)))
             ;; a refusal in this step: the end over the state without workspaces, which
             ;; are released here at the generation they were acquired or held at (no
             ;; lease has ended on them while reading)
             (mr (fn-ptx-chg m0 :b1 nil :b3 nil))
             (rel (list (list :release h1 g1) (list :release h3 g3)))
             (nfeed (if e (- e pos) (if (< (+ pos w 3) lim) w 0))))
        (mv-let (a sp) (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range bp pos nfeed id inc fn-rtc-st))
          (let ((off2 (+ off (len sp)))
                (cost (+ cost0 (nfix (fn-ptx-acc-feed-cost (fn-ptx-acc m) (fn-ptx-range bp pos nfeed id inc fn-rtc-st))))))
            (cond
             ((not (<= (+ off2 32) (fn-ptx-cap h3 id inc fn-rtc-st)))
              ;; the suffix outgrows its workspace: refused before any log action
              (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                (mv m2 (append acq rel r2) (+ cost c2))))
             (e
              (mv-let (ok pre ins ioff sh st) (fn-ptx-acc-end a (- len e))
                (let* ((ioff (if (consp ins) (nfix ioff) len))
                       (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))
                       (end (+ off2 (len st)))
                       (rlen (+ (len pre) len (len ins) (- end start)))
                       (b1 (append (fn-ptx-frame-header rlen) (fn-ptx-kd-last kd) pre)))
                  (if (not (and ok (<= ioff len) (<= (+ 32 rlen) (fn-ptx-fmax m))
                                (<= (+ (len b1) (len ins)) (fn-ptx-cap h1 id inc fn-rtc-st))
                                (<= (+ end 32) (fn-ptx-cap h3 id inc fn-rtc-st))))
                      (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                        (mv m2 (append acq rel r2) (+ cost c2)))
                    (mv (fn-ptx-chg m1 :ph :hashing :k 0
                                    :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len e (fn-ptx-cur-txid cur) ioff)
                                    :b1 (list h1 g1 (len b1) (len ins)) :b3 (list h3 g3 end start) :hs (list 0 nil) :acc nil)
                        (append acq (list (list :write h1 g1 0 (append b1 ins)))
                                (fn-ptx-write-nz h3 g3 start (take (- *fn-ptx-sufhead-max* start) sh))
                                (fn-ptx-write-nz h3 g3 off sp) (fn-ptx-write-nz h3 g3 off2 st)
                                (list (fn-ptx-timer)))
                        cost)))))
             ((< (+ pos w 3) lim)
              ;; no head end yet: the window fed, its suffix part written, continue
              (mv (fn-ptx-chg m1 :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len (+ pos w) (fn-ptx-cur-txid cur) len)
                              :b3 (list h3 g3 off2 *fn-ptx-sufhead-max*) :acc a)
                  (append acq (fn-ptx-write-nz h3 g3 off sp) (list (fn-ptx-timer)))
                  cost))
             (t
              ;; no head within the head limit: refused before any log action
              (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                (mv m2 (append acq rel r2) (+ cost c2))))))))))
       :exec (let* ((cur (fn-ptx-cur m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m))
         (bp (fn-ptx-cur-bp cur)) (len (fn-ptx-cur-len cur)) (pos (fn-ptx-cur-hoff cur))
         (lim (min len (fn-ptx-hmax m)))
         (w (fn-ptx-read-w q))
         (m0 (fn-ptx-chg m :committed nil))
         (fresh (not (consp (fn-ptx-b1 m))))
         (h1 (if fresh (fn-ptx-free 0 nil id inc fn-rtc-st) (fn-ptx-buf-h (fn-ptx-b1 m))))
         (h3 (if fresh (fn-ptx-free 0 h1 id inc fn-rtc-st) (fn-ptx-buf-h (fn-ptx-b3 m))))
         (g1 (if fresh (+ 1 (fn-ptx-gen h1 id inc fn-rtc-st)) (fn-ptx-buf-g (fn-ptx-b1 m))))
         (g3 (if fresh (+ 1 (fn-ptx-gen h3 id inc fn-rtc-st)) (fn-ptx-buf-g (fn-ptx-b3 m))))
         (off (if fresh *fn-ptx-sufhead-max* (fn-ptx-buf-len (fn-ptx-b3 m))))
         ;; acquired, b3 is zeroed below its base (a write may not start past a buffer's
         ;; fill), so the suffix's head can be written just below the base at the end
         (acq (if fresh (list (list :acquire h1) (list :acquire h3)
                              (list :write h3 g3 0 (fn-bs-zeros *fn-ptx-sufhead-max*)))
                nil))
         (e (fn-ptx-head-end bp pos (min lim (+ pos w 3)) id inc fn-rtc-st))
         (cost0 (+ w 3 (* 3 (fn-ptx-acc-out-max)) 64)))
    (if (not (and h1 h3))
        ;; no workspaces: refused before any log action
        (mv-let (m2 r2 c2) (fn-ptx-end m0 :refused kd ext nil nil id inc fn-rtc-st)
          (mv m2 r2 (+ cost0 c2)))
      (let* ((m1 (fn-ptx-chg m0 :b1 (list h1 g1 0 0) :b3 (list h3 g3 off *fn-ptx-sufhead-max*)))
             ;; a refusal in this step: the end over the state without workspaces, which
             ;; are released here at the generation they were acquired or held at (no
             ;; lease has ended on them while reading)
             (mr (fn-ptx-chg m0 :b1 nil :b3 nil))
             (rel (list (list :release h1 g1) (list :release h3 g3)))
             (nfeed (if e (- e pos) (if (< (+ pos w 3) lim) w 0))))
        (mv-let (a sp) (fn-ptx-acc-feed (fn-ptx-acc m) (fn-ptx-range bp pos nfeed id inc fn-rtc-st))
          (let ((off2 (+ off (len sp)))
                (cost (+ cost0 (nfix (fn-ptx-acc-feed-cost (fn-ptx-acc m) (fn-ptx-range bp pos nfeed id inc fn-rtc-st))))))
            (cond
             ((not (<= (+ off2 32) (fn-ptx-cap h3 id inc fn-rtc-st)))
              ;; the suffix outgrows its workspace: refused before any log action
              (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                (mv m2 (append acq rel r2) (+ cost c2))))
             (e
              (mv-let (ok pre ins ioff sh st) (fn-ptx-acc-end a (- len e))
                (let* ((ioff (if (consp ins) (nfix ioff) len))
                       (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))
                       (end (+ off2 (len st)))
                       (rlen (+ (len pre) len (len ins) (- end start)))
                       (b1 (append (fn-ptx-frame-header rlen) (true-list-fix (fn-ptx-kd-last kd)) pre)))
                  (if (not (and ok (<= ioff len) (<= (+ 32 rlen) (fn-ptx-fmax m))
                                (<= (+ (len b1) (len ins)) (fn-ptx-cap h1 id inc fn-rtc-st))
                                (<= (+ end 32) (fn-ptx-cap h3 id inc fn-rtc-st))))
                      (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                        (mv m2 (append acq rel r2) (+ cost c2)))
                    (mv (fn-ptx-chg m1 :ph :hashing :k 0
                                    :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len e (fn-ptx-cur-txid cur) ioff)
                                    :b1 (list h1 g1 (len b1) (len ins)) :b3 (list h3 g3 end start) :hs (list 0 nil) :acc nil)
                        (append acq (list (list :write h1 g1 0 (append b1 ins)))
                                (fn-ptx-write-nz h3 g3 start (take (- *fn-ptx-sufhead-max* start) sh))
                                (fn-ptx-write-nz h3 g3 off sp) (fn-ptx-write-nz h3 g3 off2 st)
                                (list (fn-ptx-timer)))
                        cost)))))
             ((< (+ pos w 3) lim)
              ;; no head end yet: the window fed, its suffix part written, continue
              (mv (fn-ptx-chg m1 :cur (list (fn-ptx-cur-fid cur) (fn-ptx-cur-finc cur) bp len (+ pos w) (fn-ptx-cur-txid cur) len)
                              :b3 (list h3 g3 off2 *fn-ptx-sufhead-max*) :acc a)
                  (append acq (fn-ptx-write-nz h3 g3 off sp) (list (fn-ptx-timer)))
                  cost))
             (t
              ;; no head within the head limit: refused before any log action
              (mv-let (m2 r2 c2) (fn-ptx-end mr :refused kd ext nil nil id inc fn-rtc-st)
                (mv m2 (append acq rel r2) (+ cost c2))))))))))))

(defun ptxt-v2-machine-observe (ctx art gs)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((enc (fn-pctx-encode ctx)) (data (append enc art gs))
        (tx (fn-pctx-get 0 ctx))
        (m (fn-ptx-mk :reading 0 (list 2 1 3 (len data) 0 tx (len data) 0 0)
              nil (fn-ptx-kd-mk 0 (make-list 32 :initial-element 0) 8192 tx 0)
              1048576 1048576 nil nil nil nil nil '(1 1048576 65536)
              (fn-pacc-begin (list tx ctx)))))
  (with-local-stobj fn-rtc-st
   (mv-let (ans fn-rtc-st)
    (let* ((fn-rtc-st (fn-rtc-st-init (list 3 4 0 1 0 1 (len data) 3 65667) fn-rtc-st))
           (fn-rtc-st (fn-rtc-st-set-slot 1 '(1 :live nil) fn-rtc-st))
           (fn-rtc-st (fn-rtc-st-reset 3 0 '(:workspace 1 1) fn-rtc-st))
           (fn-rtc-st (fn-rtc-st-splice 3 0 data fn-rtc-st)))
     (mv-let (new reqs cost) (fn-ptx-read m 100000 1 1 fn-rtc-st)
      (declare (ignore reqs cost))
      (mv-let (old old-reqs old-cost) (ptxt-v2-old-read m 100000 1 1 fn-rtc-st)
       (declare (ignore old-reqs old-cost))
       (mv (list (len (fn-pctx-get 1 ctx)) (len enc) (len art) (len gs)
                 (fn-ptx-ph new) (fn-ptx-cur new) (fn-ptx-spans new)
                 (fn-ptx-ph old) (fn-ptx-cur old) (fn-ptx-spans old) (fn-ptx-b3 new)) fn-rtc-st))))
    ans))))
(defconst *ptxt-v2-2165-rec*
 (fn-pacc-prepared-record *pc4d-wide-s* *pc4-obs* *pc4d-wide-art* *pc4d-wide-inj*))
(make-event (value `(defconst *ptxt-v2-2165-observation*
 ',(ptxt-v2-machine-observe
   (fn-pctx-of-prepared *pc4d-wide-s* *ptxt-v2-2165-rec* *pc4d-wide-art* *pc4d-wide-inj*)
   *pc4d-wide-art* (fn-pacc-prepared-gsec *ptxt-v2-2165-rec*)))))
(make-event (value `(defconst *ptxt-v2-2238-observation*
 ',(ptxt-v2-machine-observe (m2-max-ctx) *m2-max-art* (fn-pacc-prepared-gsec *m2-max-rec*)))))
(make-event (value `(defconst *ptxt-v2-2729-observation*
 ',(ptxt-v2-machine-observe (pa1-max-ctx) *pa1-max-art* (fn-pacc-prepared-gsec *pa1-max-rec*)))))
(defun ptxt-v2-layout-observedp (x pre)
 (let* ((base (nth 1 x)) (alen (nth 2 x)) (glen (nth 3 x))
        (cur (nth 5 x)) (spans (nth 6 x)) (old-cur (nth 8 x)))
  (and (equal (nth 0 x) pre) (equal (nth 4 x) :hashing)
       (equal (fn-ptx-cur-base cur) base) (equal (fn-ptx-cur-len cur) alen)
       (equal (fn-ptx-cur-glen cur) glen)
       (or (zp (fn-ptx-cur-ioff cur)) (member-equal (list 3 base (fn-ptx-cur-ioff cur)) spans))
       (or (equal (fn-ptx-cur-ioff cur) alen)
           (member-equal (list 3 (+ base (fn-ptx-cur-ioff cur)) (- alen (fn-ptx-cur-ioff cur))) spans))
       (equal (fn-ptx-buf-cut (nth 10 x)) 9)
       (or (zp glen) (member-equal (list 3 (+ base alen) glen) spans))
       (equal (nth 7 x) :hashing)
       (equal (fn-ptx-cur-base old-cur) 0)
       (equal (fn-ptx-cur-len old-cur) (+ base alen glen))
       (not (equal (nth 6 x) (nth 9 x))))))
(defthm ptxt-v2-machine-reads-the-2165-context-layout
 (ptxt-v2-layout-observedp *ptxt-v2-2165-observation* 2165) :rule-classes nil)
(defthm ptxt-v2-machine-reads-the-2238-context-layout
 (ptxt-v2-layout-observedp *ptxt-v2-2238-observation* 2238) :rule-classes nil)
(defthm ptxt-v2-machine-reads-the-2729-context-layout
 (ptxt-v2-layout-observedp *ptxt-v2-2729-observation* 2729) :rule-classes nil)))

; Amendment 4: the old four-field unfolding is false, and the
; corrected fifth field is equal on precisely the same hashing input.
(with-guard-checking-event :none
 (encapsulate ()
 (defun ptxt-hash-0h-old-rhs (m q id inc fn-rtc-st)
  (declare (xargs :guard t :verify-guards nil :stobjs fn-rtc-st))
  (let* ((nmsg (fn-ptx-hnmsg m)) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (b3 (fn-ptx-b3 m))
                (m0 (fn-ptx-chg m :committed nil))
                (pos (fn-ptx-hpos m q id inc fn-rtc-st)) (stk (fn-ptx-hstk m q id inc fn-rtc-st)))
           (if (< (+ pos 1024) nmsg)
               (fn-ptx-chg m0 :hs (list pos stk))
             (let* ((trailer (fn-ptx-finish-digest pos stk nmsg (fn-ptx-spans m) id inc fn-rtc-st))
                    (pad (fn-ptx-pad-len (+ nmsg 32) (fn-ptx-unit m)))
                    (b3x (list (fn-ptx-buf-h b3) (fn-ptx-buf-g b3) (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3)))
                    (elen (+ nmsg 32 pad))
                    (front (fn-ptx-kd-frontier kd)))
               (if (fn-olr-extension-needed-p front elen ext (fn-ptx-unit m))
                   (let ((nx (fn-olr-extension-target front elen ext (fn-ptx-unit m))))
                     (if (<= (expt 2 64) nx)
                         (mv-let (m2 r2 c2) (fn-ptx-end m0 :refused kd ext nil nil id inc fn-rtc-st) (declare (ignore r2 c2)) m2)
                       (fn-ptx-chg m0 :ph :extending :k 0 :nxt nx :b3 b3x :hs (list nmsg trailer pad) :evd nil)))
                 (fn-ptx-chg m0 :ph :payload-writing :k 0 :nxt ext :b3 b3x :hs (list nmsg trailer pad) :evd nil))))))
 (defun ptxt-hash-layout-witness ()
  (fn-ptx-mk :hashing 0 '(2 1 3 1 0 1 1 33 1) nil
   (fn-ptx-kd-mk 0 (make-list 32 :initial-element 0) 8192 1 0)
   1048576 1048576 '(0 1 42 0) '(1 1 9 9 9) '(0 nil)
   nil nil '(1 1048576 65536) nil))
 (defun ptxt-hash-layout-observe ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-rtc-st
   (mv-let (ans fn-rtc-st)
    (let* ((m (ptxt-hash-layout-witness))
           (fn-rtc-st (fn-rtc-st-init '(3 4 0 1 0 1 64 3 128) fn-rtc-st)))
     (mv-let (lhs reqs cost) (fn-ptx-hash m 0 1 1 fn-rtc-st)
      (declare (ignore reqs cost))
      (let ((rhs (ptxt-hash-0h-old-rhs m 0 1 1 fn-rtc-st)))
       (mv (list (fn-ptx-okp m) (equal lhs rhs)
          (fn-ptx-ph lhs) (fn-ptx-b3 lhs) (fn-ptx-ph rhs) (fn-ptx-b3 rhs)
          (equal lhs (fn-ptx-chg rhs :b3 (append (fn-ptx-b3 rhs) (list (fn-ptx-buf-cut (fn-ptx-b3 m))))))) fn-rtc-st))))
    ans)))
 (make-event (value `(defconst *ptxt-hash-layout-observation* ',(ptxt-hash-layout-observe))))
 (defthm ptxt-old-hash-unfolding-refuted-new-equality-holds
  (equal *ptxt-hash-layout-observation*
   '(t nil :payload-writing (1 1 41 9 9) :payload-writing (1 1 41 9) t))
  :rule-classes nil)))
