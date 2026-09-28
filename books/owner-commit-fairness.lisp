; fn: the owner's queue is fair -- a control request waits at most a bounded
; number of quanta and batches, however sustained the POST load (lane
; durability-bugs, 2026-09-28; row I3 of the 6.6.0 completion list; PKT-700/
; PKT-701's owner, scheduler-3's finding).
;
; The finding.  books/owner-commit-pipeline.lisp let a START-NEXT prepare the
; next batch behind the one in flight, and the COMPLETE sealed it, so under
; sustained POST load a batch was always in flight.  While one is,
; fn-ocs-next admits only :inspect, :commit and :reader
; (fn-ocs-in-flight-admits-only-inspect-commit-and-reader): a control, poster
; or transit request waited for as long as the POSTs kept coming.  PRF-248's
; control bound (fn-osch-control-waits-at-most-the-bound) counts only the
; picks OUTSIDE flight, and there were none.
;
; The rule.  The committer's wake (fn-ocp-wake, BLOCKED) never prepares a
; next batch while a shut-out class waits at the gate.  The batches already
; sealed or open complete, the owner leaves flight, and the four classes'
; cyclic pick serves the waiter.
;
; The bound (KEYSTONE fn-ocf-control-waits-at-most-the-bound).  The subject is
; the host's scheduling surface: fn-otm-next (host/native/owner.lisp
; fnn-owner-gate-pick, at every release of the owner and every arrival at an
; idle one) and fn-otm-commit-event (fnn-owner-commit-event, inside the
; committer's :commit quanta), with the committer's wake fn-otm-committer-
; wake (fnn-owner-commit-wake) deciding whether a START-NEXT runs.  ITEMS are
; the successive picks, each (W EVENTS): W the six waiting counts at the
; pick, EVENTS what the committer reports if the pick is a :commit.  The
; hypotheses (fn-ocf-okp):
;   - a control request waits at every pick (slot 0 of W);
;   - a :commit quantum reports one of the host's shapes: outside flight a
;     START (:started, :started-none or :started-uncertain); in flight a
;     START-NEXT (:next-none, :next-uncertain, or :next-started only when
;     the committer's wake at that W is :start-next) or a COMPLETE (the
;     barrier's word, :fenced or :failed, then :completed).
; Then before the first control pick (or the owner's stop), the quanta that
; are neither :inspect, nor a :reader or an empty START-NEXT while a batch is
; in flight, number at most fn-ocf-potential of the starting value, which is
; at most 10 (fn-ocf-potential-at-most-ten): at most 3 of the four classes'
; (PRF-248), at most one START outside flight, and the COMPLETEs of at most
; three batches.  And at most TWO batches are sealed in that time
; (fn-ocf-control-waits-at-most-two-seals): the next batch already open, and
; one START that was already due.
;
; What is not counted, and why it is bounded otherwise:
;   - :inspect quanta alternate (fn-ocs-inspect-waits-at-most-one, PRF-267);
;   - a :reader quantum in flight runs while the barrier's fdatasync runs and
;     a waiting COMPLETE goes first (fn-ocs-in-flight-commit-before-reader),
;     so readers delay the waiter by at most one quantum per barrier;
;   - a START-NEXT that took nobody is an owner quantum with no I/O
;     (books/owner-time-model.lisp's read bound counts it the same way).
; So a control request's wall-clock wait is at most three barriers
; (books/owner-time-model.lisp bounds each by the disk's deadline H, after
; which the stall answers) plus ten owner quanta plus the interleaved
; :inspect quanta and one reader quantum per barrier.
(in-package "ACL2")
(include-book "owner-time-model")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The walk.

(defun fn-ocf-item-w (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-ocf-item-events (x)
  (declare (xargs :guard t))
  (if (and (consp x) (consp (cdr x))) (cadr x) nil))

; The host's quantum shapes (host/native/owner.lisp fnn-owner-commit-pipeline):
; S the value after the :commit pick, W that pick's counts.
(defun fn-ocf-quantum-okp (s w events)
  (declare (xargs :guard t))
  (if (fn-ocs-in-flight-p (fn-otm-phase s))
      (or (equal events '(:next-none))
          (equal events '(:next-uncertain))
          (and (equal events '(:next-started))
               (equal (fn-otm-committer-wake s nil t w) :start-next))
          (equal events '(:fenced :completed))
          (equal events '(:failed :completed)))
    (or (equal events '(:started))
        (equal events '(:started-none))
        (equal events '(:started-uncertain)))))

; One quantum's events through the host's entry: (mv STOPPED SEALS S').  A
; :stop or :fault ends the owner's service (exit 3 or 4): the waiter is
; answered by the stop, and the walk ends there.
(defun fn-ocf-events (s events)
  (declare (xargs :guard t :measure (len events)))
  (if (consp events)
      (mv-let (a s2) (fn-otm-commit-event s (car events))
        (if (or (eq a :stop) (eq a :fault))
            (mv t 0 s2)
          (mv-let (stopped seals s3) (fn-ocf-events s2 (cdr events))
            (mv stopped (+ (if (eq a :sync) 1 0) seals) s3))))
    (mv nil 0 s)))

; One pick and, for a :commit, its quantum: (mv CLASS STOPPED SEALS S').
(defun fn-ocf-step (s item)
  (declare (xargs :guard t))
  (mv-let (class s2) (fn-otm-next s (fn-ocf-item-w item))
    (if (eq class :commit)
        (mv-let (stopped seals s3) (fn-ocf-events s2 (fn-ocf-item-events item))
          (mv class stopped seals s3))
      (mv class nil 0 s2))))

; The quanta the bound counts: not :inspect, and not a :reader or an empty
; START-NEXT while a batch is in flight.
(defun fn-ocf-countedp (class inflight events)
  (declare (xargs :guard t))
  (cond ((null class) nil)
        ((eq class :inspect) nil)
        ((and inflight (eq class :reader)) nil)
        ((and inflight (eq class :commit) (equal events '(:next-none))) nil)
        (t t)))

(defun fn-ocf-delay (s items)
  (declare (xargs :guard t :measure (len items)))
  (if (consp items)
      (mv-let (class stopped seals s2) (fn-ocf-step s (car items))
        (declare (ignore seals))
        (if (eq class :control)
            0
          (+ (if (fn-ocf-countedp class (fn-ocs-in-flight-p (fn-otm-phase s))
                                  (fn-ocf-item-events (car items)))
                 1 0)
             (if stopped 0 (fn-ocf-delay s2 (cdr items))))))
    0))

(defun fn-ocf-seals (s items)
  (declare (xargs :guard t :measure (len items)))
  (if (consp items)
      (mv-let (class stopped seals s2) (fn-ocf-step s (car items))
        (if (eq class :control)
            0
          (+ seals (if stopped 0 (fn-ocf-seals s2 (cdr items))))))
    0))

(defun fn-ocf-okp (s items)
  (declare (xargs :guard t :measure (len items)))
  (if (consp items)
      (let ((w (fn-ocf-item-w (car items))))
        (mv-let (class picked) (fn-otm-next s w)
          (mv-let (c stopped seals s2) (fn-ocf-step s (car items))
            (declare (ignore c seals))
            (and (posp (fn-osch-waits 0 w))
                 (implies (eq class :commit)
                          (fn-ocf-quantum-okp picked w (fn-ocf-item-events (car items))))
                 (or (eq class :control)
                     stopped
                     (fn-ocf-okp s2 (cdr items)))))))
    t))

; -----------------------------------------------------------------------------
; The potential: M the four classes' distance to the control slot, DUE
; whether a START can still be admitted before it (the commit class's passes
; plus that distance reach the commit bound), B the batches to complete (a
; staged batch 2, a fenced or failed one 1, an open next batch 2).

(defun fn-ocf-ocm (s)
  (declare (xargs :guard t))
  (fn-ocs-ocm (fn-ocp-ocs (fn-otm-ocp s))))

(defun fn-ocf-m (s)
  (declare (xargs :guard t))
  (fn-osch-measure (fn-osch-cursor (fn-ocm-sched (fn-ocf-ocm s)))))

(defun fn-ocf-due (s)
  (declare (xargs :guard t))
  (if (<= *fn-ocm-bound* (+ (fn-ocm-skipped (fn-ocf-ocm s)) (fn-ocf-m s))) 1 0))

(defun fn-ocf-b (s)
  (declare (xargs :guard t))
  (+ (let ((p (fn-otm-phase s)))
       (cond ((eq p :staged) 2) ((fn-ocs-in-flight-p p) 1) (t 0)))
     (if (fn-otm-open-next s) 2 0)))

(defun fn-ocf-potential (s)
  (declare (xargs :guard t))
  (+ (fn-ocf-m s) (* 3 (fn-ocf-due s)) (fn-ocf-b s)))

(defun fn-ocf-seal-potential (s)
  (declare (xargs :guard t))
  (+ (fn-ocf-due s) (if (fn-otm-open-next s) 1 0)))

; =============================================================================
; Theorems.

; The committer's events keep the four classes' state; the pipeline's step
; decides the phase and the next batch.
(defthm fn-ocf-ocm-of-commit-event
  (equal (fn-ocf-ocm (mv-nth 1 (fn-otm-commit-event s e))) (fn-ocf-ocm s))
  :hints (("Goal" :in-theory (enable fn-otm-commit-event fn-ocp-commit-event fn-ocs-make
                                     fn-ocs-ocm fn-otm-make fn-otm-ocp fn-ocp-make fn-ocp-ocs))))

(defthm fn-ocf-commit-event-unfolds
  (and (equal (mv-nth 0 (fn-otm-commit-event s e))
              (mv-nth 0 (fn-ocp-commit-step (fn-otm-phase s) (fn-otm-open-next s) e)))
       (equal (fn-otm-phase (mv-nth 1 (fn-otm-commit-event s e)))
              (let ((p (mv-nth 1 (fn-ocp-commit-step (fn-otm-phase s) (fn-otm-open-next s) e))))
                (if (fn-ocs-in-flight-p p) p :idle)))
       (equal (fn-otm-open-next (mv-nth 1 (fn-otm-commit-event s e)))
              (if (mv-nth 2 (fn-ocp-commit-step (fn-otm-phase s) (fn-otm-open-next s) e)) t nil)))
  :hints (("Goal" :in-theory (enable fn-otm-commit-event fn-ocp-commit-event fn-ocs-make
                                     fn-ocs-phase fn-otm-phase fn-otm-open-next fn-ocp-open-next
                                     fn-otm-make fn-otm-ocp fn-ocp-make fn-ocp-ocs))))

; The gate's pick keeps the phase and the next batch; in flight it keeps the
; four classes' state too; outside flight it is fn-ocm-next's or an :inspect.
(defthm fn-ocf-next-keeps-phase-and-next
  (and (equal (fn-otm-open-next (mv-nth 1 (fn-otm-next s w))) (fn-otm-open-next s))
       (equal (fn-otm-phase (mv-nth 1 (fn-otm-next s w))) (fn-otm-phase s)))
  :hints (("Goal" :in-theory (enable fn-otm-next fn-ocp-next fn-ocs-next fn-ocs-make fn-ocs-phase
                                     fn-otm-phase fn-otm-open-next fn-ocp-open-next fn-otm-make
                                     fn-otm-ocp fn-ocp-make fn-ocp-ocs))))

(defthm fn-ocf-next-in-flight
  (implies (fn-ocs-in-flight-p (fn-otm-phase s))
           (and (equal (fn-ocf-ocm (mv-nth 1 (fn-otm-next s w))) (fn-ocf-ocm s))
                (member-equal (mv-nth 0 (fn-otm-next s w)) '(:inspect :commit :reader nil))))
  :hints (("Goal" :in-theory (enable fn-otm-next fn-ocp-next fn-ocs-next fn-ocs-make fn-ocs-ocm
                                     fn-ocs-phase fn-otm-phase fn-ocf-ocm fn-otm-make fn-otm-ocp
                                     fn-ocp-make fn-ocp-ocs))))

(defthm fn-ocf-next-idle
  (implies (not (fn-ocs-in-flight-p (fn-otm-phase s)))
           (let ((class (mv-nth 0 (fn-otm-next s w)))
                 (ocm2 (fn-ocf-ocm (mv-nth 1 (fn-otm-next s w))))
                 (on (fn-ocm-next (fn-ocf-ocm s) (fn-ocs-w4 w) (fn-ocs-commit-waits-p w))))
             (or (and (member-equal class '(:inspect nil)) (equal ocm2 (fn-ocf-ocm s)))
                 (and (equal class (mv-nth 0 on)) class (equal ocm2 (mv-nth 1 on))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-otm-next fn-ocp-next fn-ocs-next fn-ocs-make fn-ocs-ocm
                                   fn-ocs-phase fn-otm-phase fn-ocf-ocm fn-otm-make fn-otm-ocp
                                   fn-ocp-make fn-ocp-ocs)
                                  (fn-ocm-next fn-ocs-w4 fn-ocs-commit-waits-p
                                   fn-ocs-inspect-waits-p fn-ocs-reader-waits-p)))))

(local
 (defthm fn-ocf-norm-cases
   (or (equal (fn-osch-norm c) 0) (equal (fn-osch-norm c) 1)
       (equal (fn-osch-norm c) 2) (equal (fn-osch-norm c) 3))
   :rule-classes nil))

(local
 (defthm fn-ocf-pick-from-the-control-slot
   (implies (and (posp (fn-osch-waits 0 w)) (equal (fn-osch-norm c) 0))
            (equal (fn-osch-pick c w) 0))
   :hints (("Goal" :in-theory (e/d (fn-osch-pick fn-osch-scan fn-osch-succ) (fn-osch-waits fn-osch-norm))))))

(local
 (defthm fn-ocf-pick-past-the-control-slot
   (implies (and (posp (fn-osch-waits 0 w)) (not (equal (fn-osch-pick c w) 0)))
            (and (integerp (fn-osch-pick c w))
                 (not (equal (fn-osch-norm c) 0))
                 (<= (fn-osch-norm c) (fn-osch-pick c w))
                 (< (fn-osch-pick c w) *fn-osch-slots*)))
   :hints (("Goal" :use fn-ocf-norm-cases
            :in-theory (e/d (fn-osch-pick fn-osch-scan fn-osch-succ) (fn-osch-waits fn-osch-norm))))))

(local
 (defthm fn-ocf-measure-of-norm-succ
   (implies (and (integerp j) (<= (fn-osch-norm c) j) (< j *fn-osch-slots*)
                 (not (equal (fn-osch-norm c) 0)))
            (< (fn-osch-measure (fn-osch-norm (fn-osch-succ j))) (fn-osch-measure c)))
   :rule-classes :linear
   :hints (("Goal" :use fn-ocf-norm-cases
            :cases ((equal j 1) (equal j 2) (equal j 3))
            :in-theory (e/d (fn-osch-succ) (fn-osch-norm))))))

(local
 (defthm fn-ocf-osch-step-decreases
   (implies (and (posp (fn-osch-waits 0 w)) (not (equal (fn-osch-pick c w) 0)))
            (< (fn-osch-measure (fn-osch-norm (fn-osch-succ (fn-osch-pick c w))))
               (fn-osch-measure c)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable fn-osch-pick fn-osch-measure fn-osch-succ fn-osch-norm
                                       fn-osch-waits fn-ocf-measure-of-norm-succ
                                       fn-ocf-pick-past-the-control-slot)
            :use ((:instance fn-ocf-pick-past-the-control-slot)
                  (:instance fn-ocf-measure-of-norm-succ (j (fn-osch-pick c w))))))))

(local
 (defthm fn-ocf-measure-at-most-three
   (and (natp (fn-osch-measure c)) (<= (fn-osch-measure c) 3))
   :rule-classes ((:linear :corollary (<= (fn-osch-measure c) 3))
                  (:type-prescription :corollary (natp (fn-osch-measure c))))
   :hints (("Goal" :use fn-ocf-norm-cases :in-theory (disable fn-osch-norm)))))

(defthm fn-ocf-control-waiting-is-not-idle
  (implies (posp (fn-osch-waits 0 w)) (not (fn-osch-idlep w)))
  :hints (("Goal" :in-theory (enable fn-osch-idlep))))

; While control waits, a pick of the four classes and the commit class is
; somebody's; a commit pick was due (its passes reached the bound) and
; resets them; any other pick that is not control's moves the cursor closer
; to the control slot and passes the commit at most once more.
(defthm fn-ocf-ocm-next-with-control-waiting
  (implies (posp (fn-osch-waits 0 w4))
           (let* ((on (fn-ocm-next ocm w4 commit))
                  (class (mv-nth 0 on))
                  (ocm2 (mv-nth 1 on)))
             (and class
                  (implies (equal class :commit)
                           (and (<= 4 (fn-ocm-skipped ocm))
                                (equal (fn-ocm-sched ocm2) (fn-ocm-sched ocm))
                                (equal (fn-ocm-skipped ocm2) 0)))
                  (implies (and (not (equal class :commit)) (not (equal class :control)))
                           (and (< (fn-osch-measure (fn-osch-cursor (fn-ocm-sched ocm2)))
                                   (fn-osch-measure (fn-osch-cursor (fn-ocm-sched ocm))))
                                (<= (fn-ocm-skipped ocm2) (+ 1 (fn-ocm-skipped ocm))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ocm-next fn-ocm-sched fn-ocm-skipped)
                                  (fn-osch-next fn-osch-cursor fn-osch-pick fn-osch-measure
                                   fn-osch-succ fn-osch-norm fn-osch-waits fn-osch-idlep))
           :use ((:instance fn-osch-pick-nil-iff-idle
                            (c (fn-osch-cursor (fn-ocm-sched ocm))) (w w4))
                 (:instance fn-ocf-osch-step-decreases
                            (c (fn-osch-cursor (fn-ocm-sched ocm))) (w w4))
                 (:instance fn-osch-pick-is-a-slot
                            (c (fn-osch-cursor (fn-ocm-sched ocm))) (w w4))))))

; One quantum's events in the host's shapes.
(defthm fn-ocf-events-in-flight
  (implies (and (fn-ocs-in-flight-p (fn-otm-phase s))
                (member-equal events '((:next-none) (:next-uncertain)
                                       (:fenced :completed) (:failed :completed))))
           (mv-let (stopped seals s3) (fn-ocf-events s events)
             (and (equal (fn-ocf-ocm s3) (fn-ocf-ocm s))
                  (implies (not stopped)
                           (and (if (equal events '(:next-none))
                                    (equal (fn-ocf-b s3) (fn-ocf-b s))
                                  (< (fn-ocf-b s3) (fn-ocf-b s)))
                                (<= (+ seals (if (fn-otm-open-next s3) 1 0))
                                    (if (fn-otm-open-next s) 1 0)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ocf-events fn-ocf-b fn-ocp-commit-step fn-ocs-in-flight-p)
                                  (fn-otm-commit-event fn-ocf-ocm fn-otm-phase fn-otm-open-next)))))

(defthm fn-ocf-events-idle
  (implies (and (not (fn-ocs-in-flight-p (fn-otm-phase s)))
                (member-equal events '((:started) (:started-none) (:started-uncertain))))
           (mv-let (stopped seals s3) (fn-ocf-events s events)
             (and (equal (fn-ocf-ocm s3) (fn-ocf-ocm s))
                  (implies (not stopped)
                           (and (<= (fn-ocf-b s3) 2)
                                (<= seals 1)
                                (not (fn-otm-open-next s3)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ocf-events fn-ocf-b fn-ocp-commit-step fn-ocs-in-flight-p)
                                  (fn-otm-commit-event fn-ocf-ocm fn-otm-phase fn-otm-open-next)))))

(defthm fn-ocf-events-seals
  (and (implies (and (fn-ocs-in-flight-p (fn-otm-phase s))
                     (member-equal events '((:next-none) (:next-uncertain)
                                            (:fenced :completed) (:failed :completed))))
                (<= (mv-nth 1 (fn-ocf-events s events)) (if (fn-otm-open-next s) 1 0)))
       (implies (and (not (fn-ocs-in-flight-p (fn-otm-phase s)))
                     (member-equal events '((:started) (:started-none) (:started-uncertain))))
                (<= (mv-nth 1 (fn-ocf-events s events)) 1)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ocf-events fn-ocp-commit-step fn-ocs-in-flight-p)
                                  (fn-otm-commit-event fn-ocf-ocm fn-otm-phase fn-otm-open-next)))))

(defthm fn-ocf-w4-control
  (equal (fn-osch-waits 0 (fn-ocs-w4 w)) (fn-osch-waits 0 w))
  :hints (("Goal" :in-theory (enable fn-ocs-w4 fn-osch-waits fn-osch-nth))))

; The rule, over the host's wake: while control waits the committer never
; prepares another batch.
(defthm fn-ocf-no-start-next-while-control-waits
  (implies (posp (fn-osch-waits 0 w))
           (not (equal (fn-otm-committer-wake s r q w) :start-next)))
  :hints (("Goal" :in-theory (enable fn-otm-committer-wake fn-ocp-committer-wake fn-ocp-wake
                                     fn-ocp-excluded-waits-p))))

(local
 (defthm fn-ocf-osch-next-not-inspect
   (and (not (equal (mv-nth 0 (fn-osch-next s w)) :inspect))
        (not (equal (car (fn-osch-next s w)) :inspect)))
   :hints (("Goal" :in-theory (enable fn-osch-next)))))

(local
 (defthm fn-ocf-ocm-next-not-inspect
   (and (not (equal (mv-nth 0 (fn-ocm-next s w c)) :inspect))
        (not (equal (car (fn-ocm-next s w c)) :inspect)))
   :hints (("Goal" :in-theory (e/d (fn-ocm-next) (fn-osch-next fn-osch-idlep))))))

(defthm fn-ocf-idle-pick-potential
  (implies (and (not (fn-ocs-in-flight-p (fn-otm-phase s)))
                (posp (fn-osch-waits 0 w)))
           (let ((class (mv-nth 0 (fn-otm-next s w)))
                 (s2 (mv-nth 1 (fn-otm-next s w))))
             (and (implies (member-equal class '(:inspect nil))
                           (and (equal (fn-ocf-m s2) (fn-ocf-m s))
                                (equal (fn-ocf-due s2) (fn-ocf-due s))))
                  (implies (equal class :commit)
                           (and (equal (fn-ocf-due s) 1) (equal (fn-ocf-due s2) 0)
                                (equal (fn-ocf-m s2) (fn-ocf-m s))))
                  (implies (not (member-equal class '(:inspect nil :commit :control)))
                           (and (< (fn-ocf-m s2) (fn-ocf-m s))
                                (<= (fn-ocf-due s2) (fn-ocf-due s)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ocf-m fn-ocf-due)
                                  (fn-otm-next fn-ocf-ocm fn-otm-phase fn-ocm-next fn-ocs-w4
                                   fn-ocs-commit-waits-p fn-osch-measure fn-osch-cursor
                                   fn-ocm-sched fn-ocm-skipped fn-osch-waits fn-ocs-in-flight-p
                                   fn-otm-next-is-ocp-next))
           :use ((:instance fn-ocf-next-idle)
                 (:instance fn-ocf-ocm-next-with-control-waiting
                            (ocm (fn-ocf-ocm s)) (w4 (fn-ocs-w4 w))
                            (commit (fn-ocs-commit-waits-p w)))))))

(defthm fn-ocf-b-bounds
  (and (natp (fn-ocf-b s)) (<= (fn-ocf-b s) 4)
       (implies (fn-ocs-in-flight-p (fn-otm-phase s)) (<= 1 (fn-ocf-b s)))
       (implies (not (fn-ocs-in-flight-p (fn-otm-phase s)))
                (equal (fn-ocf-b s) (if (fn-otm-open-next s) 2 0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ocf-b fn-ocs-in-flight-p))))

(defthm fn-ocf-next-keeps-b
  (equal (fn-ocf-b (mv-nth 1 (fn-otm-next s w))) (fn-ocf-b s))
  :hints (("Goal" :in-theory (e/d (fn-ocf-b) (fn-otm-next)))))

(defthm fn-ocf-due-bounds
  (or (equal (fn-ocf-due s) 0) (equal (fn-ocf-due s) 1))
  :rule-classes nil)

(defthm fn-ocf-step-potential
  (let* ((w (fn-ocf-item-w item))
         (events (fn-ocf-item-events item))
         (class (mv-nth 0 (fn-otm-next s w)))
         (picked (mv-nth 1 (fn-otm-next s w)))
         (r (fn-ocf-step s item))
         (stopped (mv-nth 1 r))
         (seals (mv-nth 2 r))
         (s2 (mv-nth 3 r))
         (counted (if (fn-ocf-countedp class (fn-ocs-in-flight-p (fn-otm-phase s)) events) 1 0)))
    (implies (and (posp (fn-osch-waits 0 w))
                  (implies (equal class :commit) (fn-ocf-quantum-okp picked w events))
                  (not (equal class :control)))
             (and (<= counted (fn-ocf-potential s))
                  (<= seals (fn-ocf-seal-potential s))
                  (implies (not stopped)
                           (and (<= (+ counted (fn-ocf-potential s2)) (fn-ocf-potential s))
                                (<= (+ seals (fn-ocf-seal-potential s2))
                                    (fn-ocf-seal-potential s)))))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((fn-ocs-in-flight-p (fn-otm-phase s)))
           :in-theory (e/d (fn-ocf-step fn-ocf-quantum-okp fn-ocf-countedp fn-ocf-potential
                            fn-ocf-seal-potential fn-ocf-m fn-ocf-due)
                           (fn-otm-next fn-ocf-events fn-ocf-ocm fn-otm-phase fn-otm-open-next
                            fn-ocm-next fn-ocs-w4 fn-ocs-commit-waits-p fn-osch-measure
                            fn-osch-cursor fn-ocm-sched fn-ocm-skipped fn-osch-waits
                            fn-otm-committer-wake fn-ocs-in-flight-p fn-otm-next-is-ocp-next
                            fn-ocp-next-is-ocs-next fn-otm-commit-event-is-ocp-commit-event
                            fn-ocs-next fn-ocp-next fn-osch-pick fn-ocf-b))
           :use ((:instance fn-ocf-idle-pick-potential (w (fn-ocf-item-w item)))
                 (:instance fn-ocf-next-in-flight (w (fn-ocf-item-w item)))
                 (:instance fn-ocf-events-in-flight
                            (s (mv-nth 1 (fn-otm-next s (fn-ocf-item-w item))))
                            (events (fn-ocf-item-events item)))
                 (:instance fn-ocf-events-idle
                            (s (mv-nth 1 (fn-otm-next s (fn-ocf-item-w item))))
                            (events (fn-ocf-item-events item)))
                 (:instance fn-ocf-events-seals
                            (s (mv-nth 1 (fn-otm-next s (fn-ocf-item-w item))))
                            (events (fn-ocf-item-events item)))
                 (:instance fn-ocf-due-bounds (s s))
                 (:instance fn-ocf-b-bounds (s s))
                 (:instance fn-ocf-b-bounds (s (mv-nth 1 (fn-otm-next s (fn-ocf-item-w item)))))))))

(defthm fn-ocf-step-class-is-the-pick
  (equal (mv-nth 0 (fn-ocf-step s item)) (mv-nth 0 (fn-otm-next s (fn-ocf-item-w item))))
  :hints (("Goal" :in-theory (e/d (fn-ocf-step) (fn-otm-next fn-ocf-events)))))

(defthm fn-ocf-potential-natp
  (natp (fn-ocf-potential s))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-ocf-b)
           :use ((:instance fn-ocf-measure-at-most-three
                            (c (fn-osch-cursor (fn-ocm-sched (fn-ocf-ocm s)))))))))

(defthm fn-ocf-seal-potential-natp
  (natp (fn-ocf-seal-potential s))
  :rule-classes :type-prescription)

(defthm fn-ocf-potential-at-most-ten
  (<= (fn-ocf-potential s) 10)
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-ocf-b fn-ocf-due)
           :use ((:instance fn-ocf-b-bounds) (:instance fn-ocf-due-bounds)))))

(defthm fn-ocf-seal-potential-at-most-two
  (<= (fn-ocf-seal-potential s) 2)
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-ocf-due) :use ((:instance fn-ocf-due-bounds)))))

(defthm fn-ocf-delay-at-most-the-potential
  (implies (fn-ocf-okp s items)
           (<= (fn-ocf-delay s items) (fn-ocf-potential s)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-ocf-delay s items)
           :in-theory (e/d (fn-ocf-delay fn-ocf-okp)
                           (fn-ocf-step fn-otm-next fn-ocf-potential fn-ocf-countedp fn-otm-phase
                            fn-ocs-in-flight-p fn-ocf-quantum-okp fn-osch-waits
                            fn-ocf-seal-potential)))
          ("Subgoal *1/2" :use ((:instance fn-ocf-step-potential (item (car items)))))))

(defthm fn-ocf-seals-at-most-the-seal-potential
  (implies (fn-ocf-okp s items)
           (<= (fn-ocf-seals s items) (fn-ocf-seal-potential s)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-ocf-seals s items)
           :in-theory (e/d (fn-ocf-seals fn-ocf-okp)
                           (fn-ocf-step fn-otm-next fn-ocf-potential fn-ocf-countedp fn-otm-phase
                            fn-ocs-in-flight-p fn-ocf-quantum-okp fn-osch-waits
                            fn-ocf-seal-potential)))
          ("Subgoal *1/2" :use ((:instance fn-ocf-step-potential (item (car items)))))))

; KEYSTONE.  The subject is the host's scheduling surface: fn-otm-next
; (host/native/owner.lisp fnn-owner-gate-pick), fn-otm-commit-event
; (fnn-owner-commit-event) and, through fn-ocf-okp's START-NEXT clause,
; fn-otm-committer-wake (fnn-owner-commit-wake, and its recheck inside the
; START-NEXT quantum).  From ANY scheduler value, while a control request
; waits at every pick and the committer's quanta take the host's shapes,
; before that request is admitted (or the owner stops): at most TEN quanta
; that are not :inspect, not an in-flight :reader and not an empty
; START-NEXT, and at most TWO batches sealed.
(defthm fn-ocf-control-waits-at-most-the-bound
  (implies (fn-ocf-okp s items)
           (and (<= (fn-ocf-delay s items) 10)
                (<= (fn-ocf-seals s items) 2)))
  :hints (("Goal" :in-theory (disable fn-ocf-delay fn-ocf-seals fn-ocf-okp fn-ocf-potential
                                      fn-ocf-seal-potential))))

(in-theory (disable fn-ocf-events fn-ocf-step fn-ocf-delay fn-ocf-seals fn-ocf-okp
                    fn-ocf-potential fn-ocf-seal-potential fn-ocf-m fn-ocf-due fn-ocf-b))
