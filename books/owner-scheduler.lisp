; fn: the owner's scheduler -- which service class runs next (wave 5, lane
; owner-scheduler, 2026-09-26; ember's priority 2 "a better mutation scheme";
; gpt-6's consolidation review section 7; HST-023; PRF-248).
;
; One semantic owner does not require one enormous critical section.  The
; native owner (host/native/owner.lisp) keeps ONE mutation owner: every
; bounded semantic step runs under the service mutex.  What this book owns is
; the decision the host used to leave to the Lisp runtime's mutex: WHICH
; waiting thread runs the next step.  Under a bare mutex the thread that
; just released it re-acquires it before a thread that has waited for
; seconds (barging), so under three tight-loop readers the control socket's
; requests waited past their 10 s deadline (PKT-321, the mixed hour of
; qual-b6759850, qual-dfa810fc and qual-69046a76).
;
; The host observes how many threads of each SERVICE CLASS wait
; (WAITING: four naturals, control reader poster transit, in the order of
; *fn-osch-order*) and asks `fn-osch-next' which class runs the next
; quantum.  The answer is a deterministic function of the class cursor and
; those counts: the first waiting class in cyclic order from the cursor, and
; the cursor moves to the slot after it.  Within a class the host serves in
; arrival order (its own FIFO tickets: a host observation of arrival, never a
; decision about a request's content).
;
;   fn-osch-next        (s waiting) -> (mv class-or-nil s')    the pick
;   fn-osch-observe     (s class hold-ms wait-ms) -> s'        the hold and wait fold
;   fn-osch-health-lines (s) -> octets                          the lines `health' prints
;
; The keystone `fn-osch-control-waits-at-most-the-bound': while the control
; class has a waiter at every pick, at most *fn-osch-bound* = 3 quanta of
; other classes run before a control quantum, from ANY cursor.  A quantum is
; one bounded semantic step (a served read with its drain, one control
; request, one transit step); the bound is in quanta, and the wall time a
; control request waits is at most B times the longest quantum plus its own.
; The same cyclic scan gives every class the same bound (the argument is
; symmetric in the slot); the theorem is stated for the class the packet is
; about.
;
; What this book does not decide: the class of a request (the host knows
; which socket it arrived on: the control socket, a reader connection, a
; peer connection, a poster's submission), the length of a quantum (the
; step's own work: bounded per step by the books that define it), or
; anything the step itself answers.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; The classes and the cyclic order.  Control (and maintenance) is slot 0.

(defconst *fn-osch-order* '(:control :reader :poster :transit))
(defconst *fn-osch-slots* 4)
(defconst *fn-osch-bound* 3)

(defun fn-osch-classp (x)
  (declare (xargs :guard t))
  (and (member-eq x *fn-osch-order*) t))

(defun fn-osch-class-index (c)
  (declare (xargs :guard t))
  (cond ((eq c :reader) 1) ((eq c :poster) 2) ((eq c :transit) 3) (t 0)))

(defun fn-osch-index-class (i)
  (declare (xargs :guard t))
  (cond ((eql i 1) :reader) ((eql i 2) :poster) ((eql i 3) :transit) (t :control)))

; A guard-free NTH over any object.
(defun fn-osch-nth (i x)
  (declare (xargs :guard t :measure (nfix i)))
  (if (not (posp i))
      (if (consp x) (car x) nil)
    (fn-osch-nth (- i 1) (if (consp x) (cdr x) nil))))

(defun fn-osch-update-nth (i v x)
  (declare (xargs :guard t :measure (nfix i)))
  (if (not (posp i))
      (cons v (if (consp x) (cdr x) nil))
    (cons (if (consp x) (car x) nil)
          (fn-osch-update-nth (- i 1) v (if (consp x) (cdr x) nil)))))

; WAITING: the threads of slot I waiting for the owner.
(defun fn-osch-waits (i w)
  (declare (xargs :guard t))
  (nfix (fn-osch-nth i w)))

(defun fn-osch-idlep (w)
  (declare (xargs :guard t))
  (and (zp (fn-osch-waits 0 w)) (zp (fn-osch-waits 1 w))
       (zp (fn-osch-waits 2 w)) (zp (fn-osch-waits 3 w))))

; The cursor is a slot; anything else reads as slot 0.
(defun fn-osch-norm (c)
  (declare (xargs :guard t))
  (if (and (natp c) (< c *fn-osch-slots*)) c 0))

(defun fn-osch-succ (i)
  (declare (xargs :guard t))
  (let ((j (+ 1 (fn-osch-norm i))))
    (if (< j *fn-osch-slots*) j 0)))

; Scan K slots cyclically from I: the first slot with a waiter, or nil.
(defun fn-osch-scan (i k w)
  (declare (xargs :guard t :measure (nfix k)))
  (if (not (posp k))
      nil
    (let ((i (fn-osch-norm i)))
      (if (posp (fn-osch-waits i w))
          i
        (fn-osch-scan (fn-osch-succ i) (- k 1) w)))))

; The pick: the first waiting slot from the cursor, over one whole cycle.
(defun fn-osch-pick (cursor w)
  (declare (xargs :guard t))
  (fn-osch-scan (fn-osch-norm cursor) *fn-osch-slots* w))

; -----------------------------------------------------------------------------
; The state: (CURSOR ROWS), ROWS one row per slot.
; A row: (holds hold<1ms hold<10ms hold<100ms hold<1s hold>=1s hold-max-ms
;         wait-max-ms waits>=1s).

(defun fn-osch-row0 ()
  (declare (xargs :guard t))
  (list 0 0 0 0 0 0 0 0 0))

(defun fn-osch-init ()
  (declare (xargs :guard t))
  (list 0 (list (fn-osch-row0) (fn-osch-row0) (fn-osch-row0) (fn-osch-row0))))

(defun fn-osch-cursor (s)
  (declare (xargs :guard t))
  (fn-osch-norm (fn-osch-nth 0 s)))

(defun fn-osch-rows (s)
  (declare (xargs :guard t))
  (fn-osch-nth 1 s))

(defun fn-osch-row (i s)
  (declare (xargs :guard t))
  (fn-osch-nth i (fn-osch-rows s)))

(defun fn-osch-field (j row)
  (declare (xargs :guard t))
  (nfix (fn-osch-nth j row)))

(defun fn-osch-holds (i s)
  (declare (xargs :guard t))
  (fn-osch-field 0 (fn-osch-row i s)))

; Which of the five hold buckets MS falls in.
(defun fn-osch-bucket (ms)
  (declare (xargs :guard t))
  (let ((ms (nfix ms)))
    (cond ((< ms 1) 1) ((< ms 10) 2) ((< ms 100) 3) ((< ms 1000) 4) (t 5))))

(defun fn-osch-bump (j row)
  (declare (xargs :guard t))
  (fn-osch-update-nth j (+ 1 (fn-osch-field j row)) row))

(defun fn-osch-row-observe (row hold-ms wait-ms)
  (declare (xargs :guard t))
  (let* ((row (fn-osch-bump 0 row))
         (row (fn-osch-bump (fn-osch-bucket hold-ms) row))
         (row (fn-osch-update-nth 6 (max (nfix hold-ms) (fn-osch-field 6 row)) row))
         (row (fn-osch-update-nth 7 (max (nfix wait-ms) (fn-osch-field 7 row)) row)))
    (if (<= 1000 (nfix wait-ms)) (fn-osch-bump 8 row) row)))

; The fold the host runs when a step leaves the mutex: CLASS held it HOLD-MS
; and waited WAIT-MS at the gate before it.  Decides nothing.
(defun fn-osch-observe (s class hold-ms wait-ms)
  (declare (xargs :guard t))
  (let ((i (fn-osch-class-index class)))
    (list (fn-osch-cursor s)
          (fn-osch-update-nth i (fn-osch-row-observe (fn-osch-row i s) hold-ms wait-ms)
                              (fn-osch-rows s)))))

; The pick, with the cursor moved past the slot it picked.  The rows are kept.
(defun fn-osch-next (s w)
  (declare (xargs :guard t))
  (let ((j (fn-osch-pick (fn-osch-cursor s) w)))
    (if j
        (mv (fn-osch-index-class j) (list (fn-osch-succ j) (fn-osch-rows s)))
      (mv nil s))))

; -----------------------------------------------------------------------------
; The lines `health' prints (host/native-live-status-host.lisp appends them
; after the exposure lines; the exit code is the verdict's,
; fn-nh-report-exit-of-render-and-more).

; Guard-free: a non-character renders as `?', so the health line can never
; be the reason a report is refused.
(defun fn-osch-chars-octets (chars)
  (declare (xargs :guard t))
  (if (consp chars)
      (cons (if (characterp (car chars)) (char-code (car chars)) 63)
            (fn-osch-chars-octets (cdr chars)))
    nil))

(defun fn-osch-text (s)
  (declare (xargs :guard (stringp s)))
  (fn-osch-chars-octets (coerce s 'list)))

(defun fn-osch-decimal (n)
  (declare (xargs :guard t))
  (fn-osch-chars-octets (explode-nonnegative-integer (nfix n) 10 nil)))

(defun fn-osch-kv (name n)
  (declare (xargs :guard (stringp name)))
  (append (fn-osch-text " ") (fn-osch-text name) (fn-osch-text "=") (fn-osch-decimal n)))

(defun fn-osch-class-name (i)
  (declare (xargs :guard t))
  (cond ((eql i 1) "reader") ((eql i 2) "poster") ((eql i 3) "transit") (t "control")))

(defun fn-osch-row-line (i row)
  (declare (xargs :guard t))
  (append (fn-osch-text "sched ")
          (fn-osch-text (fn-osch-class-name i))
          (fn-osch-kv "holds" (fn-osch-field 0 row))
          (fn-osch-kv "hold<1ms" (fn-osch-field 1 row))
          (fn-osch-kv "hold<10ms" (fn-osch-field 2 row))
          (fn-osch-kv "hold<100ms" (fn-osch-field 3 row))
          (fn-osch-kv "hold<1s" (fn-osch-field 4 row))
          (fn-osch-kv "hold>=1s" (fn-osch-field 5 row))
          (fn-osch-kv "hold-max-ms" (fn-osch-field 6 row))
          (fn-osch-kv "wait-max-ms" (fn-osch-field 7 row))
          (fn-osch-kv "waits>=1s" (fn-osch-field 8 row))
          (list 10)))

(defun fn-osch-health-lines (s)
  (declare (xargs :guard t))
  (append (fn-osch-text "sched order=control,reader,poster,transit")
          (fn-osch-kv "bound" *fn-osch-bound*)
          (fn-osch-kv "cursor" (fn-osch-cursor s))
          (list 10)
          (fn-osch-row-line 0 (fn-osch-row 0 s))
          (fn-osch-row-line 1 (fn-osch-row 1 s))
          (fn-osch-row-line 2 (fn-osch-row 2 s))
          (fn-osch-row-line 3 (fn-osch-row 3 s))))

; =============================================================================
; Theorems

; The scan answers a slot with a waiter.
(defthm fn-osch-scan-is-a-slot
  (implies (fn-osch-scan i k w)
           (and (natp (fn-osch-scan i k w))
                (< (fn-osch-scan i k w) *fn-osch-slots*)))
  :rule-classes ((:rewrite) (:linear :corollary
                             (implies (fn-osch-scan i k w)
                                      (and (<= 0 (fn-osch-scan i k w))
                                           (< (fn-osch-scan i k w) *fn-osch-slots*)))))
  :hints (("Goal" :induct (fn-osch-scan i k w)
           :in-theory (disable fn-osch-waits))))

(defthm fn-osch-scan-has-a-waiter
  (implies (fn-osch-scan i k w)
           (posp (fn-osch-waits (fn-osch-scan i k w) w)))
  :hints (("Goal" :induct (fn-osch-scan i k w)
           :in-theory (disable fn-osch-waits))))

; The pick names a slot with a waiter, and it is nil exactly when nobody waits.
(defthm fn-osch-pick-is-a-slot
  (implies (fn-osch-pick c w)
           (and (natp (fn-osch-pick c w)) (< (fn-osch-pick c w) *fn-osch-slots*)))
  :rule-classes ((:rewrite) (:linear :corollary
                             (implies (fn-osch-pick c w)
                                      (and (<= 0 (fn-osch-pick c w))
                                           (< (fn-osch-pick c w) *fn-osch-slots*)))))
  :hints (("Goal" :in-theory (disable fn-osch-scan fn-osch-waits))))

(defthm fn-osch-pick-has-a-waiter
  (implies (fn-osch-pick c w)
           (posp (fn-osch-waits (fn-osch-pick c w) w)))
  :hints (("Goal" :in-theory (disable fn-osch-scan fn-osch-waits))))

(local
 (defthm fn-osch-norm-cases
   (or (equal (fn-osch-norm c) 0) (equal (fn-osch-norm c) 1)
       (equal (fn-osch-norm c) 2) (equal (fn-osch-norm c) 3))
   :rule-classes nil))

(defthm fn-osch-pick-nil-iff-idle
  (iff (fn-osch-pick c w) (not (fn-osch-idlep w)))
  :hints (("Goal" :use fn-osch-norm-cases
           :in-theory (e/d (fn-osch-scan fn-osch-succ) (fn-osch-waits fn-osch-norm)))))

; -----------------------------------------------------------------------------
; KEYSTONE: a control request waits at most *fn-osch-bound* quanta.
;
; WS is the sequence of WAITING observations the host makes at successive
; picks; `fn-osch-control-waitsp' says control has a waiter at each.
; `fn-osch-control-delay' counts the quanta of other classes picked before
; the first control pick (a pick that finds nobody costs nothing: the owner
; is idle).

(defun fn-osch-control-waitsp (ws)
  (declare (xargs :guard t))
  (if (consp ws)
      (and (posp (fn-osch-waits 0 (car ws)))
           (fn-osch-control-waitsp (cdr ws)))
    t))

(defun fn-osch-control-delay (c ws)
  (declare (xargs :guard t))
  (if (consp ws)
      (let ((j (fn-osch-pick c (car ws))))
        (cond ((null j) (fn-osch-control-delay c (cdr ws)))
              ((equal j 0) 0)
              (t (+ 1 (fn-osch-control-delay (fn-osch-succ j) (cdr ws))))))
    0))

; The distance from the cursor to the control slot, going round.
(defun fn-osch-measure (c)
  (declare (xargs :guard t))
  (if (zp (fn-osch-norm c)) 0 (- *fn-osch-slots* (fn-osch-norm c))))

(local
 (defthm fn-osch-pick-from-the-control-slot
   (implies (and (posp (fn-osch-waits 0 w)) (equal (fn-osch-norm c) 0))
            (equal (fn-osch-pick c w) 0))
   :hints (("Goal" :in-theory (e/d (fn-osch-scan fn-osch-succ) (fn-osch-waits fn-osch-norm))))))

(local
 (defthm fn-osch-pick-past-the-control-slot
   (implies (and (posp (fn-osch-waits 0 w)) (not (equal (fn-osch-pick c w) 0)))
            (and (integerp (fn-osch-pick c w))
                 (not (equal (fn-osch-norm c) 0))
                 (<= (fn-osch-norm c) (fn-osch-pick c w))
                 (< (fn-osch-pick c w) *fn-osch-slots*)))
   :rule-classes ((:rewrite) (:linear :corollary
                              (implies (and (posp (fn-osch-waits 0 w))
                                            (not (equal (fn-osch-pick c w) 0)))
                                       (and (<= (fn-osch-norm c) (fn-osch-pick c w))
                                            (< (fn-osch-pick c w) *fn-osch-slots*)))))
   :hints (("Goal" :use fn-osch-norm-cases
            :in-theory (e/d (fn-osch-scan fn-osch-succ) (fn-osch-waits fn-osch-norm))))))

(local
 (defthm fn-osch-norm-of-slot
   (implies (and (natp j) (< j *fn-osch-slots*))
            (equal (fn-osch-norm j) j))))

(local
 (defthm fn-osch-measure-of-succ
   (implies (and (integerp j) (<= (fn-osch-norm c) j) (< j *fn-osch-slots*)
                 (not (equal (fn-osch-norm c) 0)))
            (< (fn-osch-measure (fn-osch-succ j)) (fn-osch-measure c)))
   :rule-classes :linear
   :hints (("Goal" :use fn-osch-norm-cases
            :cases ((equal j 1) (equal j 2) (equal j 3))
            :in-theory (e/d (fn-osch-succ) (fn-osch-norm))))))

; The step of the bound's induction, with both variables in its trigger.
(local
 (defthm fn-osch-delay-step
   (implies (and (< 0 (fn-osch-waits 0 w)) (not (equal (fn-osch-pick c w) 0)))
            (< (fn-osch-measure (fn-osch-succ (fn-osch-pick c w))) (fn-osch-measure c)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable fn-osch-pick fn-osch-measure fn-osch-succ fn-osch-norm
                                       fn-osch-waits fn-osch-measure-of-succ
                                       fn-osch-pick-past-the-control-slot)
            :use ((:instance fn-osch-pick-past-the-control-slot)
                  (:instance fn-osch-measure-of-succ (j (fn-osch-pick c w))))))))

(local
 (defthm fn-osch-measure-natp
   (natp (fn-osch-measure c))
   :rule-classes :type-prescription))

(local
 (defthm fn-osch-control-delay-at-most-the-measure
   (implies (fn-osch-control-waitsp ws)
            (<= (fn-osch-control-delay c ws) (fn-osch-measure c)))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-osch-control-delay c ws)
            :in-theory (disable fn-osch-pick fn-osch-measure fn-osch-succ fn-osch-norm
                                fn-osch-waits fn-osch-measure-of-succ
                                fn-osch-pick-past-the-control-slot)))))

(local
 (defthm fn-osch-measure-at-most-the-bound
   (<= (fn-osch-measure c) *fn-osch-bound*)
   :rule-classes :linear
   :hints (("Goal" :use fn-osch-norm-cases :in-theory (disable fn-osch-norm)))))

(defthm fn-osch-control-waits-at-most-the-bound
  ; KEYSTONE (PRF-248).  The subject is `fn-osch-next' (its pick is
  ; `fn-osch-pick' of the cursor and the counts), which host/native/owner.lisp
  ; fnn-owner-gate-pick calls at every release of the owner mutex and at
  ; every arrival at an idle owner.  From any cursor, while control has a
  ; waiter at each pick, at most three quanta of the other classes run
  ; before a control quantum.
  (implies (fn-osch-control-waitsp ws)
           (<= (fn-osch-control-delay c ws) *fn-osch-bound*))
  :hints (("Goal" :in-theory (disable fn-osch-control-delay fn-osch-measure
                                      fn-osch-control-waitsp))))

; The pick `fn-osch-next' makes is `fn-osch-pick' of the cursor, and the
; cursor it leaves is the slot after the pick (so the class just served is
; the last one considered next time).
(defthm fn-osch-next-is-the-pick
  (and (equal (mv-nth 0 (fn-osch-next s w))
              (if (fn-osch-pick (fn-osch-cursor s) w)
                  (fn-osch-index-class (fn-osch-pick (fn-osch-cursor s) w))
                nil))
       (equal (fn-osch-cursor (mv-nth 1 (fn-osch-next s w)))
              (if (fn-osch-pick (fn-osch-cursor s) w)
                  (fn-osch-norm (fn-osch-succ (fn-osch-pick (fn-osch-cursor s) w)))
                (fn-osch-cursor s)))
       (equal (fn-osch-rows (mv-nth 1 (fn-osch-next s w))) (fn-osch-rows s)))
  :hints (("Goal" :in-theory (disable fn-osch-pick fn-osch-succ fn-osch-index-class
                                      fn-osch-norm))))

; -----------------------------------------------------------------------------
; The fold: one observation adds one hold to exactly its class, and to
; exactly one bucket, so the buckets of a row always sum to its holds.

(defun fn-osch-row-okp (row)
  (declare (xargs :guard t))
  (equal (+ (fn-osch-field 1 row) (fn-osch-field 2 row) (fn-osch-field 3 row)
            (fn-osch-field 4 row) (fn-osch-field 5 row))
         (fn-osch-field 0 row)))

(local
 (defthm fn-osch-nth-of-update-nth
   (equal (fn-osch-nth i (fn-osch-update-nth j v x))
          (if (equal (nfix i) (nfix j)) v (fn-osch-nth i x)))))

(local
 (defthm fn-osch-bucket-range
   (and (integerp (fn-osch-bucket ms))
        (<= 1 (fn-osch-bucket ms))
        (<= (fn-osch-bucket ms) 5))
   :rule-classes ((:rewrite)
                  (:linear :corollary (and (<= 1 (fn-osch-bucket ms))
                                           (<= (fn-osch-bucket ms) 5)))
                  (:type-prescription :corollary (integerp (fn-osch-bucket ms))))))

; The fold, one layer at a time, with the recursive accessors closed: what a
; field is after one update and after one bump.  (One lemma over the whole
; five-layer fold cost 17 s at two jobs; these two cost nothing.)
(local
 (defthm fn-osch-field-of-update-nth
   (equal (fn-osch-field j (fn-osch-update-nth i v row))
          (if (equal (nfix j) (nfix i)) (nfix v) (fn-osch-field j row)))
   :hints (("Goal" :in-theory (enable fn-osch-field)))))

(local (in-theory (disable fn-osch-field fn-osch-nth fn-osch-update-nth)))

(local
 (defthm fn-osch-field-natp
   (natp (fn-osch-field j row))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-osch-field)))))

(local
 (defthm fn-osch-field-of-bump
   (equal (fn-osch-field j (fn-osch-bump i row))
          (if (equal (nfix j) (nfix i))
              (+ 1 (fn-osch-field i row))
            (fn-osch-field j row)))
   :hints (("Goal" :in-theory (enable fn-osch-bump)))))

(local (in-theory (disable fn-osch-bump)))

(local
 (defthm fn-osch-nth-of-two
   (and (equal (fn-osch-nth 0 (list a b)) a)
        (equal (fn-osch-nth 1 (list a b)) b))
   :hints (("Goal" :in-theory (enable fn-osch-nth)))))

(local
 (defthm fn-osch-nth-when-not-natp
   (implies (not (natp i))
            (equal (fn-osch-nth i x) (fn-osch-nth 0 x)))
   :hints (("Goal" :in-theory (enable fn-osch-nth)))))

(defthm fn-osch-observe-holds
  (equal (fn-osch-holds i (fn-osch-observe s class hold-ms wait-ms))
         (if (equal (nfix i) (fn-osch-class-index class))
             (+ 1 (fn-osch-holds i s))
           (fn-osch-holds i s)))
  :hints (("Goal" :in-theory (e/d (fn-osch-observe fn-osch-holds fn-osch-row fn-osch-rows
                                   fn-osch-cursor fn-osch-row-observe)
                                  (fn-osch-bucket fn-osch-norm)))))

(defthm fn-osch-row-observe-keeps-okp
  (implies (fn-osch-row-okp row)
           (fn-osch-row-okp (fn-osch-row-observe row hold-ms wait-ms)))
  :hints (("Goal" :in-theory (e/d (fn-osch-row-okp fn-osch-row-observe) (fn-osch-bucket))
           :cases ((equal (fn-osch-bucket hold-ms) 1) (equal (fn-osch-bucket hold-ms) 2)
                   (equal (fn-osch-bucket hold-ms) 3) (equal (fn-osch-bucket hold-ms) 4)
                   (equal (fn-osch-bucket hold-ms) 5)))))

(local
 (defthm fn-osch-norm-idempotent
   (equal (fn-osch-norm (fn-osch-norm c)) (fn-osch-norm c))))

(defthm fn-osch-observe-keeps-cursor
  (equal (fn-osch-cursor (fn-osch-observe s class hold-ms wait-ms))
         (fn-osch-cursor s))
  :hints (("Goal" :in-theory (e/d (fn-osch-observe fn-osch-cursor)
                                  (fn-osch-norm fn-osch-row-observe fn-osch-class-index)))))

(in-theory (disable fn-osch-pick fn-osch-next fn-osch-observe fn-osch-health-lines))
