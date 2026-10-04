; fn: the retention bound on the arena readers' generation pins, and the
; ousted laggard (lane reclaim-design, 2026-10-04; PRF-1312; the packet
; planning/design/reclaim-2026-10-04.md section 5).
;
; books/arena-reader-pins.lisp (PRF-941) releases a retirement only when no
; live pin is at or below its stamp.  Nothing there bounds how far a pin may
; lag.  One reader that never ends -- a connection whose OVER response is
; never drained, a publication thread stuck in I/O -- keeps every retirement
; stamped at or after its generation pending for ever: the reseated staged
; pages of every COMPLETE since, every dropped segment's descriptor, every
; forgotten handle's entry.  Unbounded memory and disk held by one laggard,
; and a reclaim pass that can never return what it reclaimed.  LMDB has the
; same shape (the oldest reader's transaction bounds the free list);
; libmdbx answers it by OUSTING the laggard (its handle-slow-readers hook: a
; reader more than a bound behind is kicked and its next access refused).
;
; This book is that bound, as a wrapper machine over fn-arpn-step.  The
; state gains OUSTED, the ousted readers' generations:
;
;   (:oust B)   every pin more than B generations behind CUR (G < CUR - B)
;               leaves the live table for OUSTED; the answer is those rows.
;               The next :release then answers what those pins covered.
;   (:held G)   t for a live pin, :ousted for an ousted one, nil otherwise:
;               a reader asks it before each quantum; an ousted reader is
;               refused BY NAME, never served a released handle.
;   (:unpin G)  :ok for a live pin (fn-arpn-step's), :ousted once for an
;               ousted one (so the host's accounting of the thread still
;               balances), :refused otherwise.
;   any other   fn-arpn-step over (CUR PINS PEND); OUSTED unchanged.
;
; The retention bound.  After (:oust B) every live pin is at or above
; CUR - B (fn-arpb-oust-leaves-no-pin-below-the-bound), so after the next
; :release every retirement still pending has a stamp at or above CUR - B
; (KEYSTONE fn-arpb-pending-after-oust-is-within-the-bound): what is held
; back is at most what the last B generations retired, whoever is stuck.
;
; A pinned generation is never released.  A reader within the bound keeps
; its pin exactly (fn-arpb-oust-keeps-every-pin-within-the-bound), and
; every retirement it is pinned at or below stays pending through the oust
; and the release (KEYSTONE fn-arpb-release-after-oust-keeps-every-covered-
; retirement).  The ousted laggard is refused: (:held G) and (:unpin G)
; answer :ousted, never t or :ok (fn-arpb-ousted-reader-is-refused), and a
; reader within the bound is held (fn-arpb-reader-within-the-bound-is-held).
; Off :oust, :held and an ousted :unpin the machine IS fn-arpn-step over
; its first three slots (fn-arpb-step-is-the-pins-step), so every PRF-941
; keystone holds of it unchanged.
;
; What this book does NOT decide: B itself (a profile parameter, D27: a
; bound on how long one reader may hold back release, never on stored
; data) and the host's response to :ousted (a publication restarts at a
; fresh pin; a response in flight answers its client by name).  The host
; calls fn-arpb-step where it calls fn-arpn-step today (host/native/io.lisp
; fnn-arena-pins-step); that wiring is the RECLAIM lane's (arena-* area).

(in-package "ACL2")
(include-book "arena-reader-pins")

; ---------------------------------------------------------------- ousted

; Rows (G . N): N readers ousted at generation G, in no particular order
; (a generation is ousted at most once, but nothing here needs that).
(defun fn-arpb-tablep (tab)
  (declare (xargs :guard t))
  (if (atom tab)
      (null tab)
    (and (consp (car tab))
         (natp (caar tab))
         (posp (cdar tab))
         (fn-arpb-tablep (cdr tab)))))

(defun fn-arpb-ousted-of-loop (g tab acc)
  (declare (xargs :guard (and (fn-arpb-tablep tab) (acl2-numberp acc))))
  (cond ((atom tab) acc)
        ((equal (caar tab) g) (fn-arpb-ousted-of-loop g (cdr tab) (+ acc (cdar tab))))
        (t (fn-arpb-ousted-of-loop g (cdr tab) acc))))

; The readers ousted at G.
(defun fn-arpb-ousted-of (g tab)
  (declare (xargs :guard (fn-arpb-tablep tab) :verify-guards nil))
  (mbe :logic (cond ((atom tab) 0)
                    ((equal (caar tab) g) (+ (cdar tab) (fn-arpb-ousted-of g (cdr tab))))
                    (t (fn-arpb-ousted-of g (cdr tab))))
       :exec (fn-arpb-ousted-of-loop g tab 0)))

(defthm fn-arpb-ousted-of-loop-is-ousted-of
  (implies (acl2-numberp acc)
           (equal (fn-arpb-ousted-of-loop g tab acc)
                  (+ acc (fn-arpb-ousted-of g tab)))))

(verify-guards fn-arpb-ousted-of)

(defun fn-arpb-ousted-drop-loop (g tab rev)
  (declare (xargs :guard (and (fn-arpb-tablep tab) (true-listp rev))))
  (cond ((atom tab) (revappend rev tab))
        ((equal (caar tab) g)
         (if (< 1 (cdar tab))
             (revappend rev (cons (cons g (- (cdar tab) 1)) (cdr tab)))
           (revappend rev (cdr tab))))
        (t (fn-arpb-ousted-drop-loop g (cdr tab) (cons (car tab) rev)))))

; One reader fewer ousted at G (its first row dropped at zero).
(defun fn-arpb-ousted-drop (g tab)
  (declare (xargs :guard (fn-arpb-tablep tab) :verify-guards nil))
  (mbe :logic (cond ((atom tab) tab)
                    ((equal (caar tab) g)
                     (if (< 1 (cdar tab))
                         (cons (cons g (- (cdar tab) 1)) (cdr tab))
                       (cdr tab)))
                    (t (cons (car tab) (fn-arpb-ousted-drop g (cdr tab)))))
       :exec (fn-arpb-ousted-drop-loop g tab nil)))

(defthm fn-arpb-ousted-drop-loop-is-ousted-drop
  (equal (fn-arpb-ousted-drop-loop g tab rev)
         (revappend rev (fn-arpb-ousted-drop g tab))))

(verify-guards fn-arpb-ousted-drop)

; ---------------------------------------------------------------- the cut

; The live pins below FLOOR -- a prefix, PINS ascending -- and the rest.
(defun fn-arpb-below-loop (floor pins rev)
  (declare (xargs :guard (and (natp floor) (fn-arpn-pinsp pins) (true-listp rev))))
  (if (and (consp pins) (< (caar pins) floor))
      (fn-arpb-below-loop floor (cdr pins) (cons (car pins) rev))
    (revappend rev nil)))

(defun fn-arpb-below (floor pins)
  (declare (xargs :guard (and (natp floor) (fn-arpn-pinsp pins)) :verify-guards nil))
  (mbe :logic (if (and (consp pins) (< (caar pins) floor))
                  (cons (car pins) (fn-arpb-below floor (cdr pins)))
                nil)
       :exec (fn-arpb-below-loop floor pins nil)))

(defthm fn-arpb-below-loop-is-below
  (implies (true-listp rev)
           (equal (fn-arpb-below-loop floor pins rev)
                  (revappend rev (fn-arpb-below floor pins)))))

(verify-guards fn-arpb-below)

(defun fn-arpb-from (floor pins)
  (declare (xargs :guard (and (natp floor) (fn-arpn-pinsp pins))))
  (if (and (consp pins) (< (caar pins) floor))
      (fn-arpb-from floor (cdr pins))
    pins))

; The bound's floor: the oldest generation a pin may still hold.
(defun fn-arpb-floor (cur b)
  (declare (xargs :guard (and (natp cur) (natp b))))
  (nfix (- cur b)))

; ---------------------------------------------------------------- the state

; ST = (CUR PINS PEND OUSTED): fn-arpn's state and the ousted table.
(defun fn-arpb-core (st)
  (declare (xargs :guard (true-listp st)))
  (list (first st) (second st) (third st)))

(defun fn-arpb-okp (st)
  (declare (xargs :guard t))
  (and (true-listp st)
       (equal (len st) 4)
       (fn-arpn-okp (fn-arpb-core st))
       (fn-arpb-tablep (fourth st))))

(defun fn-arpb-initial ()
  (declare (xargs :guard t))
  (list 0 nil nil nil))

(defun fn-arpb-step (st ev)
  (declare (xargs :guard (fn-arpb-okp st)))
  (let ((cur (first st)) (pins (second st)) (pend (third st)) (ousted (fourth st)))
    (case (and (consp ev) (car ev))
      (:oust (let ((b (and (consp (cdr ev)) (cadr ev))))
               (if (natp b)
                   (let ((floor (fn-arpb-floor cur b)))
                     (mv (list cur (fn-arpb-from floor pins) pend
                               (append (fn-arpb-below floor pins) ousted))
                         (fn-arpb-below floor pins)))
                 (mv st :refused))))
      (:held (let ((g (and (consp (cdr ev)) (cadr ev))))
               (cond ((not (natp g)) (mv st :refused))
                     ((fn-arpn-held-p g pins) (mv st t))
                     ((< 0 (fn-arpb-ousted-of g ousted)) (mv st :ousted))
                     (t (mv st nil)))))
      (:unpin (let ((g (and (consp (cdr ev)) (cadr ev))))
                (cond ((and (natp g) (fn-arpn-held-p g pins))
                       (mv-let (core ans) (fn-arpn-step (list cur pins pend) ev)
                         (mv (list (first core) (second core) (third core) ousted) ans)))
                      ((and (natp g) (< 0 (fn-arpb-ousted-of g ousted)))
                       (mv (list cur pins pend (fn-arpb-ousted-drop g ousted)) :ousted))
                      (t (mv st :refused)))))
      (otherwise
       (mv-let (core ans) (fn-arpn-step (list cur pins pend) ev)
         (mv (list (first core) (second core) (third core) ousted) ans))))))

; ---------------------------------------------------------------- lemmas

(local
 (defthm fn-arpb-tablep-true-listp
   (implies (fn-arpb-tablep tab) (true-listp tab))
   :rule-classes :forward-chaining))

(local
 (defthm fn-arpn-pinsp-true-listp
   (implies (fn-arpn-pinsp pins) (true-listp pins))
   :rule-classes :forward-chaining))

(local
 (defthm fn-arpb-ousted-of-natp
   (implies (fn-arpb-tablep tab)
            (natp (fn-arpb-ousted-of g tab)))
   :rule-classes :type-prescription))

(local
 (defthm fn-arpb-ousted-of-append
   (equal (fn-arpb-ousted-of g (append a b))
          (+ (fn-arpb-ousted-of g a) (fn-arpb-ousted-of g b)))))

(local
 (defthm fn-arpb-tablep-append
   (implies (and (fn-arpb-tablep a) (fn-arpb-tablep b))
            (fn-arpb-tablep (append a b)))))

(local
 (defthm fn-arpb-tablep-ousted-drop
   (implies (fn-arpb-tablep tab)
            (fn-arpb-tablep (fn-arpb-ousted-drop g tab)))))

; A pins table's prefix below FLOOR is a pins table, and a table.
(local
 (defthm fn-arpb-below-car
   (implies (consp (fn-arpb-below floor pins))
            (equal (car (fn-arpb-below floor pins)) (car pins)))))

(local
 (defthm fn-arpb-below-pinsp
   (implies (fn-arpn-pinsp pins)
            (fn-arpn-pinsp (fn-arpb-below floor pins)))))

(local
 (defthm fn-arpn-pinsp-is-tablep
   (implies (fn-arpn-pinsp pins)
            (fn-arpb-tablep pins))))

; ... and its suffix from FLOOR is a pins table at most CUR.
(local
 (defthm fn-arpb-from-pinsp
   (implies (fn-arpn-pinsp pins)
            (fn-arpn-pinsp (fn-arpb-from floor pins)))))

(local
 (defthm fn-arpb-from-at-most
   (implies (fn-arpn-at-most-p pins cur)
            (fn-arpn-at-most-p (fn-arpb-from floor pins) cur))))

; In a pins table every key past the first is above it, so a G below the
; first key is ousted nowhere and a G at the first key only there.
(local
 (defthm fn-arpb-ousted-of-above-the-first
   (implies (and (fn-arpn-pinsp pins) (consp pins) (< g (caar pins)))
            (equal (fn-arpb-ousted-of g pins) 0))))

(local
 (defthm fn-arpb-ousted-of-a-pins-table
   (implies (fn-arpn-pinsp pins)
            (equal (fn-arpb-ousted-of g pins) (fn-arpn-pins-of g pins)))))

; Every live pin is at or above the first row.
(local
 (defthm fn-arpn-oldest-at-most-every-pin
   (implies (and (fn-arpn-pinsp pins)
                 (consp pins)
                 (< 0 (fn-arpn-pins-of h pins)))
            (<= (caar pins) h))))

; The readers at H after the cut: none below the floor, all at or above it.
(local
 (defthm fn-arpn-pins-of-from
   (implies (fn-arpn-pinsp pins)
            (equal (fn-arpn-pins-of h (fn-arpb-from floor pins))
                   (if (< h floor) 0 (fn-arpn-pins-of h pins))))))

(local
 (defthm fn-arpn-pins-of-below
   (implies (fn-arpn-pinsp pins)
            (equal (fn-arpn-pins-of h (fn-arpb-below floor pins))
                   (if (< h floor) (fn-arpn-pins-of h pins) 0)))))

(local
 (defthm fn-arpn-pins-of-natp
   (implies (fn-arpn-pinsp pins)
            (natp (fn-arpn-pins-of h pins)))
   :rule-classes :type-prescription))

; A three-slot state is the list of its slots.
(local
 (defthm fn-arpn-okp-state-is-its-slots
   (implies (fn-arpn-okp c)
            (equal (list (car c) (cadr c) (caddr c)) c))
   :hints (("Goal" :expand ((len c) (len (cdr c)) (len (cddr c)) (len (cdddr c)))))))

(local
 (defthm fn-arpb-okp-core
   (implies (fn-arpb-okp st)
            (and (fn-arpn-okp (list (car st) (cadr st) (caddr st)))
                 (fn-arpb-tablep (cadddr st))))))

(local
 (defthm fn-arpb-member-revappend
   (iff (member-equal e (revappend a b))
        (or (member-equal e a) (member-equal e b)))
   :hints (("Goal" :induct (revappend a b)))))

; A retirement the split keeps has a live pin at or below its stamp.
(local
 (defthm fn-arpn-split-acc-kept-is-unclear
   (implies (member-equal e (mv-nth 1 (fn-arpn-split-acc pend pins rel keep)))
            (or (member-equal e keep)
                (and (member-equal e pend)
                     (not (fn-arpn-clear-through-p (car e) pins)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-arpn-split-acc pend pins rel keep)
                   :in-theory (disable fn-arpn-clear-through-p)))))

(local
 (defthm fn-arpn-split-kept-is-unclear
   (implies (member-equal e (mv-nth 1 (fn-arpn-split pend pins)))
            (and (member-equal e pend)
                 (not (fn-arpn-clear-through-p (car e) pins))))
   :hints (("Goal" :use (:instance fn-arpn-split-acc-kept-is-unclear
                                   (rel nil) (keep nil))
                   :in-theory (disable fn-arpn-clear-through-p)))))

(local (in-theory (disable fn-arpn-okp fn-arpn-step fn-arpn-split
                           fn-arpn-clear-through-p fn-arpn-pins-of)))

; ---------------------------------------------------------------- theorems

(defthm fn-arpb-initial-okp
  (fn-arpb-okp (fn-arpb-initial)))

(defthm fn-arpb-step-preserves-okp
  (implies (fn-arpb-okp st)
           (fn-arpb-okp (mv-nth 0 (fn-arpb-step st ev))))
  :hints (("Goal" :in-theory (enable fn-arpn-okp)
                  :use ((:instance fn-arpn-okp-state-is-its-slots
                                   (c (mv-nth 0 (fn-arpn-step (list (car st) (cadr st) (caddr st)) ev))))
                        (:instance fn-arpn-step-preserves-okp
                                   (st (list (car st) (cadr st) (caddr st))))))))

; Off :oust, :held and an ousted :unpin, the machine is fn-arpn-step over
; its first three slots, the ousted table untouched: every keystone of
; books/arena-reader-pins.lisp holds of it unchanged.
(defthm fn-arpb-step-is-the-pins-step
  (implies (and (fn-arpb-okp st)
                (or (not (member-eq (and (consp ev) (car ev)) '(:oust :held :unpin)))
                    (and (consp ev) (eq (car ev) :unpin)
                         (consp (cdr ev)) (natp (cadr ev))
                         (fn-arpn-held-p (cadr ev) (second st)))))
           (let ((r (fn-arpb-step st ev))
                 (p (fn-arpn-step (fn-arpb-core st) ev)))
             (and (equal (fn-arpb-core (mv-nth 0 r)) (mv-nth 0 p))
                  (equal (fourth (mv-nth 0 r)) (fourth st))
                  (equal (mv-nth 1 r) (mv-nth 1 p)))))
  :hints (("Goal" :in-theory (enable fn-arpn-okp)
                  :use ((:instance fn-arpn-okp-state-is-its-slots
                                   (c (mv-nth 0 (fn-arpn-step (list (car st) (cadr st) (caddr st)) ev))))
                        (:instance fn-arpn-step-preserves-okp
                                   (st (list (car st) (cadr st) (caddr st))))))))

; After (:oust B) every live pin is at or above CUR - B.
(defthm fn-arpb-oust-leaves-no-pin-below-the-bound
  (implies (and (fn-arpb-okp st)
                (natp b)
                (< 0 (fn-arpn-pins-of h (second (mv-nth 0 (fn-arpb-step st (list :oust b)))))))
           (<= (fn-arpb-floor (first st) b) h))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arpn-okp))))

; ... and a pin within the bound is exactly what it was.
(defthm fn-arpb-oust-keeps-every-pin-within-the-bound
  (implies (and (fn-arpb-okp st)
                (natp b)
                (<= (fn-arpb-floor (first st) b) h))
           (equal (fn-arpn-pins-of h (second (mv-nth 0 (fn-arpb-step st (list :oust b)))))
                  (fn-arpn-pins-of h (second st))))
  :hints (("Goal" :in-theory (enable fn-arpn-okp))))

; An oust leaves the pending retirements and the generation as they were.
(defthm fn-arpb-oust-keeps-the-rest
  (implies (and (fn-arpb-okp st) (natp b))
           (let ((r (mv-nth 0 (fn-arpb-step st (list :oust b)))))
             (and (equal (first r) (first st))
                  (equal (third r) (third st))))))

;; The oust then the release leaves pending exactly what the pins table's
;; split keeps against the pins at or above the floor.
(defthm fn-arpb-release-after-oust-is-the-split
  (implies (and (fn-arpb-okp st) (natp b))
           (equal (third (mv-nth 0 (fn-arpb-step (mv-nth 0 (fn-arpb-step st (list :oust b)))
                                                 '(:release))))
                  (mv-nth 1 (fn-arpn-split (third st)
                                           (fn-arpb-from (fn-arpb-floor (first st) b) (second st))))))
  :hints (("Goal" :in-theory (enable fn-arpn-step fn-arpn-okp))))

; KEYSTONE (PRF-1312).  The retention bound: after (:oust B) and the next
; :release, every retirement still pending has a stamp at or above CUR - B.
; What is held back is at most what the last B generations retired,
; whoever is stuck.
(defthm fn-arpb-pending-after-oust-is-within-the-bound
  (implies (and (fn-arpb-okp st)
                (natp b)
                (member-equal e (third (mv-nth 0 (fn-arpb-step
                                                  (mv-nth 0 (fn-arpb-step st (list :oust b)))
                                                  '(:release))))))
           (<= (fn-arpb-floor (first st) b) (car e)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-arpn-okp)
                                  (fn-arpb-step fn-arpb-from fn-arpb-floor
                                   fn-arpn-split-kept-is-unclear))
                  :use (fn-arpb-release-after-oust-is-the-split
                        (:instance fn-arpn-split-kept-is-unclear
                                   (pend (third st))
                                   (pins (fn-arpb-from (fn-arpb-floor (first st) b) (second st))))
                        (:instance fn-arpn-not-clear-has-a-pin-at-or-below
                                   (s (car e))
                                   (pins (fn-arpb-from (fn-arpb-floor (first st) b) (second st))))
                        (:instance fn-arpn-pins-of-from
                                   (h (caar (fn-arpb-from (fn-arpb-floor (first st) b) (second st))))
                                   (floor (fn-arpb-floor (first st) b))
                                   (pins (second st)))))))

; KEYSTONE (PRF-1312).  A pinned generation is never released: a reader
; within the bound keeps its pin through the oust, and every retirement it
; is pinned at or below is still pending after the oust and the release.
(defthm fn-arpb-release-after-oust-keeps-every-covered-retirement
  (implies (and (fn-arpb-okp st)
                (natp b)
                (member-equal e (third st))
                (< 0 (fn-arpn-pins-of h (second st)))
                (<= (fn-arpb-floor (first st) b) h)
                (<= h (car e)))
           (member-equal e (third (mv-nth 0 (fn-arpb-step
                                             (mv-nth 0 (fn-arpb-step st (list :oust b)))
                                             '(:release))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arpn-okp)
                  :do-not-induct t
                  :use ((:instance fn-arpn-release-keeps-every-covered-retirement
                                   (st (list (first st)
                                             (fn-arpb-from (fn-arpb-floor (first st) b) (second st))
                                             (third st))))))))

; The ousted laggard is refused by name: after (:oust B) a reader pinned
; below CUR - B is answered :ousted by :held and by :unpin, never t or :ok.
(defthm fn-arpb-ousted-reader-is-refused
  (implies (and (fn-arpb-okp st)
                (natp b)
                (natp g)
                (< 0 (fn-arpn-pins-of g (second st)))
                (< g (fn-arpb-floor (first st) b)))
           (let ((st1 (mv-nth 0 (fn-arpb-step st (list :oust b)))))
             (and (equal (mv-nth 1 (fn-arpb-step st1 (list :held g))) :ousted)
                  (equal (mv-nth 1 (fn-arpb-step st1 (list :unpin g))) :ousted))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arpn-okp))))

; ... and a reader within the bound is held.
(defthm fn-arpb-reader-within-the-bound-is-held
  (implies (and (fn-arpb-okp st)
                (natp b)
                (natp g)
                (< 0 (fn-arpn-pins-of g (second st)))
                (<= (fn-arpb-floor (first st) b) g))
           (equal (mv-nth 1 (fn-arpb-step (mv-nth 0 (fn-arpb-step st (list :oust b)))
                                          (list :held g)))
                  t))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arpn-okp))))
