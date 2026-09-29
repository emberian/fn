; fn: the arena readers' generation pins (lane composed-owner-5, 2026-09-29;
; row A6 of build/coordinator/COMPLETE-BEFORE-6.6.0.md, PRF-941).
;
; A thread that reads the live arena OUTSIDE the owner's mutex (a
; checkpoint publication, host/native/owner.lisp fnn-owner-publish-captured;
; the installing reclaim pass, fnn-owner-reclaim-pass) may hold a handle, or
; a file, that a COMPLETE's reseat or a reclaim's retirement takes away while
; it runs.  What is taken away is therefore released only once every such
; reader that could have seen it has finished.  This book decides that, by
; GENERATION (epoch-based reclamation):
;
;   - the state carries the current generation CUR, the live pins (a table of
;     (G . N): N readers pinned at generation G, strictly ascending in G,
;     every G <= CUR) and the pending retirements ((S . ITEMS): ITEMS taken
;     away at stamp S);
;   - a reader PINS the current generation when it starts (under the owner
;     mutex, before its thread runs) and UNPINS it when it ends;
;   - a retirement is STAMPED with the current generation and the generation
;     advances, so every reader live at the retirement pinned at or below the
;     stamp and every reader that starts after it pins above it;
;   - a pending retirement is RELEASED when no live pin is at or below its
;     stamp (fn-arpn-clear-through-p, one comparison with the oldest pin).
;
; KEYSTONE fn-arpn-release-postdates-every-live-pin: every retirement the
; host's :release answers has a stamp below every live pin -- each reader
; still running started after it.  With fn-arpn-retire-stamp-covers-every-
; live-pin (a retirement's stamp is at or above every live pin) and
; fn-arpn-step-generation-never-decreases, no reader that was live at a
; retirement is live at its release.
;
; The generalization of host/native/io.lisp's *fnn-arena-off-mutex-readers*
; (one count; a staged page waited for NO off-mutex reader at all): an old
; retirement is released as soon as the readers older than it end, whatever
; newer readers run.  The host holds the state in *fnn-arena-pins* under its
; own lock and calls fn-arpn-step for every event (host/native/io.lisp
; fnn-arena-pins-step); the table has one row per distinct live generation,
; so each event is bounded by the live readers, and :release by the pending
; retirements it walks.

(in-package "ACL2")

; ---------------------------------------------------------------- the table

(defun fn-arpn-pinsp (pins)
  (declare (xargs :guard t))
  (if (atom pins)
      (null pins)
    (and (consp (car pins))
         (natp (caar pins))
         (posp (cdar pins))
         (or (atom (cdr pins))
             (and (consp (cadr pins))
                  (natp (caadr pins))
                  (< (caar pins) (caadr pins))))
         (fn-arpn-pinsp (cdr pins)))))

; Every pinned generation is at most CUR.
(defun fn-arpn-at-most-p (pins cur)
  (declare (xargs :guard (and (fn-arpn-pinsp pins) (natp cur))))
  (if (atom pins)
      t
    (and (<= (caar pins) cur)
         (fn-arpn-at-most-p (cdr pins) cur))))

; The readers pinned at H.
(defun fn-arpn-pins-of (h pins)
  (declare (xargs :guard (fn-arpn-pinsp pins)))
  (cond ((atom pins) 0)
        ((equal (caar pins) h) (cdar pins))
        (t (fn-arpn-pins-of h (cdr pins)))))

(defun fn-arpn-held-p (g pins)
  (declare (xargs :guard (fn-arpn-pinsp pins)))
  (< 0 (fn-arpn-pins-of g pins)))

(defun fn-arpn-count (pins)
  (declare (xargs :guard (fn-arpn-pinsp pins)))
  (if (atom pins)
      0
    (+ (cdar pins) (fn-arpn-count (cdr pins)))))

; One more reader at G (G's row incremented, or inserted in order).
(defun fn-arpn-pin-at (g pins)
  (declare (xargs :guard (and (natp g) (fn-arpn-pinsp pins))))
  (cond ((atom pins) (list (cons g 1)))
        ((equal (caar pins) g) (cons (cons g (+ 1 (cdar pins))) (cdr pins)))
        ((< g (caar pins)) (cons (cons g 1) pins))
        (t (cons (car pins) (fn-arpn-pin-at g (cdr pins))))))

; One reader fewer at G (its row dropped at zero); a G nobody pins is left
; as it is (the step refuses it first).
(defun fn-arpn-unpin-at (g pins)
  (declare (xargs :guard (fn-arpn-pinsp pins)))
  (cond ((atom pins) pins)
        ((equal (caar pins) g)
         (if (< 1 (cdar pins))
             (cons (cons g (- (cdar pins) 1)) (cdr pins))
           (cdr pins)))
        (t (cons (car pins) (fn-arpn-unpin-at g (cdr pins))))))

; No reader is pinned at or below S: one comparison with the oldest pin.
(defun fn-arpn-clear-through-p (s pins)
  (declare (xargs :guard (and (natp s) (fn-arpn-pinsp pins))))
  (or (atom pins)
      (< s (caar pins))))

; ---------------------------------------------------------------- pending

(defun fn-arpn-pendp (pend)
  (declare (xargs :guard t))
  (if (atom pend)
      (null pend)
    (and (consp (car pend))
         (natp (caar pend))
         (true-listp (cdar pend))
         (fn-arpn-pendp (cdr pend)))))

; The pending retirements split into those released (every stamp clear)
; and those kept, each in its original order.
(defun fn-arpn-split-acc (pend pins rel keep)
  (declare (xargs :guard (and (fn-arpn-pendp pend) (fn-arpn-pinsp pins)
                              (true-listp rel) (true-listp keep))))
  (cond ((atom pend) (mv (revappend rel nil) (revappend keep nil)))
        ((fn-arpn-clear-through-p (caar pend) pins)
         (fn-arpn-split-acc (cdr pend) pins (cons (car pend) rel) keep))
        (t (fn-arpn-split-acc (cdr pend) pins rel (cons (car pend) keep)))))

(defun fn-arpn-split (pend pins)
  (declare (xargs :guard (and (fn-arpn-pendp pend) (fn-arpn-pinsp pins))))
  (fn-arpn-split-acc pend pins nil nil))

; ---------------------------------------------------------------- the state

; ST = (CUR PINS PEND).
(defun fn-arpn-okp (st)
  (declare (xargs :guard t))
  (and (true-listp st)
       (equal (len st) 3)
       (natp (first st))
       (fn-arpn-pinsp (second st))
       (fn-arpn-at-most-p (second st) (first st))
       (fn-arpn-pendp (third st))))

(defun fn-arpn-initial ()
  (declare (xargs :guard t))
  (list 0 nil nil))

; One event of the host (host/native/io.lisp fnn-arena-pins-step), under its
; lock.  Answers (mv ST' ANSWER):
;   (:pin)              the generation the reader pinned
;   (:unpin G)          :ok, or :refused when no reader is pinned at G
;   (:retire ITEMS)     the stamp S (ITEMS pending at S; the generation
;                       advances)
;   (:stamp)            the stamp S, nothing pending (a retirement the host
;                       releases itself once fn-arpn-clear-through-p S)
;   (:release)          the pending retirements released, ((S . ITEMS) ...)
;   (:clear S)          whether no reader is pinned at or below S
;   (:clear-except S G) the same with one reader pinned at G not counted
;                       (the asking reader's own pin)
;   (:count)            the live readers
; Any other event is :refused and ST unchanged.
(defun fn-arpn-step (st ev)
  (declare (xargs :guard (fn-arpn-okp st)))
  (let ((cur (first st)) (pins (second st)) (pend (third st)))
    (case (and (consp ev) (car ev))
      (:pin (mv (list cur (fn-arpn-pin-at cur pins) pend) cur))
      (:unpin (let ((g (and (consp (cdr ev)) (cadr ev))))
                (if (and (natp g) (fn-arpn-held-p g pins))
                    (mv (list cur (fn-arpn-unpin-at g pins) pend) :ok)
                  (mv st :refused))))
      (:retire (let ((items (and (consp (cdr ev)) (cadr ev))))
                 (if (true-listp items)
                     (mv (list (+ 1 cur) pins (cons (cons cur items) pend)) cur)
                   (mv st :refused))))
      (:stamp (mv (list (+ 1 cur) pins pend) cur))
      (:release (mv-let (rel keep) (fn-arpn-split pend pins)
                  (mv (list cur pins keep) rel)))
      (:clear (let ((s (and (consp (cdr ev)) (cadr ev))))
                (if (natp s)
                    (mv st (fn-arpn-clear-through-p s pins))
                  (mv st :refused))))
      (:clear-except (let ((s (and (consp (cdr ev)) (cadr ev)))
                           (g (and (consp (cdr ev)) (consp (cddr ev)) (caddr ev))))
                       (if (and (natp s) (natp g) (fn-arpn-held-p g pins))
                           (mv st (fn-arpn-clear-through-p s (fn-arpn-unpin-at g pins)))
                         (mv st :refused))))
      (:count (mv st (fn-arpn-count pins)))
      (otherwise (mv st :refused)))))

; ---------------------------------------------------------------- lemmas

(local
 (defthm fn-arpn-pinsp-true-listp
   (implies (fn-arpn-pinsp pins) (true-listp pins))
   :rule-classes :forward-chaining))

(local
 (defthm fn-arpn-pendp-true-listp
   (implies (fn-arpn-pendp pend) (true-listp pend))
   :rule-classes :forward-chaining))

; Every live pin is at or above the oldest row.
(local
 (defthm fn-arpn-oldest-at-most-every-pin
   (implies (and (fn-arpn-pinsp pins)
                 (consp pins)
                 (< 0 (fn-arpn-pins-of h pins)))
            (<= (caar pins) h))))

(local
 (defthm fn-arpn-pins-of-natp
   (implies (fn-arpn-pinsp pins)
            (natp (fn-arpn-pins-of h pins)))
   :rule-classes :type-prescription))

(local
 (defthm fn-arpn-pins-of-at-most
   (implies (and (fn-arpn-at-most-p pins cur)
                 (< 0 (fn-arpn-pins-of h pins)))
            (<= h cur))))

(local
 (defthm fn-arpn-pin-at-first
   (implies (and (fn-arpn-pinsp pins) (natp g))
            (and (consp (fn-arpn-pin-at g pins))
                 (equal (caar (fn-arpn-pin-at g pins))
                        (if (and (consp pins) (< (caar pins) g))
                            (caar pins)
                          g))))))

(defthm fn-arpn-pin-at-pinsp
  (implies (and (fn-arpn-pinsp pins) (natp g))
           (fn-arpn-pinsp (fn-arpn-pin-at g pins))))

(local
 (defthm fn-arpn-unpin-at-first
   (implies (and (fn-arpn-pinsp pins)
                 (consp (fn-arpn-unpin-at g pins)))
            (and (consp pins)
                 (<= (caar pins) (caar (fn-arpn-unpin-at g pins)))))))

(defthm fn-arpn-unpin-at-pinsp
  (implies (fn-arpn-pinsp pins)
           (fn-arpn-pinsp (fn-arpn-unpin-at g pins))))

(defthm fn-arpn-pin-at-at-most
  (implies (and (fn-arpn-at-most-p pins cur) (<= g cur))
           (fn-arpn-at-most-p (fn-arpn-pin-at g pins) cur)))

(defthm fn-arpn-unpin-at-at-most
  (implies (fn-arpn-at-most-p pins cur)
           (fn-arpn-at-most-p (fn-arpn-unpin-at g pins) cur)))

(defthm fn-arpn-at-most-monotone
  (implies (and (fn-arpn-at-most-p pins cur) (<= cur cur2))
           (fn-arpn-at-most-p pins cur2)))

(defthm fn-arpn-pins-of-pin-at
  (implies (fn-arpn-pinsp pins)
           (equal (fn-arpn-pins-of h (fn-arpn-pin-at g pins))
                  (if (equal h g)
                      (+ 1 (fn-arpn-pins-of h pins))
                    (fn-arpn-pins-of h pins)))))

(defthm fn-arpn-pins-of-unpin-at
  (implies (fn-arpn-pinsp pins)
           (equal (fn-arpn-pins-of h (fn-arpn-unpin-at g pins))
                  (if (equal h g)
                      (nfix (- (fn-arpn-pins-of h pins) 1))
                    (fn-arpn-pins-of h pins)))))

(local
 (defthm fn-arpn-pendp-revappend
   (implies (and (fn-arpn-pendp x) (fn-arpn-pendp y))
            (fn-arpn-pendp (revappend x y)))))

(local
 (defthm fn-arpn-split-acc-shape
   (implies (and (fn-arpn-pendp pend) (fn-arpn-pendp rel) (fn-arpn-pendp keep))
            (and (fn-arpn-pendp (mv-nth 0 (fn-arpn-split-acc pend pins rel keep)))
                 (fn-arpn-pendp (mv-nth 1 (fn-arpn-split-acc pend pins rel keep)))))
   :hints (("Goal" :induct (fn-arpn-split-acc pend pins rel keep)))))

(local
 (defthm fn-arpn-member-revappend
   (iff (member-equal e (revappend x y))
        (or (member-equal e x) (member-equal e y)))
   :hints (("Goal" :induct (revappend x y)))))

(local
 (defthm fn-arpn-split-acc-released-member
   (implies (member-equal e (mv-nth 0 (fn-arpn-split-acc pend pins rel keep)))
            (or (member-equal e rel)
                (and (member-equal e pend)
                     (fn-arpn-clear-through-p (car e) pins))))
   :rule-classes nil))

(defthm fn-arpn-split-released-are-clear
  (implies (member-equal e (mv-nth 0 (fn-arpn-split pend pins)))
           (and (member-equal e pend)
                (fn-arpn-clear-through-p (car e) pins)))
  :hints (("Goal" :use (:instance fn-arpn-split-acc-released-member
                                  (rel nil) (keep nil))
                  :in-theory (disable fn-arpn-clear-through-p))))

(local
 (defthm fn-arpn-split-acc-kept-member
   (implies (or (member-equal e keep)
                (and (member-equal e pend)
                     (not (fn-arpn-clear-through-p (car e) pins))))
            (member-equal e (mv-nth 1 (fn-arpn-split-acc pend pins rel keep))))
   :rule-classes nil))

(defthm fn-arpn-split-keeps-every-unclear
  (implies (and (member-equal e pend)
                (not (fn-arpn-clear-through-p (car e) pins)))
           (member-equal e (mv-nth 1 (fn-arpn-split pend pins))))
  :hints (("Goal" :use (:instance fn-arpn-split-acc-kept-member
                                  (rel nil) (keep nil))
                  :in-theory (disable fn-arpn-clear-through-p))))

(defthm fn-arpn-split-pendp
  (implies (fn-arpn-pendp pend)
           (and (fn-arpn-pendp (mv-nth 0 (fn-arpn-split pend pins)))
                (fn-arpn-pendp (mv-nth 1 (fn-arpn-split pend pins))))))

(verify-guards fn-arpn-step)

; ---------------------------------------------------------------- theorems

(defthm fn-arpn-initial-okp
  (fn-arpn-okp (fn-arpn-initial)))

(defthm fn-arpn-step-preserves-okp
  (implies (fn-arpn-okp st)
           (fn-arpn-okp (mv-nth 0 (fn-arpn-step st ev)))))

(defthm fn-arpn-step-generation-never-decreases
  (implies (fn-arpn-okp st)
           (<= (first st) (first (mv-nth 0 (fn-arpn-step st ev)))))
  :rule-classes :linear)

; A clear stamp is below every live pin.
(defthm fn-arpn-clear-through-below-every-pin
  (implies (and (fn-arpn-pinsp pins)
                (fn-arpn-clear-through-p s pins)
                (< 0 (fn-arpn-pins-of h pins)))
           (< s h)))

; ... and a stamp that is not clear has a live pin at or below it.
(defthm fn-arpn-not-clear-has-a-pin-at-or-below
  (implies (and (fn-arpn-pinsp pins)
                (not (fn-arpn-clear-through-p s pins)))
           (and (< 0 (fn-arpn-pins-of (caar pins) pins))
                (<= (caar pins) s))))

; A reader's pin is the current generation, held once more.
(defthm fn-arpn-pin-answers-the-generation
  (implies (fn-arpn-okp st)
           (let ((r (fn-arpn-step st '(:pin))))
             (and (equal (mv-nth 1 r) (first st))
                  (equal (fn-arpn-pins-of (first st) (second (mv-nth 0 r)))
                         (+ 1 (fn-arpn-pins-of (first st) (second st))))))))

; A retirement's stamp is at or above every live pin, and the generation
; moves past it: every later pin is above it.
(defthm fn-arpn-retire-stamp-covers-every-live-pin
  (implies (and (fn-arpn-okp st)
                (true-listp items)
                (< 0 (fn-arpn-pins-of h (second st))))
           (let ((r (fn-arpn-step st (list :retire items))))
             (and (<= h (mv-nth 1 r))
                  (equal (mv-nth 1 r) (first st))
                  (equal (first (mv-nth 0 r)) (+ 1 (mv-nth 1 r)))
                  (member-equal (cons (mv-nth 1 r) items) (third (mv-nth 0 r)))))))

; KEYSTONE (PRF-941).  Every retirement the host's :release answers was
; pending, and its stamp is below every live pin: each reader still running
; pinned after the retirement.
(defthm fn-arpn-release-postdates-every-live-pin
  (implies (and (fn-arpn-okp st)
                (member-equal e (mv-nth 1 (fn-arpn-step st '(:release))))
                (< 0 (fn-arpn-pins-of h (second (mv-nth 0 (fn-arpn-step st '(:release)))))))
           (and (member-equal e (third st))
                (< (car e) h)))
  :hints (("Goal" :in-theory (disable fn-arpn-split fn-arpn-clear-through-p)
                  :use ((:instance fn-arpn-split-released-are-clear
                                   (pend (third st)) (pins (second st)))
                        (:instance fn-arpn-clear-through-below-every-pin
                                   (s (car e)) (pins (second st)))))))

; ... and a retirement some live reader is pinned at or below stays pending.
(defthm fn-arpn-release-keeps-every-covered-retirement
  (implies (and (fn-arpn-okp st)
                (member-equal e (third st))
                (< 0 (fn-arpn-pins-of h (second st)))
                (<= h (car e)))
           (member-equal e (third (mv-nth 0 (fn-arpn-step st '(:release))))))
  :hints (("Goal" :in-theory (disable fn-arpn-split fn-arpn-clear-through-p)
                  :use ((:instance fn-arpn-split-keeps-every-unclear
                                   (pend (third st)) (pins (second st)))
                        (:instance fn-arpn-clear-through-below-every-pin
                                   (s (car e)) (pins (second st)))))))

; An unpin of a held generation removes exactly one reader there.
(defthm fn-arpn-unpin-removes-one-reader
  (implies (and (fn-arpn-okp st)
                (natp g)
                (fn-arpn-held-p g (second st)))
           (let ((r (fn-arpn-step st (list :unpin g))))
             (and (equal (mv-nth 1 r) :ok)
                  (equal (fn-arpn-pins-of h (second (mv-nth 0 r)))
                         (if (equal h g)
                             (- (fn-arpn-pins-of h (second st)) 1)
                           (fn-arpn-pins-of h (second st))))))))
