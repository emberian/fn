; Response ownership of arena-reader generations (PRF-1059).
; The host captures one response plan per connection under the owner mutex.
; The plan may contain several pipelined cursor replies.  Its single hold
; lives until every reply window drains or the whole plan is cancelled.
; fnn-owner-response-pin/unpin call fn-rpin-step under the same lock as the
; other arena pin events.  Generation, multiplicity, duplicate capture and
; idempotent cancellation are ACL2 decisions, never host arithmetic.
(in-package "ACL2")
(include-book "arena-reader-pins")

(defun fn-rpin-owner (id owners)
  (declare (xargs :guard t))
  (cond ((atom owners) nil)
        ((and (consp (car owners)) (equal id (caar owners))) (car owners))
        (t (fn-rpin-owner id (cdr owners)))))

(defun fn-rpin-count-at (g owners)
  (declare (xargs :guard t))
  (if (consp owners)
      (+ (if (and (consp (car owners)) (equal g (cdar owners))) 1 0)
         (fn-rpin-count-at g (cdr owners)))
    0))

(defun fn-rpin-remove (id owners)
  (declare (xargs :guard t))
  (cond ((atom owners) nil)
        ((and (consp (car owners)) (equal id (caar owners))) (cdr owners))
        (t (cons (car owners) (fn-rpin-remove id (cdr owners))))))

(defun fn-rpin-step (owners st event)
  (declare (xargs :guard (and (alistp owners) (fn-arpn-okp st))))
  (let* ((id (and (consp event) (consp (cdr event)) (cadr event)))
         (held (fn-rpin-owner id owners)))
    (case (and (consp event) (car event))
      (:acquire
       (if (or (not (natp id)) held)
           (mv owners st :duplicate)
         (mv-let (next g) (fn-arpn-step st '(:pin))
           (mv (cons (cons id g) owners) next :acquired))))
      (:release
       (if (not held)
           (mv owners st :absent)
         (mv-let (next answer) (fn-arpn-step st (list :unpin (cdr held)))
           (if (equal answer :ok)
               (mv (fn-rpin-remove id owners) next :released)
             (mv owners st :inconsistent)))))
      (otherwise (mv owners st :refused)))))

(defthm fn-rpin-step-keeps-arena-invariant
  (implies (fn-arpn-okp st)
           (fn-arpn-okp (mv-nth 1 (fn-rpin-step owners st event))))
  :hints (("Goal" :in-theory (disable fn-arpn-step fn-arpn-okp
                                      fn-arpn-step-preserves-okp)
                  :use ((:instance fn-arpn-step-preserves-okp (ev '(:pin)))
                        (:instance fn-arpn-step-preserves-okp
                                   (ev (list :unpin (cdr (fn-rpin-owner (cadr event) owners)))))))))

(local
 (defthm fn-rpin-remove-owner-keeps-alist
   (implies (alistp owners) (alistp (fn-rpin-remove id owners)))
   :hints (("Goal" :induct (fn-rpin-remove id owners)))))

(defthm fn-rpin-step-keeps-owner-table
  (implies (alistp owners)
           (alistp (mv-nth 0 (fn-rpin-step owners st event))))
  :hints (("Goal" :in-theory (disable fn-arpn-step fn-rpin-owner fn-rpin-remove))))

(defthm fn-rpin-count-at-removes-one-owned-hold
  (equal (fn-rpin-count-at h (fn-rpin-remove id owners))
         (if (and (fn-rpin-owner id owners)
                  (equal h (cdr (fn-rpin-owner id owners))))
             (- (fn-rpin-count-at h owners) 1)
           (fn-rpin-count-at h owners)))
  :hints (("Goal" :induct (fn-rpin-remove id owners))))

; Pointwise ownership relation: at every generation H, the responses own
; no more reader holds than the arena table carries (other users may carry
; additional holds).  It is initialized at NIL and preserved for each H.
(local
 (defthm fn-rpin-arena-has-pin-table
   (implies (fn-arpn-okp st) (fn-arpn-pinsp (second st)))
   :hints (("Goal" :in-theory (enable fn-arpn-okp)))))
(local
 (defthm fn-rpin-pins-of-natp
   (implies (fn-arpn-pinsp pins) (natp (fn-arpn-pins-of h pins)))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (fn-arpn-pins-of h pins)
                   :in-theory (enable fn-arpn-pinsp fn-arpn-pins-of)))))
(local
 (defthm fn-rpin-count-at-cons
   (equal (fn-rpin-count-at h (cons (cons id g) owners))
          (+ (if (equal h g) 1 0) (fn-rpin-count-at h owners)))))

(defthm fn-rpin-step-preserves-funded-ownership
  (implies (and (fn-arpn-okp st)
                (<= (fn-rpin-count-at h owners)
                    (fn-arpn-pins-of h (second st))))
           (let ((next (fn-rpin-step owners st event)))
             (<= (fn-rpin-count-at h (mv-nth 0 next))
                 (fn-arpn-pins-of h (second (mv-nth 1 next))))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable fn-arpn-okp fn-arpn-pin-at fn-arpn-unpin-at
                                      fn-arpn-pins-of fn-rpin-owner fn-rpin-remove
                                      fn-rpin-count-at alistp)
                  :use ((:instance fn-rpin-pins-of-natp (pins (second st)))))))

(defthm fn-rpin-empty-ownership-is-funded
  (implies (fn-arpn-okp st)
           (<= (fn-rpin-count-at h nil) (fn-arpn-pins-of h (second st))))
  :hints (("Goal" :in-theory (enable fn-rpin-count-at)
                  :use ((:instance fn-rpin-pins-of-natp (pins (second st)))))))

(defthm fn-rpin-duplicate-capture-keeps-ownership
  (implies (fn-rpin-owner id owners)
           (and (equal (mv-nth 0 (fn-rpin-step owners st (list :acquire id))) owners)
                (equal (mv-nth 1 (fn-rpin-step owners st (list :acquire id))) st)
                (equal (mv-nth 2 (fn-rpin-step owners st (list :acquire id))) :duplicate))))

(defthm fn-rpin-absent-release-keeps-ownership
  (implies (not (fn-rpin-owner id owners))
           (and (equal (mv-nth 0 (fn-rpin-step owners st (list :release id))) owners)
                (equal (mv-nth 1 (fn-rpin-step owners st (list :release id))) st)
                (equal (mv-nth 2 (fn-rpin-step owners st (list :release id))) :absent))))

(defthm fn-rpin-acquire-holds-the-captured-generation
  (implies (and (fn-arpn-okp st) (natp id)
                (not (fn-rpin-owner id owners)))
           (let ((next (fn-rpin-step owners st (list :acquire id))))
             (and (equal (mv-nth 2 next) :acquired)
                  (equal (fn-rpin-owner id (mv-nth 0 next)) (cons id (first st)))
                  (equal (fn-arpn-pins-of h (second (mv-nth 1 next)))
                         (if (equal h (first st))
                             (+ 1 (fn-arpn-pins-of h (second st)))
                           (fn-arpn-pins-of h (second st)))))))
  :hints (("Goal" :in-theory (enable fn-rpin-owner))))

(defthm fn-rpin-release-settles-only-the-named-response
  (implies (and (fn-arpn-okp st) (fn-rpin-owner id owners)
                (natp (cdr (fn-rpin-owner id owners)))
                (fn-arpn-held-p (cdr (fn-rpin-owner id owners)) (second st)))
           (let ((next (fn-rpin-step owners st (list :release id))))
             (and (equal (mv-nth 2 next) :released)
                  (equal (mv-nth 0 next) (fn-rpin-remove id owners))
                  (equal (fn-arpn-pins-of h (second (mv-nth 1 next)))
                         (if (equal h (cdr (fn-rpin-owner id owners)))
                             (- (fn-arpn-pins-of h (second st)) 1)
                           (fn-arpn-pins-of h (second st)))))))
  :hints (("Goal" :use ((:instance fn-arpn-unpin-removes-one-reader
                                    (g (cdr (fn-rpin-owner id owners))))))))

(in-theory (disable fn-rpin-owner fn-rpin-count-at fn-rpin-remove fn-rpin-step))
