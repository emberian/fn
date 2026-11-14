; Source geometry and stored-count boundary controls. Qualification pending.
(in-package "ACL2")
(include-book "../books/txn")
(include-book "../books/article-membership")

(defun fn2-membership-slot-triplets (k n)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) nil
    (let ((s (fn2-txn-group-slot (nfix k))))
      (append (list s (+ 1 s) (+ 2 s))
              (fn2-membership-slot-triplets (+ 1 (nfix k)) (- n 1))))))
(assert-event
 (equal (fn2-membership-slot-triplets 0 7)
        '(8 9 10 11 12 13 14 15 16 17 18 19 21 22 23 24 25 26 27 28 29)))
(assert-event (equal *fn2-txn-groups-max* 7))
(assert-event (not (member-equal *fn2-txn-slot-depend* (fn2-membership-slot-triplets 0 7))))
(assert-event (no-duplicatesp-equal (fn2-membership-slot-triplets 0 7)))
(assert-event (equal (fn2-succ-replay-event-mask *fn2-article-membership-sid*) 1))
; Stored counts are independent of today's seven-group admission capacity.
(assert-event (eq (fn2-article-membership-position-code 8 9 0) :read))
(assert-event (eq (fn2-article-membership-position-code 9 9 0) :end))
(assert-event (eq (fn2-article-membership-position-code 9 9 1) :fault))
(assert-event (eq (fn2-article-membership-position-code 10 9 0) :fault))
(assert-event (eq (fn2-article-membership-position-code -1 9 0) :fault))
(assert-event (eq (fn2-article-membership-position-code (1- (expt 2 60)) (1- (expt 2 60)) 0) :end))
