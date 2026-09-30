; Unactivated S9 cursor contract; no native/funding verdict.
(in-package "ACL2")
(include-book "../../books/owner-retire-cursor")

(defconst *orc-limits* (fn-feed-limits 1024 1000 3 t))
(defconst *orc-dropped*
  (list (fn-own-feed-entry
         "gave-up" nil
         (fn-feed-make '(103) *orc-limits*
                       (list (fn-feed-entry '(60 98 62)
                                            '(:dropped :retry-bound) 3 0))
                       nil 0 7 0))))
(defconst *orc-pending*
  (cons (fn-own-feed-entry
         "silent" nil
         (fn-feed-make '(115) *orc-limits*
                       (list (fn-feed-entry '(60 97 62) :queued 1 0))
                       nil 0 nil 0))
        *orc-dropped*))

; Nonempty positive for tally conservation: one pending and one dropped
; queue, checked through every table-load and queue-inspection step.
(defconst *orc-p0* (fn-orc-start *orc-pending* 7))
(defconst *orc-p1* (fn-orc-next *orc-p0*))
(defconst *orc-p2* (fn-orc-next *orc-p1*))
(defconst *orc-p3* (fn-orc-next *orc-p2*))
(defconst *orc-p4* (fn-orc-next *orc-p3*))
(assert-event
 (and (equal (fn-orc-table-pending-model *orc-pending*) 1)
      (equal (fn-orc-remaining *orc-p0*) 1)
      (equal (fn-orc-remaining *orc-p1*) 1)
      (equal (fn-orc-remaining *orc-p2*) 1)
      (equal (fn-orc-remaining *orc-p3*) 1)
      (equal (fn-orc-remaining *orc-p4*) 1)
      (fn-orc-donep *orc-p4*)
      (not (fn-orc-zero-currentp *orc-p4* 7))))

; Nonempty positive for completed zero: the sole queue entry really gave
; up at its retry bound, so it stays undelivered but no longer pending.
(defconst *orc-d0* (fn-orc-start *orc-dropped* 7))
(defconst *orc-d1* (fn-orc-next *orc-d0*))
(defconst *orc-d2* (fn-orc-next *orc-d1*))
(assert-event
 (and (consp *orc-dropped*)
      (equal (len (fn-feed-queue
                   (fn-own-feed-entry-feed (car *orc-dropped*)))) 1)
      (fn-orc-zero-currentp *orc-d2* 7)
      (equal (fn-orc-remaining *orc-d2*) 0)))

; Hypothesis removal for complete-zero: its zero-current antecedent fails
; and its conclusion fails.  Every retained internal check holds, but the
; pending entry has not been inspected.  Calling its accumulator a result
; would incorrectly discharge a live silent peer.
(assert-event
 (and (not (fn-orc-donep *orc-p0*))
      (equal (nth 4 *orc-p0*) 7)
      (equal (nfix (nth 3 *orc-p0*)) 0)
      (not (fn-orc-zero-currentp *orc-p0* 7))
      (not (equal (fn-orc-remaining *orc-p0*) 0))))

; Mutation witness, stale coordinate: the scan is complete and its
; tally is zero, but it is stale.  It never authorizes a current zero.
(assert-event
 (and (fn-orc-donep *orc-d2*)
      (equal (nfix (nth 3 *orc-d2*)) 0)
      (not (equal (nth 4 *orc-d2*) 8))
      (not (fn-orc-zero-currentp *orc-d2* 8))))
