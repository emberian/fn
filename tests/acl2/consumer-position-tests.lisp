; Executable E2 decision traces, not Store publication or a served consumer API.
(in-package "ACL2")
(include-book "../../books/consumer-position")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cpt-h* '(1))
(defconst *cpt-i* '(2))
(defconst *cpt-c* '(3))
(defconst *cpt-p* '(4))
(defconst *cpt-q* '(5))
(defconst *cpt-first* (fn-cp-initial *cpt-h* *cpt-i* 10))
(defconst *cpt-reg* (fn-cp-register *cpt-first* *cpt-p* *cpt-c* *cpt-q* 1 1))
(assert-event (equal (car *cpt-reg*) :write))
(defconst *cpt-registered* (fn-cp-apply *cpt-first* (cadr *cpt-reg*)))
(assert-event (and (equal (nth 3 *cpt-registered*) 10)
                   (equal (nth 4 *cpt-first*) 1)
                   (equal (nth 4 *cpt-registered*) 2)))
(defconst *cpt-entry* (fn-cp-find *cpt-c* (nth 5 *cpt-registered*)))
(defconst *cpt-zero* (fn-cp-scope-cursor *cpt-registered* *cpt-entry*))
(defconst *cpt-five* (fn-cp-cursor *cpt-h* *cpt-i* *cpt-c* *cpt-p* *cpt-q* 1 1 1 5))
(defconst *cpt-eleven* (fn-cp-cursor *cpt-h* *cpt-i* *cpt-c* *cpt-p* *cpt-q* 1 1 1 11))

; Exact v1 byte grammar, including zero/trailing input, bound and version.
(assert-event (equal (fn-cp-cursor-decode (fn-cp-cursor-encode *cpt-five*))
                     (list :ok *cpt-five*)))
(assert-event (<= (len (fn-cp-cursor-encode *cpt-five*)) *fn-cp-max-token*))
(defconst *cpt-max-id* (make-list 64 :initial-element 255))
(defconst *cpt-max-cursor*
  (fn-cp-cursor *cpt-max-id* *cpt-max-id* *cpt-max-id*
                *cpt-max-id* *cpt-max-id* 4294967295 4294967295
                4294967295 4294967295))
(assert-event (equal (len (fn-cp-cursor-encode *cpt-max-cursor*)) 346))
(assert-event (equal (fn-cp-cursor-decode
                      (fn-cp-cursor-encode *cpt-max-cursor*))
                     (list :ok *cpt-max-cursor*)))
(assert-event (equal (fn-cp-cursor-decode
                      (append (fn-cp-cursor-encode *cpt-five*) '(0)))
                     '(:refused :grammar)))
(assert-event (equal (fn-cp-cursor-decode
                      (cons 0 (cdr (fn-cp-cursor-encode *cpt-five*))))
                     '(:refused :version)))
(assert-event (equal (fn-cp-cursor-decode (make-list 513 :initial-element 0))
                     '(:refused :octets)))
(assert-event (equal (fn-cp-cursor-decode
                      (append *fn-cp-magic* (list *fn-cp-version* 65)))
                     '(:refused :grammar)))

; A page cursor is a proposal to record the consumer's own declaration.
(assert-event (equal (fn-cp-ack *cpt-registered* *cpt-p* 1 1 *cpt-eleven*)
                     '(:refused :future)))
(defconst *cpt-ack* (fn-cp-ack *cpt-registered* *cpt-p* 1 1 *cpt-five*))
(assert-event (equal (car *cpt-ack*) :write))
(defconst *cpt-acked* (fn-cp-apply *cpt-registered* (cadr *cpt-ack*)))
(assert-event (and (equal (nth 3 *cpt-acked*) 10)
                   (equal (nth 4 *cpt-acked*) 2)))
(assert-event (equal (nth 7 (fn-cp-find *cpt-c* (nth 5 *cpt-acked*))) 5))
(assert-event (equal (car (fn-cp-ack *cpt-acked* *cpt-p* 1 1 *cpt-five*)) :no-op))
(assert-event (equal (fn-cp-ack *cpt-acked* *cpt-p* 1 1 *cpt-zero*)
                     '(:refused :backwards)))
(assert-event (equal (fn-cp-ack *cpt-acked* *cpt-p* 1 2 *cpt-five*)
                     '(:refused :scope)))
(assert-event (equal (fn-cp-ack *cpt-acked* '(99) 1 1 *cpt-five*)
                     '(:refused :scope)))
(assert-event (equal (fn-cp-ack *cpt-acked* *cpt-p* 1 1
                                (fn-cp-cursor '(99) *cpt-i* *cpt-c* *cpt-p*
                                              *cpt-q* 1 1 1 6))
                     '(:refused :scope)))

; Unregister and re-register the same scope: a delayed old ack cannot move
; the new position.  The global epoch scalar survives removal of the entry.
(defconst *cpt-unreg* (fn-cp-unregister *cpt-acked* *cpt-p* *cpt-c*))
(defconst *cpt-removed* (fn-cp-apply *cpt-acked* (cadr *cpt-unreg*)))
(defconst *cpt-reg2* (fn-cp-register *cpt-removed* *cpt-p* *cpt-c* *cpt-q* 1 1))
(defconst *cpt-again* (fn-cp-apply *cpt-removed* (cadr *cpt-reg2*)))
(assert-event (equal (nth 6 (fn-cp-find *cpt-c* (nth 5 *cpt-again*))) 2))
(assert-event (equal (fn-cp-ack *cpt-again* *cpt-p* 1 1 *cpt-five*)
                     '(:refused :scope)))
(assert-event (equal (nth 7 (fn-cp-find *cpt-c* (nth 5 *cpt-again*))) 0))
(defconst *cpt-new-five* (fn-cp-cursor *cpt-h* *cpt-i* *cpt-c* *cpt-p* *cpt-q* 1 1 2 5))
(assert-event (equal (car (fn-cp-ack *cpt-again* *cpt-p* 1 1 *cpt-new-five*))
                     :write))

; Rebase resets progress under a new view and consumes another epoch.
(defconst *cpt-rebase* (fn-cp-rebase *cpt-acked* *cpt-p* *cpt-c* *cpt-q* 1 2))
(defconst *cpt-rebased* (fn-cp-apply *cpt-acked* (cadr *cpt-rebase*)))
(assert-event (equal (nth 7 (fn-cp-find *cpt-c* (nth 5 *cpt-rebased*))) 0))
(assert-event (equal (nth 6 (fn-cp-find *cpt-c* (nth 5 *cpt-rebased*))) 2))
(assert-event (equal (fn-cp-ack *cpt-rebased* *cpt-p* 1 2 *cpt-five*)
                     '(:refused :scope)))

; These witnesses use the reachable write arm, rather than satisfying the
; keystones only by failing their write antecedent.
(assert-event (and (equal (car *cpt-ack*) :write)
                   (<= (nth 9 *cpt-five*) (nth 3 *cpt-registered*))
                   (equal (nth 8 *cpt-five*) (nth 6 *cpt-entry*))))
(assert-event (and (not (equal (nth 8 *cpt-five*)
                               (nth 6 (fn-cp-find *cpt-c* (nth 5 *cpt-again*)))))
                   (equal (fn-cp-ack *cpt-again* *cpt-p* 1 1 *cpt-five*)
                          '(:refused :scope))))

; Removing the stale-epoch hypothesis is false on the same reachable
; registration with a fresh cursor.  Future-bound and epoch conclusions also
; fail for input cursors when their write-arm premise is removed.
(must-fail (defthm fn-cpt-epoch-refusal-needs-mismatch
             (equal (fn-cp-ack s caller qver view cursor)
                    (list :refused :scope))))
(must-fail (defthm fn-cpt-bound-needs-write-arm
             (<= (nth 9 cursor) (nth 3 s))))
(must-fail (defthm fn-cpt-epoch-binding-needs-write-arm
             (equal (nth 8 cursor)
                    (nth 6 (fn-cp-find (nth 3 cursor) (nth 5 s))))))

; Reach capacity through actual register/apply decisions, not a fabricated
; duplicate-filled table.  Each one-byte consumer ID is distinct.
(defun fn-cpt-fill (s n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) s
    (let* ((candidate (fn-cp-register s *cpt-p* (list (1- n)) *cpt-q* 1 1)))
      (fn-cpt-fill (fn-cp-apply s (cadr candidate)) (1- n)))))
(defconst *cpt-full* (fn-cpt-fill *cpt-first* 256))
(assert-event (equal (len (nth 5 *cpt-full*)) *fn-cp-max-consumers*))
(assert-event (equal (fn-cp-register *cpt-full* *cpt-p* '(0 0) *cpt-q* 1 1)
                     '(:refused :capacity)))
(defconst *cpt-full-rebase* (fn-cp-rebase *cpt-full* *cpt-p* '(0) *cpt-q* 1 2))
(assert-event (equal (car *cpt-full-rebase*) :write))
(assert-event (equal (len (nth 5 (fn-cp-apply *cpt-full*
                                              (cadr *cpt-full-rebase*))))
                     *fn-cp-max-consumers*))
(must-fail (defthm fn-cpt-capacity-needs-bounded-initial-table
             (<= (len (nth 5 (fn-cp-apply s event)))
                 *fn-cp-max-consumers*)))
