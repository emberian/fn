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
(assert-event (and (fn-cp-statep *cpt-first*)
                   (fn-cp-statep *cpt-registered*)))
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
(must-fail (defthm fn-cpt-roundtrip-needs-valid-cursor
             (equal (fn-cp-cursor-decode (fn-cp-cursor-encode cursor))
                    (list :ok cursor))))
(assert-event (equal (fn-cp-cursor-decode
                      (append (fn-cp-cursor-encode *cpt-five*) '(0)))
                     '(:refused :grammar)))
(assert-event (equal (fn-cp-cursor-decode
                      (cons 0 (cdr (fn-cp-cursor-encode *cpt-five*))))
                     '(:refused :version)))
(assert-event (equal (fn-cp-cursor-decode (make-list 513 :initial-element 0))
                     '(:refused :octets)))
(must-fail (defthm fn-cpt-overlong-refusal-needs-overlong-input
             (equal (fn-cp-cursor-decode octets)
                    '(:refused :octets))))
(assert-event (equal (fn-cp-cursor-decode
                      (append *fn-cp-magic* (list *fn-cp-version* 65)))
                     '(:refused :grammar)))

; A page cursor is a proposal to record the consumer's own declaration.
(assert-event (equal (fn-cp-ack *cpt-registered* *cpt-p* 1 1 *cpt-eleven*)
                     '(:refused :future)))
(defconst *cpt-ack* (fn-cp-ack *cpt-registered* *cpt-p* 1 1 *cpt-five*))
(assert-event (equal (car *cpt-ack*) :write))
(defconst *cpt-acked* (fn-cp-apply *cpt-registered* (cadr *cpt-ack*)))
(assert-event (fn-cp-statep *cpt-acked*))
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
(assert-event (and (fn-cp-statep *cpt-removed*)
                   (fn-cp-statep *cpt-again*)
                   (equal (fn-cp-apply-trace
                           *cpt-acked*
                           (list (cadr *cpt-unreg*) (cadr *cpt-reg2*)))
                          *cpt-again*)))
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

; Reach the operator's bound through actual register/apply decisions, not a
; fabricated duplicate-filled table.  Each consumer ID is distinct: one
; octet below 256, then (1 k-256).
; The old figure 256 is an instance of MAX: every pre-D27 witness runs at it.
(defconst *cpt-old* 256)
(defun fn-cpt-fill (s max n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) s
    (let* ((k (1- n))
           (candidate (fn-cp-register-within
                       s max *cpt-p* (if (< k 256) (list k) (list 1 (- k 256)))
                       *cpt-q* 1 1)))
      (fn-cpt-fill (fn-cp-apply s (cadr candidate)) max (1- n)))))
(defconst *cpt-full* (fn-cpt-fill *cpt-first* *cpt-old* 256))
(assert-event (equal (len (nth 5 *cpt-full*)) *cpt-old*))
(assert-event (fn-cp-statep *cpt-full*))
; Positive witness at the bound: the 256th register is a write under 256.
(defconst *cpt-255* (fn-cpt-fill *cpt-first* *cpt-old* 255))
(assert-event (equal (len (nth 5 *cpt-255*)) 255))
(assert-event (equal (car (fn-cp-register-within *cpt-255* *cpt-old* *cpt-p*
                                                 '(0 0) *cpt-q* 1 1))
                     :write))
; Exactly past the bound: the 257th is refused by name under 256 ...
(assert-event (equal (fn-cp-register-within *cpt-full* *cpt-old* *cpt-p*
                                            '(0 0) *cpt-q* 1 1)
                     '(:refused :max-consumers)))
; ... and is a write under a raised bound (300, the native case's figure),
; with the same event replay re-runs through fn-cp-register.
(defconst *cpt-257* (fn-cp-register-within *cpt-full* 300 *cpt-p* '(0 0)
                                           *cpt-q* 1 1))
(assert-event (equal (car *cpt-257*) :write))
(assert-event (equal *cpt-257*
                     (fn-cp-register *cpt-full* *cpt-p* '(0 0) *cpt-q* 1 1)))
(assert-event (equal (len (nth 5 (fn-cp-apply *cpt-full* (cadr *cpt-257*))))
                     257))
(assert-event (fn-cp-statep (fn-cp-apply *cpt-full* (cadr *cpt-257*))))
; Replay validity carries no admission bound: the committed 257th applies.
(defconst *cpt-300* (fn-cpt-fill *cpt-first* 300 300))
(assert-event (equal (len (nth 5 *cpt-300*)) 300))
(assert-event (equal (fn-cp-register-within *cpt-300* 300 *cpt-p* '(0 0)
                                            *cpt-q* 1 1)
                     '(:refused :max-consumers)))
; A no-op and a refusal fn-cp-register gives are unchanged at the bound.
(assert-event (equal (car (fn-cp-register-within *cpt-full* *cpt-old* *cpt-p*
                                                 '(0) *cpt-q* 1 1))
                     :no-op))
(defconst *cpt-full-rebase* (fn-cp-rebase *cpt-full* *cpt-p* '(0) *cpt-q* 1 2))
(assert-event (equal (car *cpt-full-rebase*) :write))
(assert-event (equal (len (nth 5 (fn-cp-apply *cpt-full*
                                              (cadr *cpt-full-rebase*))))
                     *cpt-old*))
; Teeth of fn-cp-register-within-refuses-exactly-past-the-operator-bound: the
; refusal needs the table at the bound (a write below it is not refused) ...
(must-fail (defthm fn-cpt-within-refuses-without-the-bound
             (implies (equal (car (fn-cp-register s caller consumer query
                                                  qver view))
                             :write)
                      (equal (fn-cp-register-within s max caller consumer
                                                    query qver view)
                             '(:refused :max-consumers)))))
; ... and a write: an overlong caller stays refused :input, not :max-consumers.
(assert-event (equal '(:refused :input)
              (fn-cp-register *cpt-full* (make-list 65 :initial-element 1)
                              '(0 0) *cpt-q* 1 1)))
(assert-event (equal (fn-cp-register-within *cpt-full* *cpt-old* (make-list 65 :initial-element 1)
                                            '(0 0) *cpt-q* 1 1)
                     (fn-cp-register *cpt-full* (make-list 65 :initial-element 1)
                                     '(0 0) *cpt-q* 1 1)))
; Teeth of fn-cp-apply-preserves-consumer-capacity: one per hypothesis.
; Without the starting table within MAX:
(must-fail (defthm fn-cpt-capacity-needs-bounded-initial-table
             (implies (or (not (eq (nth 0 event) :register))
                          (equal (fn-cp-register-within s max caller consumer
                                                        query qver view)
                                 (list :write event)))
                      (<= (len (nth 5 (fn-cp-apply s event))) (nfix max)))))
; Without the served decision's write (a register applied at the bound):
(must-fail (defthm fn-cpt-capacity-needs-the-served-decision
             (implies (<= (len (nth 5 s)) (nfix max))
                      (<= (len (nth 5 (fn-cp-apply s event))) (nfix max)))))
; The witness of the second: the committed 257th applied to a 256 table
; exceeds 256 (the replay admits it; the served decision under 256 did not).
(assert-event (< *cpt-old*
                 (len (nth 5 (fn-cp-apply *cpt-full* (cadr *cpt-257*))))))

; No invariant is asserted of malformed initial states.  The transition
; theorem and its trace corollary both require a recognized starting state.
(must-fail (defthm fn-cpt-statep-needs-valid-start
             (fn-cp-statep (fn-cp-apply s event))))
(must-fail (defthm fn-cpt-trace-needs-valid-start
             (fn-cp-statep (fn-cp-apply-trace s events))))
