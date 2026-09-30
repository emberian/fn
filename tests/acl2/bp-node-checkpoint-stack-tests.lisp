(in-package "ACL2")
(include-book "../../books/bp-node-checkpoint-stack")

; Reachable encoder pair expansion, with complete antecedent and conclusions.
(assert-event
 (let* ((tasks (list (list :scan (cons nil t) 2 (cons nil t) 0)))
        (next (fn-bpn-nth 2 (fn-bpnrc-step tasks))))
   (and (fn-bpnrc-tasks-validp tasks)
        (fn-bpcks-stackp tasks 2) (fn-bpcks-small-tasks-p tasks)
        (equal (fn-bpn-nth 0 (fn-bpnrc-step tasks)) :continue)
        (equal next '((:value nil 1) (:value t 1)))
        (fn-bpcks-stackp next 2) (fn-bpcks-small-tasks-p next)
        (<= (len next) (* 2 (+ 2 2))))))

; Actual CK census/grant creates this native source-turn input. No supplied
; scalar depth roster is substituted for the queue shape.
(assert-event
 (let* ((token '(:maintenance 0 7 0))
        (initial (fn-bpck-begin token 7 1 8 nil nil 0 0 10000))
        (counted (fn-bpck-census-step initial 128))
        (job (fn-bpck-stage-granted counted (list :grown token)))
        (next (fn-bpn-nth 0 (fn-bpck-emit-step job))))
   (and (equal (fn-bpn-nth 6 job) :emit)
        (fn-bpcks-stackp (fn-bpn-nth 7 job) (fn-bpn-nth 4 job))
        (fn-bpcks-small-tasks-p (fn-bpn-nth 7 job))
        (fn-bpcks-stackp (fn-bpn-nth 7 next) (fn-bpn-nth 4 next))
        (fn-bpcks-small-tasks-p (fn-bpn-nth 7 next))
        (equal (fn-bpn-nth 4 next) 8)
        (<= (len (fn-bpn-nth 7 next)) (* 2 (+ 2 8))))))

; Hypothesis removal, separately labelled corrupted-state witness: no normal
; constructor creates four adjacent rank-zero tasks. Omitting the stack
; invariant allows the next source turn to retain an invalid three-task run.
(assert-event
 (let* ((tasks '((:octets nil) (:octets nil) (:octets nil) (:octets nil)))
        (job (fn-bpck-make '(:maintenance 0 7 0) 7 1 0 nil :emit tasks
                            3 1000 0 :private))
        (next (fn-bpn-nth 0 (fn-bpck-emit-step job))))
   (and (fn-bpcks-small-tasks-p tasks)
        (not (fn-bpcks-stackp tasks 0))
        (not (fn-bpcks-stackp (fn-bpn-nth 7 next) (fn-bpn-nth 4 next))))))

; The ordered-count theorem needs its range hypothesis even for an empty
; stack: the predicate has no tasks to constrain LOW/HIGH in that case.
(assert-event
 (and (integerp 100) (<= -1 100) (natp 0)
      (fn-bpcks-orderedp nil 100 0 nil)
      (not (<= 100 0))
      (not (<= (len nil) (+ (* 2 (+ 1 (- (nfix 0) (ifix 100)))) 0)))))
