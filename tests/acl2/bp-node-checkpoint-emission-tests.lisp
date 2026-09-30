; Complete literal teeth for actual bounded emission and terminal frame prefix.
; Typed grant is a codec test input, not evidence of an actual funding grant.
(in-package "ACL2")
(include-book "../../books/bp-node-checkpoint-emission")
(defun fn-bpcke-test-history (job fuel emitted)
 (declare (xargs :guard t :measure (nfix fuel) :verify-guards nil))
 (if (or (zp (nfix fuel)) (not (equal (fn-bpn-nth 6 job) :emit))) nil
  (let ((answer (fn-bpck-emit-step job)))
   (cons (list job emitted answer)
    (fn-bpcke-test-history (car answer) (1- (nfix fuel))
                          (append emitted (cadr answer)))))))
(defconst *bpcke-token* '(:maintenance 0 7 0))
(defconst *bpcke-initial* (fn-bpck-begin *bpcke-token* 7 1 8 nil nil 0 0 10000))
(defconst *bpcke-counted* (fn-bpck-census-step *bpcke-initial* 128))
(defconst *bpcke-emitting*
 (fn-bpck-stage-observation
  (fn-bpck-stage-granted *bpcke-counted* (list :grown *bpcke-token*)) :created))
(make-event `(defconst *bpcke-history* ',(fn-bpcke-test-history *bpcke-emitting* 128 nil)))
(defconst *bpcke-first* (car *bpcke-history*))
(defconst *bpcke-last* (car (last *bpcke-history*)))
; Positive preservation: the complete invariant antecedent and all outputs.
(assert-event
 (let* ((job (car *bpcke-first*)) (emitted (cadr *bpcke-first*))
        (answer (fn-bpck-emit-step job)))
  (and (fn-bpcke-invariantp job emitted)
       (fn-bpcke-invariantp (car answer) (append emitted (cadr answer)))
       (equal (fn-bpn-nth 5 (car answer)) (fn-bpn-nth 5 job))
       (<= (len (cadr answer)) 9))))
; Positive terminal: actual final producer turn, exact BP header+payload bytes.
(assert-event
 (let* ((job (car *bpcke-last*)) (emitted (cadr *bpcke-last*))
        (answer (fn-bpck-emit-step job)))
  (and (equal (fn-bpn-nth 6 job) :emit)
       (fn-bpcke-invariantp job emitted)
       (equal (fn-bpn-nth 6 (car answer)) :digest-finish)
       (equal (append emitted (cadr answer))
        (fn-bpnr-checkpoint-prefix (fn-bpnr-enc (fn-bpn-nth 5 job) (fn-bpn-nth 4 job)))))))
; Hypothesis removal: wrong ghost write history, original actual job unchanged.
(assert-event
 (let* ((job (car *bpcke-first*)) (emitted '(1))
        (answer (fn-bpck-emit-step job)))
  (and (not (fn-bpcke-invariantp job emitted))
       (not (and (fn-bpcke-invariantp (car answer) (append emitted (cadr answer)))
                 (equal (fn-bpn-nth 5 (car answer)) (fn-bpn-nth 5 job))
                 (<= (len (cadr answer)) 9))))))
; Terminal phase removal, explicitly corrupted state: prematurely mark finish.
(defconst *bpcke-premature*
 (fn-bpck-make *bpcke-token* 7 1 8 (fn-bpn-nth 5 *bpcke-emitting*)
               :digest-finish (fn-bpn-nth 7 *bpcke-emitting*)
               (fn-bpn-nth 8 *bpcke-emitting*) 10000 0 :private))
(assert-event
 (let ((answer (fn-bpck-emit-step *bpcke-premature*)))
  (and (not (equal (fn-bpn-nth 6 *bpcke-premature*) :emit))
       (fn-bpcke-invariantp *bpcke-premature* nil)
       (equal (fn-bpn-nth 6 (car answer)) :digest-finish)
       (not (equal (cadr answer)
        (fn-bpnr-checkpoint-prefix
         (fn-bpnr-enc (fn-bpn-nth 5 *bpcke-premature*) 8)))))))
; Terminal invariant removal: wrong write history with every retained phase.
(assert-event
 (let* ((job (car *bpcke-last*)) (emitted '(0))
        (answer (fn-bpck-emit-step job)))
  (and (equal (fn-bpn-nth 6 job) :emit)
       (not (fn-bpcke-invariantp job emitted))
       (equal (fn-bpn-nth 6 (car answer)) :digest-finish)
       (not (equal (append emitted (cadr answer))
        (fn-bpnr-checkpoint-prefix (fn-bpnr-enc (fn-bpn-nth 5 job) (fn-bpn-nth 4 job))))))))
; Terminal finish removal: first reachable bounded turn has more bytes to emit.
(assert-event
 (let* ((job (car *bpcke-first*)) (emitted (cadr *bpcke-first*))
        (answer (fn-bpck-emit-step job)))
  (and (equal (fn-bpn-nth 6 job) :emit)
       (fn-bpcke-invariantp job emitted)
       (not (equal (fn-bpn-nth 6 (car answer)) :digest-finish))
       (not (equal (append emitted (cadr answer))
        (fn-bpnr-checkpoint-prefix (fn-bpnr-enc (fn-bpn-nth 5 job) (fn-bpn-nth 4 job))))))))
