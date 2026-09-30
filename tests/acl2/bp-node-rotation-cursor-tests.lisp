; PRF-1137 planned codec library teeth, no host publication activation.
(in-package "ACL2")
(include-book "../../books/bp-node-rotation-cursor")

(defun bprc-test-casesp (cases)
  (if (atom cases) t
    (let* ((x (car cases)) (tasks (fn-bpnrc-begin x 64))
           (answer (fn-bpnrc-run tasks 2048 nil))
           (census (fn-bpnrc-census-run tasks 2048 0)))
      (and (fn-bpnrc-tasks-validp tasks)
           (equal (fn-bpn-nth 0 answer) :done)
           (equal (fn-bpn-nth 1 answer) (fn-bpnr-enc x 64))
           (equal (fn-bpn-nth 0 census) :done)
           (equal (fn-bpn-nth 1 census) (len (fn-bpnr-enc x 64)))
           (bprc-test-casesp (cdr cases))))))

(defconst *bprc-ck*
  (fn-bpnr-checkpoint 7
                      (list (list :held '(0 128 255) "row" '(7 . 12)))
                      (list (list :handoff :ready)) '(2 . 19) 40 81))
(assert-event
 (bprc-test-casesp
  (list nil t :keyword 'acl2::value 'common-lisp::cons 0 256
        *fn-bpc-max-uint* -1 (- *fn-bpc-max-uint*) #\A "" "body"
        '(0 128 255) '(0 1 . 2) '((3 4) "longer") *bprc-ck*)))

; Reach every turn from the actual generator, checking literal antecedent
; and all three clauses of the exact residual keystone at every turn.
(defun bprc-test-tracep (tasks fuel)
  (declare (xargs :measure (nfix fuel)
                  :hints (("Goal" :in-theory
                           (disable fn-bpnrc-tasks-validp fn-bpnrc-residual fn-bpnrc-step)))))
  (if (zp (nfix fuel)) nil
    (let ((answer (fn-bpnrc-step tasks)))
      (and (fn-bpnrc-tasks-validp tasks)
           (member-equal (fn-bpn-nth 0 answer) '(:continue :done))
           (equal (fn-bpnrc-residual tasks)
                  (append (fn-bpn-nth 1 answer)
                          (fn-bpnrc-residual (fn-bpn-nth 2 answer))))
           (fn-bpnrc-tasks-validp (fn-bpn-nth 2 answer))
           (or (equal (fn-bpn-nth 0 answer) :done)
               (bprc-test-tracep (fn-bpn-nth 2 answer) (1- (nfix fuel))))))))
(assert-event
 (and (consp (fn-bpnrc-residual (fn-bpnrc-begin *bprc-ck* 64)))
      (bprc-test-tracep (fn-bpnrc-begin *bprc-ck* 64) 2048)))

; Corrupted-state removal checks omitted invariant false and the literal
; keystone conclusion false (a value claims an exhausted depth budget).
(assert-event
 (let* ((tasks (list (list :value :keyword 0)))
        (answer (fn-bpnrc-step tasks)))
   (and (not (fn-bpnrc-tasks-validp tasks))
        (not (and (member-equal (fn-bpn-nth 0 answer) '(:continue :done))
                  (equal (fn-bpnrc-residual tasks)
                         (append (fn-bpn-nth 1 answer)
                                 (fn-bpnrc-residual (fn-bpn-nth 2 answer))))
                  (fn-bpnrc-tasks-validp (fn-bpn-nth 2 answer)))))))

; Literal quantum positive, with a nonempty accumulator and payload.
(assert-event
 (let* ((tasks (fn-bpnrc-begin *bprc-ck* 64)) (acc '(222 221))
        (answer (fn-bpnrc-run tasks 7 acc)))
   (and (fn-bpnrc-tasks-validp tasks)
        (consp (fn-bpn-nth 1 answer))
        (equal (fn-bpn-nth 0 answer) :yield)
        (member-equal (fn-bpn-nth 0 answer) '(:yield :done))
        (equal (append (fn-bpn-nth 1 answer)
                       (fn-bpnrc-residual (fn-bpn-nth 2 answer)))
               (append (fn-ag-rev-onto acc nil) (fn-bpnrc-residual tasks)))
        (fn-bpnrc-tasks-validp (fn-bpn-nth 2 answer)))))
(assert-event
 (let* ((tasks (fn-bpnrc-begin *bprc-ck* 64))
        (answer (fn-bpnrc-census-run tasks 7 17)))
   (and (fn-bpnrc-tasks-validp tasks)
        (< 17 (fn-bpn-nth 1 answer))
        (member-equal (fn-bpn-nth 0 answer) '(:yield :done))
        (equal (+ (fn-bpn-nth 1 answer)
                  (len (fn-bpnrc-residual (fn-bpn-nth 2 answer))))
               (+ 17 (len (fn-bpnrc-residual tasks))))
        (fn-bpnrc-tasks-validp (fn-bpn-nth 2 answer)))))

; Exact width boundary is reached, not merely a zero-byte turn.
(assert-event
 (let ((answer (fn-bpnrc-step (fn-bpnrc-begin *fn-bpc-max-uint* 1))))
   (and (equal (len (fn-bpn-nth 1 answer)) 9)
        (<= (len (fn-bpn-nth 1 answer)) 9))))

; Literal hypothesis removal for both quantum and census: the omitted
; invariant is false and each complete conjunction fails by refusal.
(assert-event
 (let* ((tasks (fn-bpnrc-begin :keyword 0))
        (q (fn-bpnrc-run tasks 7 '(222)))
        (c (fn-bpnrc-census-run tasks 7 17)))
   (and (not (fn-bpnrc-tasks-validp tasks))
        (equal (fn-bpn-nth 0 q) :refused)
        (equal (fn-bpn-nth 0 c) :refused)
        (not (and (member-equal (fn-bpn-nth 0 q) '(:yield :done))
                  (equal (append (fn-bpn-nth 1 q)
                                 (fn-bpnrc-residual (fn-bpn-nth 2 q)))
                         (append '(222) (fn-bpnrc-residual tasks)))
                  (fn-bpnrc-tasks-validp (fn-bpn-nth 2 q))))
        (not (and (member-equal (fn-bpn-nth 0 c) '(:yield :done))
                  (equal (+ (fn-bpn-nth 1 c)
                            (len (fn-bpnrc-residual (fn-bpn-nth 2 c))))
                         (+ 17 (len (fn-bpnrc-residual tasks))))
                  (fn-bpnrc-tasks-validp (fn-bpn-nth 2 c)))))))

(defun bprc-test-resume (tasks quantum fuel acc)
  (declare (xargs :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bpnrc-run)))))
  (if (zp (nfix fuel)) (list :exhausted acc tasks)
    (let* ((answer (fn-bpnrc-run tasks quantum nil))
           (bytes (append acc (fn-bpn-nth 1 answer))))
      (if (equal (fn-bpn-nth 0 answer) :yield)
          (bprc-test-resume (fn-bpn-nth 2 answer) quantum (1- (nfix fuel)) bytes)
        (list (fn-bpn-nth 0 answer) bytes (fn-bpn-nth 2 answer))))))
(assert-event
 (let* ((tasks (fn-bpnrc-begin *bprc-ck* 64))
        (one (bprc-test-resume tasks 1 2048 nil))
        (seven (bprc-test-resume tasks 7 2048 nil)))
   (and (equal (car one) :done) (equal (car seven) :done)
        (equal (cadr one) (fn-bpnr-enc *bprc-ck* 64))
        (equal (cadr seven) (cadr one)))))

; Mutation witness: dropping one emitted octet breaks the exact sequence.
(assert-event
 (let* ((tasks (fn-bpnrc-begin *bprc-ck* 64))
        (answer (fn-bpnrc-run tasks 7 nil)))
   (and (fn-bpnrc-tasks-validp tasks)
        (consp (fn-bpn-nth 1 answer))
        (not (equal (fn-bpnrc-residual tasks)
                    (append (cdr (fn-bpn-nth 1 answer))
                            (fn-bpnrc-residual (fn-bpn-nth 2 answer))))))))
