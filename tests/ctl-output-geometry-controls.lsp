; Execute the actual CTL selector with concrete child dimensions mocked at
; their readers. This tests its refusal boundary, not the generated core.
(load "tests/cns-drain-parent-controls.lsp")
(in-package "ACL2")
(defun nfix (x) (if (and (integerp x) (<= 0 x)) x 0))
(defun natp (x) (and (integerp x) (<= 0 x)))
(defmacro stobj-let (bindings names computation &body body)
 `(let ,bindings (multiple-value-bind ,names ,computation ,@body)))
(defun fn2-cns-snapshot-read-code (cns core) (declare (ignore core)) (if (= cns 2) :ok :bounds))
(defun fn2-ctl-snapshot-read-code (ctl core) (declare (ignore core)) (if (= ctl 1) :ok :bounds))
(defun fn2-machine-slot (ctl core) (declare (ignore ctl)) (getf core :slot 0))
(dolist (name '(fn2-ctl-table fn2-cns-table fn2-core-fc fn2-core-b3 fn2-core-fields fn2-core-cns-sources))
 (eval `(defun ,name (core) core)))
(loop for (name key default) in '((fn2-ctl-rows :connections 2) (fn2-cns-rows :sources 2)
                                 (fn2-fc-rows :formats 32) (fn2-b3-rows :hashers 32)
                                 (fn2-fields-rows :fields 4096) (fn2-cns-sources-rows :jobs 2))
 do (eval `(defun ,name (core) (getf core ,key ,default))))
(with-open-file (in "books/machines-b.lisp")
 (loop for form = (read in nil :end) until (eq form :end) do
  (when (and (consp form) (eq (car form) 'defun)
             (member (cadr form) '(fn2-b-ctl-runtime-row fn2-b-cns-replay-row fn2-b-cns-source-row fn2-b-cns-source-geometry-p)))
   (eval form))))
(eval (find-form (lambda (f) (and (eq (car f) 'defun) (eq (cadr f) 'fn2-ctl-fc-row))) *source-forms*))
(assert (equal (multiple-value-list (fn2-ctl-fc-row 1 '(:slot 0))) '(:ok 21)))
(assert (equal (multiple-value-list (fn2-ctl-fc-row 1 '(:slot 1))) '(:ok 22)))
; Different FC/B3 dimensions satisfy their individual bounds but alias the
; last CTL with source0. The composed selector must refuse that geometry.
(assert (= (fn2-b-ctl-runtime-row 1 2 2 32) (fn2-b-cns-source-row 0 2 29)))
(assert (equal (multiple-value-list (fn2-ctl-fc-row 1 '(:slot 1 :hashers 29))) '(:bounds 0)))
(assert (equal (multiple-value-list (fn2-ctl-fc-row 1 '(:slot 1 :fields 2688))) '(:bounds 0)))
(format t "CTL ACTUAL GEOMETRY SOURCE CONTROLS PASS: separate rows, mismatched-table alias refused, short stripe refused~%")

; Source-job dimensions, not just CNS capacity, drive source hash rows.
(assert (= (fn2-b-ctl-runtime-row 1 2 2 32) (fn2-b-cns-source-row 0 5 32)))
(assert (equal (multiple-value-list (fn2-ctl-fc-row 1 '(:slot 1 :jobs 5))) '(:bounds 0)))
(format t "CTL ACTUAL GEOMETRY SOURCE CONTROL PASS: source-job/CNS mismatch refused~%")

(eval (find-form (lambda (f) (and (eq (car f) 'defun) (eq (cadr f) 'fn2-cns-replay-row))) *source-forms*))
(assert (equal (multiple-value-list (fn2-cns-replay-row 2 '(:slot 0))) '(:ok 23)))
(assert (equal (multiple-value-list (fn2-cns-replay-row 2 '(:slot 1))) '(:ok 24)))
(assert (< (fn2-b-ctl-runtime-row 1 2 2 32) 23 24 (fn2-b-cns-source-row 0 2 32)))
(assert (equal (multiple-value-list (fn2-cns-replay-row 2 '(:slot 1 :hashers 29))) '(:unavailable 0)))
(assert (equal (multiple-value-list (fn2-cns-replay-row 2 '(:slot 1 :jobs 5))) '(:unavailable 0)))
(format t "CNS REPLAY GEOMETRY SOURCE CONTROLS PASS: separate rows, mismatched dimensions refused~%")
