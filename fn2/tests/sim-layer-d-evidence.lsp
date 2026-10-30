; Layer D's scenario (fn2/tests/sim-layer-d.lsp, read unchanged) under A4's
; instruments: every fn2-turn of every run is the per-case TRACE turn against
; the reference carried across the run's turns, with the own-read hook and
; OWN after it (q1-case-hook.lsp's turn hook). The driver's forms are read and evaluated in order,
; except that its closing (good-bye) is dropped and each verdict line
; (value-triple (cw "SIM-LAYER-D ..." X)) becomes an assertion that X is
; :pass, printed as before. When every verdict passed and no TRACE turn
; failed, the tallies are written to fn2/tests/evidence/q1-d-tally.lisp,
; which tests/q1-evidence.lisp adds to every Q1 case's evidence beside the
; A4 run's. Run from the repository root:
;   FN_ACL2=... tools/acl2 < fn2/tests/sim-layer-d-evidence.lsp > build/sim-layer-d-evidence.log
(in-package "ACL2")
:q
(handler-case
    (let* ((forms (with-open-file (in "fn2/tests/sim-layer-d.lsp")
                    (let ((*package* (find-package "ACL2")))
                      (loop for form = (read in nil :eof) until (eq form :eof) collect form))))
           (verdictp (lambda (form)
                       (and (consp form) (eq (car form) 'value-triple)
                            (consp (cadr form)) (eq (car (cadr form)) 'cw)
                            (stringp (cadr (cadr form)))
                            (eql 0 (search "SIM-LAYER-D " (cadr (cadr form)))))))
           (definitions (remove-if (lambda (form) (or (funcall verdictp form) (equal form '(good-bye)))) forms))
           (verdicts (loop for form in forms when (funcall verdictp form)
                           collect (destructuring-bind (fmt x) (cdr (cadr form))
                                     `(assert-event (let ((v ,x)) (prog2$ (cw ,fmt v) (eq v :pass)))))))
           ; Each verdict line's label and the expression it prints, for the run's domain.
           (domain (loop for form in forms when (funcall verdictp form)
                         collect (destructuring-bind (fmt x) (cdr (cadr form))
                                   (let ((*print-pretty* nil))
                                     ; a character string, never a base-string (printed readably as #A)
                                     (coerce (format nil "~A ~(~S~)" (subseq fmt 12 (search " ~x0" fmt)) x)
                                             '(simple-array character (*)))))))
           (run-ld (lambda (forms)
                           (multiple-value-bind (erp value state)
                               (let ((*features* (adjoin :acl2-loop-only *features*)))
                                 (with-suppression (ld forms :ld-error-action :error)))
                             (declare (ignore state))
                             (assert (and (not erp) (eq value :eof)))))))
      (assert (equal (car (last forms)) '(good-bye)))
      (assert (consp verdicts))
      (let ((process (sb-ext:run-program "python3" '("fn2/tests/scenario-revision.py")
                       :search t :output "build/scenario-revision.lsp"
                       :if-output-exists :supersede :error *error-output*)))
        (assert (eql (sb-ext:process-exit-code process) 0)))
      ; D's definitions (its set-cbd leaves the cbd at fn2/tests/).
      (funcall run-ld (append definitions
                                    '((include-book "../sim/check-trace")
                                      (include-book "../sim/check")
                                      (ld "../../build/scenario-revision.lsp" :ld-error-action :error))))
      (load "fn2/tests/own-read-hook.lsp")
      (load "fn2/tests/q1-case-hook.lsp")
      (fn2-own-hook-install)
      (fn2-q1-hook-install-turn)
      (unwind-protect (funcall run-ld verdicts)
        (fn2-q1-hook-restore)
        (fn2-own-hook-restore))
      (fn2-own-hook-report "SIM-LAYER-D")
      (format t "OWN CHECKS ~D~%" *fn2-q1-hook-own-checks*)
      (fn2-q1-hook-write "fn2/tests/evidence/q1-d-tally.lisp" "fn2/tests/sim-layer-d.lsp"
                         (coerce (format nil "D's sim-layer-d, every turn under TRACE per case and OWN: ~{~A~^; ~}" domain)
                                 '(simple-array character (*)))
                         '(:conn-wire :conn-wire-flood) "d")
      (format t "SIM-LAYER-D-EVIDENCE PASS~%")
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "SIM-LAYER-D-EVIDENCE FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
