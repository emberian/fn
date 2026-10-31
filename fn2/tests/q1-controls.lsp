; Q1's shared-handler controls (build/coordinator/fn2/lanes/a-dm4-q1-classification.md section 4):
; for each machine kind, one site of its generated handler is mutated and the kind's independent
; contract (fn2/tests/q1-contracts.lisp) is evaluated with every fn2-turn under TRACE per case
; (q1-case-hook.lsp's turn hook, the reference carried across the run's turns). Four runs per kind:
;   :baseline       unmutated               TRACE passes, the oracle passes
;   :shared         mutant on both cores    TRACE passes (the handler is shared), the oracle fails
;   :concrete-only  mutant on the concrete  TRACE fails where the site changes compared state
;   :restored       unmutated again         TRACE passes, the oracle passes
; Each run records TRACE's verdict, the oracle's, and how many times the mutant changed something
; on each core (a mutation that never ran proves nothing). The records go to
; fn2/tests/evidence/q1-controls.lisp; tests/q1-controls-check.lisp judges them per kind.
; Run from the repository root:
;   FN_ACL2=... tools/acl2 < fn2/tests/q1-controls.lsp > build/q1-controls.log
(in-package "ACL2")
(include-book "fn2/tests/q1-contracts")
(include-book "fn2/tests/q1-contracts-b")
(include-book "fn2/tests/q1-contracts-c")
(include-book "fn2/tests/q1-contracts-d")
(set-guard-checking nil)
:q
; The core whose sealer step is running (fn2-run-install takes the table, not the core).
(defvar *fn2-q1-sealer-core* nil)
(handler-case
    (progn
      (load "fn2/tests/own-read-hook.lsp")
      (load "fn2/tests/q1-case-hook.lsp")
      (let ((process (sb-ext:run-program "python3" '("fn2/tests/scenario-revision.py")
                       :search t :output "build/scenario-revision.lsp"
                       :if-output-exists :supersede :error *error-output*)))
        (assert (eql (sb-ext:process-exit-code process) 0)))
      (multiple-value-bind (erp value state)
          (let ((*features* (adjoin :acl2-loop-only *features*)))
            (with-suppression (ld '((ld "build/scenario-revision.lsp" :ld-error-action :error))
                                  :ld-error-action :error)))
        (declare (ignore state))
        (assert (and (not erp) (eq value :eof))))
      (let ((counts (list 0 0)) (mode :off) (records nil))
        (labels
            ((note (core)
               ; Count a change the mutant made, on the core it made it on.
               (if (eq core *fn2-q1-hook-ref*) (incf (second counts)) (incf (first counts))))
             (active (core)
               (or (eq mode :shared) (and (eq mode :concrete-only) (not (eq core *fn2-q1-hook-ref*)))))
             (mutate (name make)
               ; Replace NAME's definition by MAKE's wrapper of the original; return the restorer.
               (let ((original (symbol-function name)))
                 (setf (symbol-function name) (funcall make original))
                 (lambda () (setf (symbol-function name) original))))
             (run-kind (kind oracle name make)
               (let ((restore (mutate name make)))
                 (unwind-protect
                     (dolist (phase '(:baseline :shared :concrete-only :restored))
                       (setf mode (if (member phase '(:shared :concrete-only)) phase :off)
                             counts (list 0 0) *fn2-q1-hook-failures* nil
                             ; a monitor belongs to the run whose fn2-own-init made it
                             *fn2-q1-hook-monitor* nil)
                       ; An oracle that signals is :error, never :fail: a mutant that breaks the
                       ; run is not one the oracle caught (the judge refuses it).
                       (let* ((ok (handler-case (if (funcall oracle) :pass :fail)
                                    (cl:error (condition)
                                      (format t "Q1 CONTROL ~A ~A oracle error: ~A~%" kind phase condition)
                                      :error)))
                              (trace (if (find :trace *fn2-q1-hook-failures* :key #'second) :fail :pass)))
                         (format t "Q1 CONTROL ~A ~A trace=~A oracle=~A invocations(concrete reference)=~A~%"
                                 kind phase trace ok counts)
                         (push (list kind phase trace ok (first counts) (second counts)) records)))
                   (funcall restore) (setf mode :off)))))
          (fn2-q1-hook-install-turn)
          (unwind-protect
              (progn
                ; fn2-conn: the greeting is sent as 900 (its first TX octet becomes '9').
                (run-kind 'fn2-conn (lambda () (fn2-q1c-fixtures-ok *fn2-cu-fixtures* nil)) 'fn2-conn-run-greeting
                  (lambda (orig)
                    (lambda (refused posting mask tslot tgen id owner-gen core)
                      (multiple-value-bind (code after core) (funcall orig refused posting mask tslot tgen id owner-gen core)
                        (when (and (active core) (eq code :ok) (not (equal refused 1)))
                          (note core)
                          (fn2-core-write tslot tgen 0 57 *fn2-conn-kind* id owner-gen core))
                        (values code after core)))))
                ; fn2-echo: a receive starts its reply at offset 1, not 0 (its first octet is lost).
                (run-kind 'fn2-echo (lambda () (and (fn2-q1c-echo-ok '(72 69 76 76 79 13 10) nil)
                                                    (fn2-q1c-echo-random-ok 3 101)))
                  'fn2-echo-observe-receive
                  (lambda (orig)
                    (lambda (id event outcome reason count aux0 aux1 core)
                      (multiple-value-bind (wake core) (funcall orig id event outcome reason count aux0 aux1 core)
                        (when (and (active core) (equal (fn2-machine-phase id core) *fn2-echo-state-reply*)
                                   (equal (fn2-machine-off id core) 0))
                          (note core)
                          (setf core (fn2-machine-write-off id 1 core)))
                        (values wake core)))))
                ; fn2-listener: a refused booking records the principal as booked.
                (run-kind 'fn2-listener (lambda () (fn2-q1c-ledger-ok 1 *fn2-q1c-ledger-clients*)) 'fn2-listener-accept
                  (lambda (orig)
                    (lambda (id budget gen principal pending target core)
                      (multiple-value-bind (b s d r core) (funcall orig id budget gen principal pending target core)
                        (when (and (active core)
                                   (equal (fn2-machine-phase id core) *fn2-listener-state-admitting*)
                                   (equal (fn2-machine-account-ref id core) *fn2-none*)
                                   (fn2-machine-admission-books-p target))
                          (note core)
                          (setf core (fn2-machine-write-account-ref id principal core)))
                        (values b s d r core)))))
                ; fn2-upload: the hasher is fed one octet short at the start of each chunk (the
                ; octet is counted as hashed, so the upload goes on to its verdict as before).
                (run-kind 'fn2-upload
                  (lambda () (and (fn2-q1c-upload-ok (fn2-q1c-upload-case "valid") nil)
                                  (fn2-q1c-upload-ok (fn2-q1c-upload-case "valid-two-chunks") nil)
                                  (fn2-q1c-upload-ok (fn2-q1c-upload-case "subject-missing") nil)))
                  'fn2-upload-hash-step
                  (lambda (orig)
                    (lambda (row slot gen off len id ogen core)
                      (if (and (active core) (eql off 0) (integerp len) (< 1 len))
                          (multiple-value-bind (code consumed core) (funcall orig row slot gen 1 (- len 1) id ogen core)
                            (note core)
                            (values code (if (member code '(:ok :more)) (+ 1 consumed) consumed) core))
                        (funcall orig row slot gen off len id ogen core)))))
                ; fn2-recovery-machine: a presented witness never matches the recovered chain
                ; (the classification then reports a rollback where there is none).
                (run-kind 'fn2-recovery-machine
                  (lambda () (and (fn2-q1r-ok 0 t 0 '((:witness 1) (:rollback 1)))
                                  (fn2-q1r-ok 0 t 0 '((:witness 2)))))
                  'fn2-recovery-witness-match
                  (lambda (orig)
                    (lambda (witness chain arena core)
                      (multiple-value-bind (code matched) (funcall orig witness chain arena core)
                        (if (and (active core) matched)
                            (progn (note core) (values code nil))
                          (values code matched))))))
                ; fn2-sealer: the install step writes the groups run one entry short (its last
                ; entry is not counted, so the run leg no longer answers for it).
                (let ((step (symbol-function 'fn2-sealer-step)))
                  (setf (symbol-function 'fn2-sealer-step)
                        (lambda (budget core) (let ((*fn2-q1-sealer-core* core)) (funcall step budget core))))
                  (unwind-protect
                      (run-kind 'fn2-sealer (lambda () (fn2-q1s-ok *fn2-smu-groups*)) 'fn2-run-install
                        (lambda (orig)
                          (lambda (r schema run top slot gen unit counter entries okind oslot ogen table)
                            (let ((core *fn2-q1-sealer-core*))
                              (if (and core (active core) (eql schema 8) (integerp entries) (< 0 entries))
                                  (progn (note core)
                                         (funcall orig r schema run top slot gen unit counter (- entries 1) okind oslot ogen table))
                                (funcall orig r schema run top slot gen unit counter entries okind oslot ogen table))))))
                    (setf (symbol-function 'fn2-sealer-step) step)))
                ; fn2-txn: the identity decision answers a second content for a recorded Message-ID
                ; as stored (the transaction then goes on toward accepting it).
                (run-kind 'fn2-txn (lambda () (and (fn2-q1t-ok (fn2-q1t-case "conflict") nil)
                                                   (fn2-q1t-ok (fn2-q1t-case "xref-seeded") nil)))
                  'fn2-identity-step
                  (lambda (orig)
                    (lambda (d budget core)
                      (multiple-value-bind (answer core) (funcall orig d budget core)
                        (if (and (active core) (eq answer :conflict))
                            (progn (note core) (values :stored core))
                          (values answer core))))))
                ; fn2-scribe: the checksum the patch writes is off by one bit.
                (run-kind 'fn2-scribe (lambda () (fn2-q1c-scribe-ok 1001 2000)) 'fn2-scribe-patch-loop
                  (lambda (orig)
                    (lambda (left cursor hash slot gen id owner-gen core)
                      (if (and (active core) (eql cursor 0))
                          (progn (note core) (funcall orig left cursor (logxor hash 1) slot gen id owner-gen core))
                        (funcall orig left cursor hash slot gen id owner-gen core))))))
            (fn2-q1-hook-restore)))
        (with-open-file (out "fn2/tests/evidence/q1-controls.lisp" :direction :output :if-exists :supersede)
          (with-standard-io-syntax
            (let ((*package* (find-package "ACL2")) (*print-case* :downcase) (*print-pretty* nil))
              (format out "; Generated by fn2/tests/q1-controls.lsp. Do not edit.~%(in-package \"ACL2\")~%")
              (format out "(defconst *fn2-q1-controls-revision* ~S)~%"
                      (coerce *fn2-scenario-revision* '(simple-array character (*))))
              (format out "(defconst *fn2-q1-controls*~% '(~{~S~^~%   ~}))~%" (reverse records))))))
      (format t "Q1-CONTROLS WRITTEN~%")
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "Q1-CONTROLS FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
