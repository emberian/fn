; The measure's recorder (LEAN-METATHEORY section -1, item 3): run the A4 smoke's echo and
; scribe scenarios (fn2/tests/sim-layer-a-a4-smoke.lsp) with the child-form arm functions
; wrapped by record-arms.lisp, writing build/lean-meta/arms-record.sexp. Test-only I/O.
; Echo runs on the tiny profile with :trace (3 connections, seed 1234) rather than the smoke's
; concrete one: the concrete pool is 7 MB of bytes, which every recorded call would carry twice.
; Scribe runs exactly as the smoke runs it (its own 4 KiB-sector profile).
; Run from the worktree root after the simulator's books certify:
;   tools/acl2 --timeout 3600 < fn2/meta/emit/record-arms.lsp
(in-package "ACL2")
:q
(handler-case
    (progn
      (let ((process (sb-ext:run-program "python3" '("fn2/tests/scenario-revision.py")
                       :search t :output "build/scenario-revision.lsp"
                       :if-output-exists :supersede :error *error-output*)))
        (assert (eql (sb-ext:process-exit-code process) 0)))
      (multiple-value-bind (erp value state)
          (let ((*features* (adjoin :acl2-loop-only *features*)))
            (with-suppression
              (ld '((set-prover-step-limit 300000)
                    (set-cbd "fn2/tests/")
                    (ld "sim-layer-a.lisp" :ld-error-action :error)
                    (set-guard-checking nil)) :ld-error-action :error)))
        (declare (ignore state))
        (assert (and (not erp) (eq value :eof))))
      (load "fn2/meta/emit/record-arms.lisp")
      (ensure-directories-exist "build/lean-meta/")
      (meta-record-install "build/lean-meta/arms-record.sexp")
      (format t "~&META ECHO ~s~%" (car (fn2-sim-run-echo 1234 3 (put-assoc-equal :trace t *fn2-profile-tiny*))))
      (format t "~&META SCRIBE ~s~%" (car (fn2-sim-run-scribe)))
      (meta-record-finish)
      (format t "~&FN2-META-RECORD PASS~%")
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "FN2-META-RECORD FAILED: ~A~%" condition)
    (sb-ext:exit :code 1)))
