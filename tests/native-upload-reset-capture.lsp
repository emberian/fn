; Test-only observation of the actual rolling reset call. This file changes no
; admission or storage state; the original function is called exactly once.
(in-package "ACL2")
(dolist (name '(fn2-upload-stream-reset fn2-upload-snapshot-read-code fn2-machine-generation
                fn2-upload-row-conn fn2-upload-row-conn-gen fn2-upload-row-request
                fn2-upload-row-op fn2-upload-row-stream-resets))
 (unless (fboundp name) (error "Missing actual rolling function ~s" name)))
(defvar *fn2-test-reset-original* (symbol-function 'fn2-upload-stream-reset))
(defun fn2-test-reset-snapshot (id gen core)
 (when (and (eq (fn2-upload-snapshot-read-code id core) :ok)
            (equal (fn2-machine-generation id core) gen))
  (list id gen (fn2-upload-row-conn id core) (fn2-upload-row-conn-gen id core)
        (fn2-upload-row-request id core) (fn2-upload-row-op id core)
        (fn2-upload-row-stream-resets id core))))
(setf (symbol-function 'fn2-upload-stream-reset)
 (lambda (id gen core)
  (let* ((before (fn2-test-reset-snapshot id gen core))
         (returned (multiple-value-list (funcall *fn2-test-reset-original* id gen core)))
         (after (and (second returned) (fn2-test-reset-snapshot id gen (second returned))))
         (path (or (sb-ext:posix-getenv "FN2_TEST_UPLOAD_RESETS")
                   (error "Missing reset evidence path"))))
   (with-open-file (out path :direction :output :if-exists :append :if-does-not-exist :create)
    (if (and before after)
        (format out "{~s:~s,~s:[~{~d~^,~}],~s:[~{~d~^,~}]}~%"
                "result" (symbol-name (first returned)) "before" before "after" after)
      (format out "{~s:false}~%" "valid"))
    (finish-output out))
   (values-list returned))))
