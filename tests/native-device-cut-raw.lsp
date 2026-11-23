;;; Load after certified sim/native-device-cut in the current selected image.
;;; Test-owned evidence only. Original before/after images must be immutable
;;; copies from the same run; selected-image/source binding is a campaign duty.
(in-package "ACL2")
(defvar *fn2-test-device-records*)
(defvar *fn2-test-device-fd*)
(let* ((*read-eval* nil)
       (capture (with-open-file (in (sb-ext:posix-getenv "FN2_TEST_DEVICE_EFFECTS"))
                  (loop for row = (read in nil :end) until (eq row :end) collect row)))
       (backend (cond ((equal (sb-ext:posix-getenv "FN2_TEST_DEVICE_BACKEND") "fdatasync") :fdatasync)
                      ((equal (sb-ext:posix-getenv "FN2_TEST_DEVICE_BACKEND") "fullfsync") :fullfsync)
                      (t (error "Selected device backend missing")))))
  (multiple-value-bind (code trace records cut) (fn2-nde-cut-prefix (cddr capture) 0 nil nil)
    (declare (ignore trace))
    (assert (eq code :ok) () "Missing, malformed or nonterminal selected cut")
    ;; An empty physical prefix (first device-submit) supplies the descriptor
    ;; fd from the campaign, not a fabricated physical return.
    (let* ((first (find-if (lambda (r) (eq (car r) :submit)) records))
           (*fn2-test-device-records* records)
           (*fn2-test-device-fd* (if first (car (third first))
                                  (parse-integer (or (sb-ext:posix-getenv "FN2_TEST_DEVICE_FD")
                                                     (error "Empty prefix needs actual fd")))))
           (replayed (fn2-native-device-cut-replay capture *fn2-test-device-fd* backend)))
      (assert (eq (car replayed) :pass) () "Actual cut/control/physical replay refused: ~s" replayed)
      ;; Whole image comparison uses the same physical records, not a second
      ;; parse or a label-only successful result. The shared model distinguishes
      ;; exact process effects from unresolved in-flight/error Write bounds.
      (load "tests/native-device-effects-raw.lsp")
      (format t "NATIVE DEVICE CUT ordinal=~d label=~s position=~s replay=PASS~%"
              (second cut) (third cut) (second replayed))
      (finish-output))))
