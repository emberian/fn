;;; Read only the test-owned capture/peer evidence; never served input.
(in-package "ACL2")
(let ((*read-eval* nil))
  (with-open-file (source (sb-ext:posix-getenv "FN2_TEST_CAPTURE"))
    (let* ((header (read source)) (boot (read source))
           (trace (loop for entry = (read source nil :end) until (eq entry :end) collect entry))
           (result
             (if (sb-ext:posix-getenv "FN2_TEST_DEVICE_EFFECTS")
                 (let* ((*fn2-test-device-records*
                          (with-open-file (in (sb-ext:posix-getenv "FN2_TEST_DEVICE_EFFECTS"))
                            (loop for row = (read in nil :end) until (eq row :end) collect row)))
                        (device
                          (with-open-file (in (sb-ext:posix-getenv "FN2_TEST_DEVICE_BACKEND"))
                            (let ((row (read in)))
                              (assert (eq (read in nil :end) :end)) row)))
                        (*fn2-test-device-fd* (second device)))
                   (declare (special *fn2-test-device-records* *fn2-test-device-fd*))
                   (assert (and (eq (first device) :device) (= (length device) 3)))
                   (let ((bound (fn2-native-device-control-replay
                                  (cadr header) boot trace *fn2-test-device-records*
                                  *fn2-test-device-fd* (third device))))
                     (assert (eq (car bound) :pass) () "Device/control join refused: ~s" (car bound))
                     ;; Consumer uses these same dynamically bound records/fd.
                     (load "tests/native-device-effects-raw.lsp")
                     bound))
               (fn2-native-control-replay (cadr header) boot trace))))
      (assert (and (eq (car header) :profile) (= (length header) 2)))
      (assert (eq (car result) :pass) () "Replay refused: ~s" (car result))
      (with-open-file (peer (sb-ext:posix-getenv "FN2_TEST_PEER"))
        (let ((evidence (read peer)))
          (assert (eq (read peer nil :end) :end))
          (assert (fn2-native-control-peer (car evidence) (cadr evidence) (caddr evidence) (cadr result)))
          ;; A changed peer byte must fail the same comparison.
          (assert (not (fn2-native-control-peer (car evidence) (cadr evidence)
                         (cons (mod (1+ (car (caddr evidence))) 256) (cdr (caddr evidence))) (cadr result))))
          (assert (not (fn2-native-control-peer (car evidence)
                         (cons (mod (1+ (caadr evidence)) 256) (cdadr evidence))
                         (caddr evidence) (cadr result))))))
      (format t "NATIVE CONTROL REPLAY PASS ~d events; disk effects not established~%" (length trace)))))
