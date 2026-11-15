;;; Test-owned capture and immutable image copies only. Load after certified
;;; sim/native-device-effects in the selected ACL2 image. No storage writes.
(in-package "ACL2")
; The joint control driver dynamically binds these exact parsed objects.
; Standalone use remains an image-only check, never a control/effect join.
(defvar *fn2-test-device-records*)
(defvar *fn2-test-device-fd*)
(let* ((*read-eval* nil)
       (records (if (boundp '*fn2-test-device-records*) *fn2-test-device-records*
                 (with-open-file (in (sb-ext:posix-getenv "FN2_TEST_DEVICE_EFFECTS"))
                  ;; An interrupted final form raises an error, never truncates
                  ;; the evidence to an apparently completed prefix.
                  (loop for row = (read in nil :end) until (eq row :end) collect row))))
       (first (find-if (lambda (r) (member (car r) '(:submit :direct))) records))
       (fd (if (boundp '*fn2-test-device-fd*) *fn2-test-device-fd* (car (third first)))))
  (assert first () "No physical device descriptor was captured")
  (multiple-value-bind (code effects) (fn2-native-device-effects records fd)
    (assert (eq code :ok) () "Malformed physical device trace")
    (with-open-file (before (sb-ext:posix-getenv "FN2_TEST_DEVICE_BEFORE")
                            :element-type '(unsigned-byte 8))
      (with-open-file (after (sb-ext:posix-getenv "FN2_TEST_DEVICE_AFTER")
                             :element-type '(unsigned-byte 8))
        (let ((before-size (file-length before)) (after-size (file-length after))
              (cursor 0)
              ;; Scratch bound, never an image-size bound. Process every byte.
              (a (make-array 65536 :element-type '(unsigned-byte 8)))
              (b (make-array 65536 :element-type '(unsigned-byte 8))))
          (loop for na = (read-sequence a before)
                for nb = (read-sequence b after)
                until (and (zerop na) (zerop nb))
                do (multiple-value-bind (verdict next)
                     (fn2-native-device-image-chunk effects before-size cursor cursor
                       (coerce (subseq a 0 na) 'list) (coerce (subseq b 0 nb) 'list))
                     (assert (eq verdict :ok) () "Device image/Read mismatch at ~d" cursor)
                     (setf cursor next)))
          (let ((verdict (fn2-native-device-image-finish effects before-size after-size cursor)))
            (assert (member verdict '(:exact-process-view :uncertain-effect-bound)))
            (format t "NATIVE DEVICE IMAGE ~s ~d bytes; Fence truth remains external~%" verdict cursor)
            (finish-output)))))))
