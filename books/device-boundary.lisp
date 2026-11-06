; Physical device observations. No raw host decides short-I/O success,
; geometry, or whether a failed operation could have modified the image.
(in-package "ACL2")

(defun fn2-device-io-observation (result errno)
  (declare (xargs :guard t))
  (cond ((and (integerp result) (<= 0 result)) (mv :ok result))
        ((equal errno 28) (mv :no-space 0))
        (t (mv :failed 0))))

(defun fn2-device-open-observation (cap size backend)
  (declare (xargs :guard t))
  (if (and (natp cap) (unsigned-byte-p 63 size)
           (member-eq backend '(:fullfsync :fdatasync)))
      (mv :ok cap size backend)
    (mv :failed 0 0 :none)))

(assert-event (mv-let (code count) (fn2-device-io-observation -1 28)
                (and (equal code :no-space) (equal count 0))))
(assert-event (mv-let (code count) (fn2-device-io-observation -1 4)
                (and (equal code :failed) (equal count 0))))
(assert-event (mv-let (code count) (fn2-device-io-observation 17 0)
                (and (equal code :ok) (equal count 17))))
(assert-event (mv-let (code cap size backend) (fn2-device-open-observation 4 1048576 :fullfsync)
                (equal (list code cap size backend) '(:ok 4 1048576 :fullfsync))))
(assert-event (mv-let (code cap size backend) (fn2-device-open-observation 4 1048576 :memory)
                (equal (list code cap size backend) '(:failed 0 0 :none))))
