; Replay the selected image's actual initialization and control trace.
; Disk Read octets remain external observations: this is NOT persisted-effect
; refinement or a proof that a successful fence tells the truth.
(in-package "ACL2")
(include-book "../sim/check-envelope")

(defun fn2-native-control-replay (profile boot trace)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (verdict caps fn2-core)
      (let ((fn2-core (fn2-init-executor profile :echo nil fn2-core)))
        (mv-let (code fn2-core) (fn2-boot-start (nth 1 boot) (nth 2 boot) fn2-core)
          (if (and (equal (car boot) :boot-start) (equal (len boot) 4)
                   (equal code :ok) (equal code (nth 3 boot)))
              (fn2-envelope-steps trace 0 t nil nil fn2-core)
            (mv :boot-start-mismatch nil fn2-core))))
      (list verdict caps))))

; The peer port is independently observed by the Python client, rather than
; taking the replay's capability index as an externally supplied identity.
(defun fn2-native-control-no-peer (port caps)
  (declare (xargs :verify-guards nil))
  (if (endp caps) t
    (and (not (equal port (nth 1 (cdar caps))))
         (fn2-native-control-no-peer port (cdr caps)))))

(defun fn2-native-control-peer (port sent received caps)
  (declare (xargs :verify-guards nil))
  (if (endp caps) nil
    (let ((c (cdar caps)))
      (if (equal port (nth 1 c))
          (and (equal sent (reverse (nth 2 c)))
               (fn2-envelope-output-matches-p (nth 8 c) received)
               (fn2-native-control-no-peer port (cdr caps)))
        (fn2-native-control-peer port sent received (cdr caps))))))

(assert-event
 (let ((caps '(((1 . 1) . (1 12001 (2 1) (4 3) nil nil nil nil ((:exact 3 4)))))))
  (and (fn2-native-control-peer 12001 '(1 2) '(3 4) caps)
       (not (fn2-native-control-peer 12002 '(1 2) '(3 4) caps))
       (not (fn2-native-control-peer 12001 '(9 2) '(3 4) caps))
       (not (fn2-native-control-peer 12001 '(1 2) '(9 4) caps))
       (not (fn2-native-control-peer 12001 '(1 2) '(3 4) (append caps caps))))))

; Consumed bytes cannot independently establish delivery. The same recorded
; prefix allows different observed receipts, but rejects bytes outside it.
(assert-event
 (let ((caps '(((1 . 1) . (1 12001 (2 1) (4 3) nil nil nil nil ((:prefix 3 4)))))))
  (and (fn2-native-control-peer 12001 '(1 2) nil caps)
       (fn2-native-control-peer 12001 '(1 2) '(3) caps)
       (not (fn2-native-control-peer 12001 '(1 2) '(4) caps)))))
