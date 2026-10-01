(in-package "ACL2")
(include-book "../../books/recovery-profile-buffer")

; The actual fixed stobj, including its distinct overflow cell.
(defun fn-rpf-buffer-example ()
  (declare (xargs :guard t))
  (with-local-stobj fn-recovery-profile-buffer
    (mv-let (ok fn-recovery-profile-buffer)
      (let* ((fn-recovery-profile-buffer
              (update-fn-rpf-bytesi 0 70 fn-recovery-profile-buffer))
             (fn-recovery-profile-buffer
              (update-fn-rpf-bytesi 641 32 fn-recovery-profile-buffer))
             (fn-recovery-profile-buffer
              (update-fn-rpf-bytesi 642 255 fn-recovery-profile-buffer)))
        (mv (and (equal (fn-rpf-bytes-length fn-recovery-profile-buffer)
                        (nth 7 (fn-recovery-profile-envelope)))
                 (equal (fn-rpf-prefix 0 fn-recovery-profile-buffer) nil)
                 (equal (fn-rpf-prefix 1 fn-recovery-profile-buffer) '(70))
                 (equal (fn-rpf-prefix 642 fn-recovery-profile-buffer)
                        (append '(70) (make-list 640 :initial-element 0) '(32)))
                 (equal (len (fn-rpf-prefix 642 fn-recovery-profile-buffer)) 642)
                 (equal (nth 641 (fn-rpf-prefix 642 fn-recovery-profile-buffer)) 32)
                 (equal (fn-rpf-bytesi 642 fn-recovery-profile-buffer) 255))
            fn-recovery-profile-buffer))
      ok)))
(assert-event (fn-rpf-buffer-example))
