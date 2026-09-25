; Scratch-only call counters (rep-wave-c lane), loaded at run time through
; FN_PROF_LOAD: each named function's fdefinition is wrapped to count its
; calls while *fnp-active* is set.  A name the image does not have is noted
; on stderr and skipped (the base image lacks the lane's new entries).
(in-package "ACL2")
(defun fnp-wrap (name)
  (let ((orig (fdefinition name)))
    (setf (fdefinition name)
          (lambda (&rest args)
            (when *fnp-active* (incf (gethash name *fnp-counts* 0)))
            (apply orig args)))))
(dolist (n '(fnn-octet-list fnn-octets-fill fnn-owner-attempt fnn-metadata
             fnn-metadata-buffer fnn-subject-id fnn-subject-id-buffer
             fnn-obligation-id fnn-trailer fnn-frame fnn-owner-handle-chunk
             fn-pbb-existing-action fn-owner-prepare-buffer
             fn-owner-existing-action-buffer fn-owner-chunk
             fn-store-subject-id-of-payload fn-store-subject-id-of-buffer
             fn-owner-subject-id-buffer fn-shb-subject-id fn-sha256-of-prefixed-buffer
             fn-sha256-stobj fn-sha256-of-string fn-octets$c-list))
  (if (fboundp n) (fnp-wrap n) (format *error-output* "fnp: ~(~a~) not fbound~%" n)))
(format *error-output* "fnp: counters installed~%")
