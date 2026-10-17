;;; Replay a trace inside the ACL2 developer image itself (no export): the
;;; same harness calls ACL2's own executable counterparts -- the matched
;;; baseline for the export's timings, and a determinism check of the image.
(in-package "ACL2")
(declaim (optimize (safety 3)))
(load (concatenate (quote string) (sb-ext:posix-getenv "RF_HERE") "serial.lisp"))
(defparameter *rf-user-stobj-alist* (user-stobj-alist *the-live-state*))
(load (concatenate (quote string) (sb-ext:posix-getenv "RF_HERE") "replay.lisp"))
;; the extent realizer: the image's own (host/native/extent.lisp) is keyed by
;; the ids its open registers; the replay registers the traced paths.
(defun rp-extent-registered (id path)
  (setf (gethash id *fnn-extent-fds*) (fnn-open path (logior sb-posix:o-rdonly +fnn-o-nofollow+))
        (gethash id *fnn-extent-paths*) path))
(sb-ext:gc :full t)
(format t "~&RP-LOADED rss-kib ~a dynamic ~,1f MiB~%" (rp-rss-kib) (/ (sb-kernel:dynamic-usage) 1048576.0))
(let ((tr (sb-ext:posix-getenv "RF_TRACE")))
  ;; first pass over the file for extents only is folded into rp-replay's
  ;; :extent handling; register lazily before each call instead
  (rp-replay tr :report 5))
(sb-ext:gc :full t)
(format t "~&RP-END rss-kib ~a dynamic ~,1f MiB~%" (rp-rss-kib) (/ (sb-kernel:dynamic-usage) 1048576.0))
