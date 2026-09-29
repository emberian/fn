;;; Shared bounded credential-file I/O; no NNTP service machinery.
(in-package "ACL2")

(defun fnn-native-auth-read (path maximum)
  "Return OCTETS,PRESENTP; missing is the existing empty credential registry."
  (let ((info (fnn-lstat path)))
    (if (null info)
        (values nil nil)
      (progn
        (when (or (fnn-symlink-p info) (not (fnn-regular-p info)))
          (fnn-refuse "AUTHINFO credential path is not a regular file: ~a" path))
        (when (> (sb-posix:stat-size info) maximum)
          (fnn-refuse "AUTHINFO credential file exceeds ACL2 bound: ~a" path))
        (values (fnn-octet-list (fnn-read-regular-bounded path maximum)) t)))))
