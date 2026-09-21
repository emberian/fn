;;; host/native/feed-filename.lisp -- raw filesystem boundary for FNFD names.
;;;
;;; ACL2 chooses and inverts every peer/component layout in
;;; books/feed-filename.lisp.  This file only moves its octet vectors across
;;; the native pathname boundary and refuses a malformed core result before
;;; passing it to a POSIX pathname primitive.

(in-package "ACL2")

(defun fnn-feed-filename-component-p (component)
  "A host output guard; it is not a peer-label parser or layout policy."
  (and (stringp component) (> (length component) 0)
       (not (member component '("." "..") :test #'string=))
       (not (find #\/ component))
       (not (find #\\ component))
       (not (find (code-char 0) component))))

(defun fnn-feed-filename-components (peer)
  "ACL2's component vector for PEER, rendered as host-safe ASCII strings."
  (let* ((peer-octets (fnn-octet-list (fnn-string-octets peer)))
         (ok (fnn-core 'fn-feed-filename-host-okp peer-octets)))
    (unless (eq ok t)
      (fnn-fault "ACL2 refused FNFD peer filename"))
    (let ((count (fnn-nat (fnn-core 'fn-feed-filename-host-count peer-octets)))
          (limit (fnn-nat (fnn-core 'fn-feed-filename-host-max-components))))
      (unless (and (> count 0) (<= count limit))
        (fnn-fault "ACL2 returned invalid FNFD component count"))
      (let ((components
              (loop for index below count
                    for octets = (fnn-core 'fn-feed-filename-host-component
                                            peer-octets index)
                    do (unless (fnn-octet-list-p octets)
                         (fnn-fault "ACL2 returned non-octet FNFD component"))
                    collect (fnn-octets-string (fnn-octets octets)))))
        (unless (every #'fnn-feed-filename-component-p components)
          (fnn-fault "ACL2 returned unsafe FNFD filename component"))
        components))))

(defun fnn-feed-filename-max-v1-chunks ()
  "The ACL2-owned depth bound used before raw directory recursion."
  (fnn-nat (fnn-core 'fn-feed-filename-host-max-v1-chunks)))

(defun fnn-feed-filename-decode-components (components)
  "Return PEER and T only for an ACL2-canonical component vector.

NIL/NIL means the vector is conflicting on-disk evidence.  The caller must
fault rather than skip it, so restart cannot silently discard a durable feed
obligation.
"
  (unless (and (listp components) (every #'fnn-feed-filename-component-p components))
    (return-from fnn-feed-filename-decode-components (values nil nil)))
  (let ((answer (fnn-core 'fn-feed-filename-host-decode
                          (mapcar (lambda (component)
                                    (fnn-octet-list (fnn-string-octets component)))
                                  components))))
    (if (or (eq answer :bad) (not (fnn-octet-list-p answer)))
        (values nil nil)
      (let ((peer (fnn-octets-string (fnn-octets answer))))
        (values peer t)))))
