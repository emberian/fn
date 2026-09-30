;;; DTN's limited live admin client.  It registers neither run nor post.
(in-package "ACL2")

(defun fnn-bpnc-status-unavailable (path kind)
  (declare (ignore path kind))
  (fnn-core 'fn-bpnc-status-unavailable))

(defun fnn-bpnc-status-tail (path kind)
  (declare (ignore path kind))
  nil)

(setq *fnn-operator-live-owner*
      (make-fnn-operator-live-owner
       :socket-present #'fnn-operator-live-socket-present
       :live-status #'fnn-bpnc-status-unavailable
       :status-tail #'fnn-bpnc-status-tail
       :admin-observe #'fnn-operator-live-admin-observe
       :admin #'fnn-operator-live-admin
       :request #'fnn-operator-live-request))
