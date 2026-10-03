; Local client observation policy; never a durable acceptance decision.
(in-package "ACL2")

(defconst *fn-nco-reply-grace-seconds* 10)
(defconst *fn-nco-observation-octets-per-second* 65536)

(defun fn-nco-reply-seconds (request-octets)
  (declare (xargs :guard (natp request-octets)))
  (+ *fn-nco-reply-grace-seconds*
     (ceiling request-octets *fn-nco-observation-octets-per-second*)))
