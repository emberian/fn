; One executable ACL2 boundary for a TCPCL session's announced octets,
; observed socket address, durable peer configuration, and FNBS ingress.
; A refused trust profile still yields a typed anonymous ingress so custody
; remains distinct from Store/receipt authority.  A malformed announced EID
; yields no ingress and therefore no custody event.
(in-package "ACL2")
(include-book "bp-session-admission")
(include-book "bp-node-receive-boundary")
(set-verify-guards-eagerness 0)

(defun fn-bpaj-raw-announced-eid (uri)
  (declare (xargs :guard t))
  (if (and (fn-cbor-at-mostp uri (+ 4 *fn-bpc-max-text*))
           (fn-cbor-octet-listp uri)
           (equal (nth 0 uri) 100)      ; d
           (equal (nth 1 uri) 116)      ; t
           (equal (nth 2 uri) 110)      ; n
           (equal (nth 3 uri) 58))      ; :
      (let ((eid (cons :dtn (nthcdr 4 uri))))
        (if (fn-bpp-eidp eid) eid nil))
    nil))

; (:admitted nil ingress), (:refused reason anonymous-ingress), or
; (:refused :announced-eid nil) for malformed external EID bytes.
(defun fn-bpaj-tcpcl-ingress-result
    (cfg st channel announced-uri session-counter xfer-id)
  (declare (xargs :guard t))
  (let ((eid (fn-bpaj-raw-announced-eid announced-uri)))
    (if (not eid) (list :refused :announced-eid nil)
      (let* ((admission (fn-bpaj-session-principal cfg channel eid))
             (admitted (equal (car admission) :admitted))
             (principal (if admitted (cadr admission) nil))
             (generation (if admitted (caddr admission) 0))
             (ingress (fn-bpnf-tcpcl-ingress
                       st session-counter xfer-id eid
                       principal generation)))
        (if (not ingress) (list :refused :ingress-shape nil)
          (if admitted (list :admitted nil ingress)
            (list :refused (cadr admission) ingress)))))))

(verify-guards fn-bpaj-raw-announced-eid)
(verify-guards fn-bpaj-tcpcl-ingress-result)
