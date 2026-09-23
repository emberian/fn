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

; The native caller supplies the observed channel and the current durable
; configuration.  This theorem joins the external octets, the admission
; decision, and the exact typed provenance handed to the receive machine.
(defthm fn-bpaj-admitted-ingress-binds-announcement-and-selection
  (implies (equal (car (fn-bpaj-tcpcl-ingress-result
                        cfg st channel uri counter xfer)) :admitted)
           (let* ((eid (fn-bpaj-raw-announced-eid uri))
                  (selection (fn-bpaj-session-principal cfg channel eid))
                  (ingress (caddr (fn-bpaj-tcpcl-ingress-result
                                  cfg st channel uri counter xfer))))
             (and (fn-bpnf-cl-ingressp ingress)
                  (equal (fn-bpn-nth 1 ingress)
                         (cons (fn-bpnf-epoch st) counter))
                  (equal (fn-bpn-nth 2 ingress) xfer)
                  (equal (fn-bpn-nth 3 ingress) eid)
                  (equal (fn-bpn-nth 3 ingress)
                         (cons :dtn (nthcdr 4 uri)))
                  (equal (fn-bpnf-ingress-principal ingress)
                         (cadr selection))
                  (equal (fn-bpn-nth 5 ingress)
                         (caddr selection)))))
  :hints (("Goal" :in-theory (enable fn-bpaj-tcpcl-ingress-result
                                      fn-bpaj-raw-announced-eid
                                      fn-bpnf-tcpcl-ingress
                                      fn-bpnf-ingress-principal))))

; In particular a length-bound failure is decided before constructing any
; custody ingress.  The octet predicate covers non-octet external objects.
(defthm fn-bpaj-invalid-announcement-has-no-custody-ingress
  (implies (or (not (fn-cbor-at-mostp uri (+ 4 *fn-bpc-max-text*)))
               (not (fn-cbor-octet-listp uri)))
           (equal (fn-bpaj-tcpcl-ingress-result
                   cfg st channel uri counter xfer)
                  '(:refused :announced-eid nil)))
  :hints (("Goal" :in-theory (enable fn-bpaj-tcpcl-ingress-result
                                      fn-bpaj-raw-announced-eid))))

; A valid, typed custody ingress may still be anonymous.  Neither the
; announced EID nor a forged configured name can supply Store authority when
; selection from the observed channel/current config refused it.
(defthm fn-bpaj-refused-selection-cannot-grant-principal
  (implies (not (equal (car (fn-bpaj-session-principal
                             cfg channel (fn-bpaj-raw-announced-eid uri)))
                       :admitted))
           (let ((answer (fn-bpaj-tcpcl-ingress-result
                          cfg st channel uri counter xfer)))
             (and (not (equal (car answer) :admitted))
                  (equal (fn-bpnf-ingress-principal (caddr answer)) nil))))
  :hints (("Goal" :in-theory (enable fn-bpaj-tcpcl-ingress-result
                                      fn-bpnf-tcpcl-ingress
                                      fn-bpnf-ingress-principal))))

(defthm fn-bpaj-valid-untrusted-session-has-anonymous-custody
  (implies (and (fn-bpaj-raw-announced-eid uri)
                (fn-bpn-machine-u64p (fn-bpnf-epoch st))
                (fn-bpn-machine-u64p counter)
                (fn-bpn-machine-u64p xfer)
                (not (equal (car (fn-bpaj-session-principal
                                   cfg channel (fn-bpaj-raw-announced-eid uri)))
                            :admitted)))
           (let ((answer (fn-bpaj-tcpcl-ingress-result
                          cfg st channel uri counter xfer)))
             (and (equal (car answer) :refused)
                  (fn-bpnf-cl-ingressp (caddr answer))
                  (equal (fn-bpnf-ingress-principal (caddr answer)) nil))))
  :hints (("Goal" :in-theory (enable fn-bpaj-tcpcl-ingress-result
                                      fn-bpnf-tcpcl-ingress
                                      fn-bpnf-cl-ingressp
                                      fn-bpnf-ingress-principal))))
