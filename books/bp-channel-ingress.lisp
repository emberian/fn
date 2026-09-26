; One executable ACL2 boundary for a TCPCL session's announced octets,
; observed socket address, durable peer configuration, and FNBS ingress.
; A refused trust profile still yields a typed anonymous ingress (the
; provenance a refusal is reported with), but D23 binds carriage to the
; admitted channel's actual policy: `fn-bpaj-admitted-receive-event', the
; receive decision the host calls, refuses custody of every bundle whose
; channel admission was refused (PRF-128).  A malformed announced EID yields
; no ingress and therefore no custody event.
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

; The theorems below name the selection by its call and never need its body.
; The rules concluding `true-listp' (or `consp') from a recognizer backchain
; into those recognizers on every list hypothesis here and never apply.
(local (in-theory (disable fn-bpaj-session-principal
                           fn-nntp-response-text-true-listp
                           fn-cp-idp-true-listp
                           fn-bpp-dtn-sspp-has-a-name-delimiter
                           fn-bpp-vchar-listp-implies-true-listp
                           fn-bpb-block-listp-implies-true-listp
                           fn-nntp-article-idp-is-consp)))

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

;; ---------------------------------------------------------------------------
;; PRF-128 (D23: carriage is bound to the admitted channel's actual policy).
;; host/native/bp-service.lisp `fnn-bps-receive' calls
;; `fn-bpaj-admitted-receive-event' with ADMISSION, the answer
;; `fn-owner-bp-tcpcl-ingress' (host/bp-native-app-host.lisp) gave for this
;; transfer, i.e. `fn-bpaj-tcpcl-ingress-result' over the live owner
;; configuration.  Only a :ready answer becomes the :receive-bundle event the
;; host hands `fnn-bps-foundation-step'; anything else is returned to the
;; convergence layer as a refusal before any FNBS step, so a refused channel
;; leaves no kind-5 custody row, hence no forwarding job, no :attempting
;; record, no fragment family and no owed receipt.  An admitted channel is
;; decided exactly as before, under the admitted ingress.
;; A nil ADMISSION (no owner or no observed channel) has no ingress, which
;; `fn-bpnf-receive-wire-event' refuses as :receive-boundary, as it did.

(defun fn-bpaj-channel-refusal-reason (admission)
  (declare (xargs :guard t))
  (let ((r (fn-bpn-nth 1 admission)))
    (if (and r (symbolp r)) r :channel)))

(defun fn-bpaj-admitted-receive-event (admission config wire observation)
  (declare (xargs :guard t))
  (if (equal (fn-cbor-ag-car admission) :refused)
      (list :refused (fn-bpaj-channel-refusal-reason admission))
    (fn-bpnf-receive-wire-event config wire observation
                                (fn-bpn-nth 2 admission))))

(verify-guards fn-bpaj-channel-refusal-reason)
(verify-guards fn-bpaj-admitted-receive-event)

(local (defthm fn-bpaj-tcpcl-ingress-result-is-admitted-or-refused
  (or (equal (car (fn-bpaj-tcpcl-ingress-result
                   cfg st channel uri counter xfer)) :admitted)
      (equal (car (fn-bpaj-tcpcl-ingress-result
                   cfg st channel uri counter xfer)) :refused))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bpaj-tcpcl-ingress-result)))))

; KEYSTONE (PRF-128): a bundle arriving over a channel whose admission verdict
; is not :admitted is refused with the verdict's own reason and is never a
; :ready receive event, so the host takes no custody of it.
(defthm fn-bpaj-refused-channel-takes-no-custody
  (let* ((admission (fn-bpaj-tcpcl-ingress-result
                     cfg st channel uri counter xfer))
         (answer (fn-bpaj-admitted-receive-event
                  admission config wire observation)))
    (implies (not (equal (car admission) :admitted))
             (and (equal answer
                         (list :refused
                               (fn-bpaj-channel-refusal-reason admission)))
                  (not (fn-bpnf-receive-wire-readyp answer)))))
  :hints (("Goal" :use fn-bpaj-tcpcl-ingress-result-is-admitted-or-refused
           :in-theory (e/d (fn-bpaj-admitted-receive-event fn-cbor-ag-car
                            fn-bpnf-receive-wire-readyp)
                           (fn-bpaj-tcpcl-ingress-result
                            fn-bpaj-channel-refusal-reason)))))

(local (defthm fn-bpaj-bpn-nth-2-is-caddr
  (equal (fn-bpn-nth 2 x) (caddr x))
  :hints (("Goal" :expand ((fn-bpn-nth 2 x) (fn-bpn-nth 1 (cdr x))
                           (fn-bpn-nth 0 (cddr x)))
           :in-theory (enable fn-cbor-ag-car)))))

; KEYSTONE (PRF-128, the admitted half): an admitted channel's bundle is
; decided by the unchanged receive boundary under the admitted ingress, whose
; principal is the policy's selection
; (fn-bpaj-admitted-ingress-binds-announcement-and-selection).
(defthm fn-bpaj-admitted-channel-receives-under-its-ingress
  (let ((admission (fn-bpaj-tcpcl-ingress-result
                    cfg st channel uri counter xfer)))
    (implies (equal (car admission) :admitted)
             (equal (fn-bpaj-admitted-receive-event
                     admission config wire observation)
                    (fn-bpnf-receive-wire-event
                     config wire observation (caddr admission)))))
  :hints (("Goal" :in-theory (e/d (fn-bpaj-admitted-receive-event
                                   fn-cbor-ag-car)
                                  (fn-bpaj-tcpcl-ingress-result
                                   fn-bpnf-receive-wire-event
                                   fn-bpn-nth)))))
