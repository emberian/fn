; Exact TCPCL wire admission and the native callback disposition for the
; finite BP machine.  The host observes octets and admitted provenance; ACL2
; parses, validates, and names the machine event and three-way result.
(in-package "ACL2")
(include-book "bp-node-foundation")
(include-book "bp-node-machine-guards")

(set-verify-guards-eagerness 0)

(defun fn-bpnf-initial-state (config max-held max-octets)
  (declare (xargs :guard t))
  (let ((base (fn-bpn-initial-machine-state config max-held max-octets)))
    (if base
        (fn-bpnf-state base nil nil nil nil nil nil 0 0)
      nil)))

(defun fn-bpnf-base-job-count (st)
  (declare (xargs :guard t))
  (len (fn-bpn-machine-state-jobs (fn-bpnf-base st))))

; The admitted principal comes from configured session admission.  The
; announced TCPCL peer EID remains a separate provenance field.
(defun fn-bpnf-tcpcl-ingress
  (st session-counter xfer-id peer-eid admitted-principal generation)
  (declare (xargs :guard t))
  (let ((ingress
         (list :cl (cons (fn-bpnf-epoch st) session-counter) xfer-id
               peer-eid admitted-principal generation)))
    (if (fn-bpnf-cl-ingressp ingress) ingress nil)))

(defun fn-bpnf-receive-wire-event (config wire observation ingress)
  (declare (xargs :guard t))
  (if (not (and (fn-bpn-configp config)
                (fn-clock-observationp observation)
                (fn-bpnf-cl-ingressp ingress)
                (fn-cbor-octet-listp wire)
                (fn-cbor-at-mostp wire *fn-bpnf-max-held-image*)))
      (list :refused :receive-boundary)
    (let* ((decision (fn-bpn-receive config wire observation))
           (bundle (fn-bpn-outcome-bundle decision)))
      (cond
       ((fn-bpn-refusedp decision)
        (list :refused (fn-bpn-outcome-reason decision)))
       ((fn-bpn-uncertainp decision)
        (list :uncertain (fn-bpn-outcome-reason decision)))
       ((and (fn-bpn-acceptedp decision)
               (fn-bpb-bundlep bundle)
               (equal wire (fn-bpb-encode bundle)))
        (list :ready (list :receive-bundle bundle wire ingress observation)))
       (t (list :refused :invalid-bundle))))))

(defun fn-bpnf-receive-wire-readyp (answer)
  (declare (xargs :guard t))
  (and (true-listp answer) (equal (len answer) 2)
       (equal (car answer) :ready)))

(defun fn-bpnf-receive-wire-event-value (answer)
  (declare (xargs :guard t))
  (fn-bpn-nth 1 answer))

(defun fn-bpnf-host-eventp (event)
  (declare (xargs :guard t))
  (cond
   ((equal (fn-cbor-ag-car event) :base)
    (and (true-listp event) (equal (len event) 2)
         (fn-bpn-machine-eventp (fn-bpn-nth 1 event))))
   ((equal (fn-cbor-ag-car event) :receive-bundle)
    (and (true-listp event) (equal (len event) 5)
         (fn-bpb-bundlep (fn-bpn-nth 1 event))
         (fn-cbor-octet-listp (fn-bpn-nth 2 event))
         (fn-cbor-at-mostp (fn-bpn-nth 2 event) *fn-bpnf-max-held-image*)
         (fn-bpnf-cl-ingressp (fn-bpn-nth 3 event))
         (fn-clock-observationp (fn-bpn-nth 4 event))))
   ((equal (fn-cbor-ag-car event) :persist-result)
    (and (true-listp event) (equal (len event) 4)
         (fn-frame-natp (fn-bpn-nth 1 event))
         (fn-frame-natp (fn-bpn-nth 2 event))
         (if (member-equal (fn-bpn-nth 3 event)
                           '(:durable :refused :uncertain))
             t nil)))
   ((equal (fn-cbor-ag-car event) :deliver)
    (and (true-listp event) (equal (len event) 3)
         (true-listp (fn-bpn-nth 1 event))
         (equal (len (fn-bpn-nth 1 event)) 2)
         (fn-bpp-eidp (fn-bpn-nth 2 event))))
   ((equal (fn-cbor-ag-car event) :deliver-result)
    (and (true-listp event) (equal (len event) 6)
         (fn-frame-natp (fn-bpn-nth 1 event))
         (fn-frame-natp (fn-bpn-nth 2 event))
         (true-listp (fn-bpn-nth 3 event))
         (equal (len (fn-bpn-nth 3 event)) 2)
         (if (or (equal (fn-bpn-nth 4 event) :uncertain)
                 (fn-bpah-disposition-code (fn-bpn-nth 4 event))) t nil)
         (fn-cbor-octet-listp (fn-bpn-nth 5 event))
         (<= (len (fn-bpn-nth 5 event)) 256)))
   ((equal (fn-cbor-ag-car event) :recover-fnbs)
    (and (true-listp event) (equal (len event) 5)
         (true-listp (fn-bpn-nth 2 event))
         (<= (len (fn-bpn-nth 2 event)) *fn-bpn-machine-max-records*)))
   (t nil)))

; Only the actual machine's final receive-answer can authorize the TCPCL
; callback disposition.  PATH is the host's physical publication path and is
; used only for a newly stored bundle, never for a duplicate.
(defun fn-bpnf-callback-result (effects ingress path)
  (declare (xargs :guard t))
  (let* ((effect (fn-bpn-nth 0 effects))
         (status (fn-bpn-nth 2 effect)))
    (if (not (and (consp effects) (null (cdr effects))
                  (equal (fn-cbor-ag-car effect) :receive-answer)
                  (equal (fn-bpn-nth 1 effect) ingress)))
        (list :uncertain :machine-answer)
      (cond ((equal status :stored) (list :accepted path))
            ((equal status :duplicate) (list :accepted nil))
            ((equal (fn-cbor-ag-car status) :refused)
             (list :refused (fn-bpn-nth 1 status)))
            ((equal (fn-cbor-ag-car status) :uncertain)
             (list :uncertain (fn-bpn-nth 1 status)))
            (t (list :refused status))))))

(defthm fn-bpnf-receive-wire-ready-has-exact-event
  (implies (fn-bpnf-receive-wire-readyp
            (fn-bpnf-receive-wire-event config wire observation ingress))
           (and (equal (fn-bpn-nth 2
                        (fn-bpnf-receive-wire-event-value
                         (fn-bpnf-receive-wire-event
                          config wire observation ingress)))
                       wire)
                (equal (fn-bpn-nth 3
                        (fn-bpnf-receive-wire-event-value
                         (fn-bpnf-receive-wire-event
                          config wire observation ingress)))
                       ingress)
                (equal (fn-bpn-nth 4
                        (fn-bpnf-receive-wire-event-value
                         (fn-bpnf-receive-wire-event
                          config wire observation ingress)))
                       observation)))
  :hints (("Goal" :in-theory (disable fn-bpn-receive fn-bpb-encode)))
  :rule-classes nil)

(verify-guards fn-bpnf-initial-state)
(verify-guards fn-bpnf-base-job-count)
(verify-guards fn-bpnf-tcpcl-ingress)
(verify-guards fn-bpnf-receive-wire-event)
(verify-guards fn-bpnf-receive-wire-readyp)
(verify-guards fn-bpnf-receive-wire-event-value)
(verify-guards fn-bpnf-host-eventp)
(verify-guards fn-bpnf-callback-result)
