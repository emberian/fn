; Read-only projection of a retained kind-5 FNBS frame for native evidence.
; The host reads bounded octets; ACL2 validates the frame and extracts the ADU.
(in-package "ACL2")
(include-book "bp-fnbs-codec")

(set-verify-guards-eagerness 0)

(defun fn-bpnf-inspect-adu (frame)
  (declare (xargs :guard t))
  (let ((record (fn-bpnf-stored-record-unframe frame)))
    (if (fn-bpnf-stored-recordp record)
        (list :ready
              (fn-bpb-payload
               (fn-bpnf-held-bundle (fn-bpn-nth 3 record))))
      (list :fault :invalid-fnbs))))

(defun fn-bpnf-inspect-readyp (result)
  (declare (xargs :guard t))
  (and (true-listp result) (equal (len result) 2)
       (equal (car result) :ready)))

(defun fn-bpnf-inspect-value (result)
  (declare (xargs :guard t))
  (fn-bpn-nth 1 result))

(verify-guards fn-bpnf-inspect-readyp)
(verify-guards fn-bpnf-inspect-value)
