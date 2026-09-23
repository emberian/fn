; FNBS kind 7: a durable local application delivery result.  A kind-7 row
; names one exact earlier kind-5 held bundle by arrival and primary identity.
; Its optional detail is a committed receipt id for a successful request, or
; a bounded refusal reason.  It is never a TCPCL custody acknowledgement.
(in-package "ACL2")
(include-book "bp-fnbs-codec")

(defconst *fn-bpah-delivery-kind* 7)
(defconst *fn-bpah-delivery-fields* '(:nat :nat :nat :blob :nat :blob))

(defun fn-bpah-delivery-values (row)
  (declare (xargs :guard t))
  (list (fn-bpn-nth 1 row) (fn-bpn-nth 2 row) (fn-bpn-nth 3 row) (fn-bpn-nth 4 row)
        (fn-bpah-disposition-code (fn-bpn-nth 5 row)) (fn-bpn-nth 6 row)))

(defun fn-bpah-delivery-frame (row)
  (declare (xargs :guard t))
  (if (not (fn-bpah-delivery-recordp row))
      :bad
    (let ((values (fn-bpah-delivery-values row)))
      (if (not (fn-frame-values-okp *fn-bpah-delivery-fields* values))
          :bad
        (let ((payload (fn-frame-fields-octets
                        *fn-bpah-delivery-fields* values)))
          (if (not (and (fn-cbor-octet-listp payload)
                        (<= (len payload) *fn-bpn-lifecycle-max-payload*)))
              :bad
            (let ((protected (fn-frame-protected
                              *fn-frame-magic-bundle-store* *fn-frame-version*
                              *fn-bpah-delivery-kind* payload)))
              (append protected (fn-frame-trailer protected)))))))))

(defun fn-bpah-delivery-from-values (values)
  (declare (xargs :guard t))
  (let ((row (fn-bpah-delivery-record
              (fn-bpn-nth 0 values) (fn-bpn-nth 1 values) (fn-bpn-nth 2 values)
              (fn-bpn-nth 3 values) (fn-bpah-code-disposition (fn-bpn-nth 4 values))
              (fn-bpn-nth 5 values))))
    (if (fn-bpah-delivery-recordp row) row nil)))

(defun fn-bpah-delivery-unframe (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets)) nil
    (let ((answer (fn-frame-decode
                   octets
                   (fn-frame-trailer (fn-frame-protected-prefix octets))
                   *fn-bpn-lifecycle-max-payload*)))
      (if (not (and (fn-frame-result-okp answer)
                    (equal (fn-frame-result-magic answer)
                           *fn-frame-magic-bundle-store*)
                    (equal (fn-frame-result-version answer) *fn-frame-version*)
                    (equal (fn-frame-result-kind answer)
                           *fn-bpah-delivery-kind*)
                    (fn-cbor-octet-listp (fn-frame-result-payload answer))))
          nil
        (let ((parsed (fn-frame-fields-parse
                       *fn-bpah-delivery-fields*
                       (fn-frame-result-payload answer))))
          (if (not (fn-frame-parse-okp parsed))
              nil
            (let ((row (fn-bpah-delivery-from-values
                        (fn-frame-parse-value parsed))))
              (if (equal (fn-bpah-delivery-frame row) octets)
                  row nil))))))))

(defthm fn-bpah-disposition-code-inverts
  (implies (fn-bpah-disposition-code status)
           (equal (fn-bpah-code-disposition
                   (fn-bpah-disposition-code status))
                  status)))
