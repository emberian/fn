; FNBS kind 18: one protected atomic family replacement decision.  Prior
; ordered kind-5 rows determine the exact active set; these bytes bind its
; anchor and the resulting whole wire without duplicating up to 64 identities.
(in-package "ACL2")
(include-book "bp-node-fragment-plan")
(include-book "bp-fnbs-codec")

(defconst *fn-bpnf-family-kind* 18)
(defconst *fn-bpnf-family-fields* '(:nat :nat :nat :nat :blob))

(defun fn-bpnf-family-record (epoch op anchor-arrival whole-arrival wire)
  (declare (xargs :guard t))
  (list :bpnf-family epoch op anchor-arrival whole-arrival wire))

(defun fn-bpnf-family-recordp (row)
  (declare (xargs :guard t))
  (and (true-listp row) (equal (len row) 6)
       (equal (car row) :bpnf-family)
       (fn-frame-natp (fn-bpn-nth 1 row))
       (fn-frame-natp (fn-bpn-nth 2 row))
       (fn-frame-natp (fn-bpn-nth 3 row))
       (fn-frame-natp (fn-bpn-nth 4 row))
       (fn-cbor-octet-listp (fn-bpn-nth 5 row))
       (consp (fn-bpn-nth 5 row))
       (<= (len (fn-bpn-nth 5 row)) *fn-bpnf-max-held-image*)))

(defun fn-bpnf-family-values (row)
  (declare (xargs :guard t))
  (list (fn-bpn-nth 1 row) (fn-bpn-nth 2 row) (fn-bpn-nth 3 row)
        (fn-bpn-nth 4 row) (fn-bpn-nth 5 row)))

(defun fn-bpnf-family-frame (row)
  (declare (xargs :guard t))
  (if (not (fn-bpnf-family-recordp row))
      :bad
    (let ((values (fn-bpnf-family-values row)))
      (if (not (fn-frame-values-okp *fn-bpnf-family-fields* values))
          :bad
        (let ((payload (fn-frame-fields-octets
                        *fn-bpnf-family-fields* values)))
          (if (not (and (fn-cbor-octet-listp payload)
                        (<= (len payload) *fn-bpn-lifecycle-max-payload*)))
              :bad
            (let ((protected (fn-frame-protected
                              *fn-frame-magic-bundle-store* *fn-frame-version*
                              *fn-bpnf-family-kind* payload)))
              (append protected (fn-frame-trailer protected)))))))))

(defun fn-bpnf-family-from-values (values)
  (declare (xargs :guard t))
  (let ((row (fn-bpnf-family-record
              (fn-bpn-nth 0 values) (fn-bpn-nth 1 values)
              (fn-bpn-nth 2 values) (fn-bpn-nth 3 values)
              (fn-bpn-nth 4 values))))
    (if (fn-bpnf-family-recordp row) row nil)))

(defun fn-bpnf-family-unframe (octets)
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
                    (equal (fn-frame-result-kind answer) *fn-bpnf-family-kind*)
                    (fn-cbor-octet-listp (fn-frame-result-payload answer))))
          nil
        (let ((parsed (fn-frame-fields-parse
                       *fn-bpnf-family-fields*
                       (fn-frame-result-payload answer))))
          (if (not (fn-frame-parse-okp parsed)) nil
            (let ((row (fn-bpnf-family-from-values
                        (fn-frame-parse-value parsed))))
              (if (equal (fn-bpnf-family-frame row) octets)
                  row nil))))))))
