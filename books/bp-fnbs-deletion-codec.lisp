; FNBS kind 10: exact protected deletion of one previously held carrier.
; This records a witnessed lifecycle decision, not application release.
(in-package "ACL2")
(include-book "bp-report-deletion")
(include-book "bp-fnbs-codec")
(set-verify-guards-eagerness 0)

(defconst *fn-bpnf-delete-kind* 10)
(defconst *fn-bpnf-delete-fields* '(:nat :nat :nat :blob :nat))

(defun fn-bpnf-delete-values (record)
  (declare (xargs :guard t))
  (list (fn-bpn-nth 1 record) (fn-bpn-nth 2 record)
        (fn-bpn-nth 3 record) (fn-bpn-nth 4 record) 1))

(defun fn-bpnf-delete-frame (record)
  (declare (xargs :guard t))
  (if (not (fn-bpn-report-delete-recordp record))
      :bad
    (let ((values (fn-bpnf-delete-values record)))
      (if (not (fn-frame-values-okp *fn-bpnf-delete-fields* values))
          :bad
        (let ((payload (fn-frame-fields-octets
                        *fn-bpnf-delete-fields* values)))
          (if (not (and (fn-cbor-octet-listp payload)
                        (<= (len payload) *fn-bpn-lifecycle-max-payload*)))
              :bad
            (let ((protected (fn-frame-protected
                              *fn-frame-magic-bundle-store*
                              *fn-frame-version* *fn-bpnf-delete-kind*
                              payload)))
              (append protected (fn-frame-trailer protected)))))))))

(defun fn-bpnf-delete-from-values (values)
  (declare (xargs :guard t))
  (let ((record (fn-bpn-report-delete-record
                 (fn-bpn-nth 0 values) (fn-bpn-nth 1 values)
                 (fn-bpn-nth 2 values) (fn-bpn-nth 3 values)
                 :lifetime-expired)))
    (if (and (equal (fn-bpn-nth 4 values) 1)
             (fn-bpn-report-delete-recordp record))
        record nil)))

(defun fn-bpnf-delete-unframe (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets)) nil
    (let ((answer (fn-frame-decode
                   octets
                   (fn-frame-trailer (fn-frame-protected-prefix octets))
                   *fn-bpn-lifecycle-max-payload*)))
      (if (not (and (fn-frame-result-okp answer)
                    (equal (fn-frame-result-magic answer)
                           *fn-frame-magic-bundle-store*)
                    (equal (fn-frame-result-version answer)
                           *fn-frame-version*)
                    (equal (fn-frame-result-kind answer)
                           *fn-bpnf-delete-kind*)
                    (fn-cbor-octet-listp
                     (fn-frame-result-payload answer))))
          nil
        (let ((parsed (fn-frame-fields-parse
                       *fn-bpnf-delete-fields*
                       (fn-frame-result-payload answer))))
          (if (not (fn-frame-parse-okp parsed)) nil
            (let ((record (fn-bpnf-delete-from-values
                           (fn-frame-parse-value parsed))))
              (if (equal (fn-bpnf-delete-frame record) octets)
                  record nil))))))))
