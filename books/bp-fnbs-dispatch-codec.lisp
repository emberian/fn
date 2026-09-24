; Logical FNBS dispatch kind 6 uses frame version 2.  The existing durable
; clock-domain marker uses kind 6 at version 1 under clock-domain.fnb; neither
; decoder accepts the other's version, and received rows use epoch-op names.
(in-package "ACL2")
(include-book "bp-fnbs-codec")
(set-verify-guards-eagerness 0)

(defconst *fn-bpnp-dispatch-kind* 6)
(defconst *fn-bpnp-dispatch-frame-version* 2)
(defconst *fn-bpnp-dispatch-fields* '(:nat :nat :nat :blob :blob))

(defun fn-bpnp-dispatch-record (epoch op arrival identity peer)
  (declare (xargs :guard t))
  (list :bpnf-dispatched epoch op arrival identity peer))

(defun fn-bpnp-dispatch-recordp (row)
  (declare (xargs :guard t))
  (and (true-listp row) (equal (len row) 6)
       (equal (car row) :bpnf-dispatched)
       (fn-frame-natp (fn-bpn-nth 1 row))
       (fn-frame-natp (fn-bpn-nth 2 row))
       (fn-frame-natp (fn-bpn-nth 3 row))
       (fn-cbor-octet-listp (fn-bpn-nth 4 row))
       (consp (fn-bpn-nth 4 row))
       (<= (len (fn-bpn-nth 4 row)) 1024)
       (fn-bpp-eidp (fn-bpn-nth 5 row))))

(defun fn-bpnp-dispatch-values (row)
  (declare (xargs :guard t))
  (list (fn-bpn-nth 1 row) (fn-bpn-nth 2 row)
        (fn-bpn-nth 3 row) (fn-bpn-nth 4 row)
        (if (fn-bpp-eidp (fn-bpn-nth 5 row))
            (fn-bpn-peer-octets (fn-bpn-nth 5 row))
          nil)))

(defun fn-bpnp-dispatch-frame (row)
  (declare (xargs :guard t))
  (if (not (fn-bpnp-dispatch-recordp row)) :bad
    (let ((values (fn-bpnp-dispatch-values row)))
      (if (not (fn-frame-values-okp *fn-bpnp-dispatch-fields* values)) :bad
        (let ((payload (fn-frame-fields-octets
                        *fn-bpnp-dispatch-fields* values)))
          (if (not (and (fn-cbor-octet-listp payload)
                        (<= (len payload) *fn-bpn-lifecycle-max-payload*)))
              :bad
            (let ((protected
                   (fn-frame-protected
                    *fn-frame-magic-bundle-store*
                    *fn-bpnp-dispatch-frame-version*
                    *fn-bpnp-dispatch-kind* payload)))
              (append protected (fn-frame-trailer protected)))))))))

(defun fn-bpnp-dispatch-from-values (values)
  (declare (xargs :guard t))
  (let ((row (fn-bpnp-dispatch-record
              (fn-bpn-nth 0 values) (fn-bpn-nth 1 values)
              (fn-bpn-nth 2 values) (fn-bpn-nth 3 values)
              (fn-bpn-peer-from-octets (fn-bpn-nth 4 values)))))
    (if (fn-bpnp-dispatch-recordp row) row nil)))

(defun fn-bpnp-dispatch-unframe (octets)
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
                           *fn-bpnp-dispatch-frame-version*)
                    (equal (fn-frame-result-kind answer)
                           *fn-bpnp-dispatch-kind*)
                    (fn-cbor-octet-listp (fn-frame-result-payload answer))))
          nil
        (let ((parsed (fn-frame-fields-parse
                       *fn-bpnp-dispatch-fields*
                       (fn-frame-result-payload answer))))
          (if (not (fn-frame-parse-okp parsed)) nil
            (let ((row (fn-bpnp-dispatch-from-values
                        (fn-frame-parse-value parsed))))
              (if (equal (fn-bpnp-dispatch-frame row) octets)
                  row nil))))))))
