; FNBS kind 14: the durable conflict record of spec bp-node-machine 3.3 and
; 4.1 step 4.  A received bundle whose identity names a live held bundle
; with a different immutable projection is refused :identity-conflict; the
; record names the held row (its arrival and primary identity), the ingress
; that offered the conflicting carrier (peer EID, session pair, transfer ID)
; and a content id of the conflicting carrier (the fn-digest seam over its
; exact received wire).  The held entry is never replaced.  The record
; changes no held row on replay; it is journal evidence and consumes one
; received final of journal credit, adding no debt.
(in-package "ACL2")
(include-book "bp-fnbs-dispatch-codec")
(include-book "crypto-attach")
(set-verify-guards-eagerness 0)

(defconst *fn-bpnf-conflict-kind* 14)
(defconst *fn-bpnf-conflict-frame-version* 1)
(defconst *fn-bpnf-conflict-fields*
  '(:nat :nat :nat :blob :blob :nat :nat :nat :blob))

(defun fn-bpnf-conflict-record
  (epoch op arrival identity peer session transfer content-id)
  (declare (xargs :guard t))
  (list :bpnf-conflict epoch op arrival identity peer session transfer
        content-id))

(defun fn-bpnf-conflict-recordp (row)
  (declare (xargs :guard t))
  (and (true-listp row) (equal (len row) 9)
       (equal (car row) :bpnf-conflict)
       (fn-frame-natp (fn-bpn-nth 1 row))
       (fn-frame-natp (fn-bpn-nth 2 row))
       (fn-frame-natp (fn-bpn-nth 3 row))
       (fn-cbor-octet-listp (fn-bpn-nth 4 row))
       (consp (fn-bpn-nth 4 row))
       (<= (len (fn-bpn-nth 4 row)) 1024)
       (fn-bpp-eidp (fn-bpn-nth 5 row))
       (consp (fn-bpn-nth 6 row))
       (fn-frame-natp (car (fn-bpn-nth 6 row)))
       (fn-frame-natp (cdr (fn-bpn-nth 6 row)))
       (fn-frame-natp (fn-bpn-nth 7 row))
       (fn-cbor-octet-listp (fn-bpn-nth 8 row))
       (equal (len (fn-bpn-nth 8 row)) 32)))

(defun fn-bpnf-conflict-values (row)
  (declare (xargs :guard t))
  (list (fn-bpn-nth 1 row) (fn-bpn-nth 2 row) (fn-bpn-nth 3 row)
        (fn-bpn-nth 4 row)
        (if (fn-bpp-eidp (fn-bpn-nth 5 row))
            (fn-bpn-peer-octets (fn-bpn-nth 5 row))
          nil)
        (fn-cbor-ag-car (fn-bpn-nth 6 row))
        (if (consp (fn-bpn-nth 6 row)) (cdr (fn-bpn-nth 6 row)) nil)
        (fn-bpn-nth 7 row) (fn-bpn-nth 8 row)))

(defun fn-bpnf-conflict-frame (row)
  (declare (xargs :guard t))
  (if (not (fn-bpnf-conflict-recordp row)) :bad
    (let ((values (fn-bpnf-conflict-values row)))
      (if (not (fn-frame-values-okp *fn-bpnf-conflict-fields* values)) :bad
        (let ((payload (fn-frame-fields-octets
                        *fn-bpnf-conflict-fields* values)))
          (if (not (and (fn-cbor-octet-listp payload)
                        (<= (len payload) *fn-bpn-lifecycle-max-payload*)))
              :bad
            (let ((protected
                   (fn-frame-protected
                    *fn-frame-magic-bundle-store*
                    *fn-bpnf-conflict-frame-version*
                    *fn-bpnf-conflict-kind* payload)))
              (append protected (fn-frame-trailer protected)))))))))

(defun fn-bpnf-conflict-from-values (values)
  (declare (xargs :guard t))
  (let ((row (fn-bpnf-conflict-record
              (fn-bpn-nth 0 values) (fn-bpn-nth 1 values)
              (fn-bpn-nth 2 values) (fn-bpn-nth 3 values)
              (fn-bpn-peer-from-octets (fn-bpn-nth 4 values))
              (cons (fn-bpn-nth 5 values) (fn-bpn-nth 6 values))
              (fn-bpn-nth 7 values) (fn-bpn-nth 8 values))))
    (if (fn-bpnf-conflict-recordp row) row nil)))

(defun fn-bpnf-conflict-unframe (octets)
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
                           *fn-bpnf-conflict-frame-version*)
                    (equal (fn-frame-result-kind answer)
                           *fn-bpnf-conflict-kind*)
                    (fn-cbor-octet-listp (fn-frame-result-payload answer))))
          nil
        (let ((parsed (fn-frame-fields-parse
                       *fn-bpnf-conflict-fields*
                       (fn-frame-result-payload answer))))
          (if (not (fn-frame-parse-okp parsed)) nil
            (let ((row (fn-bpnf-conflict-from-values
                        (fn-frame-parse-value parsed))))
              (if (equal (fn-bpnf-conflict-frame row) octets)
                  row nil))))))))

; The record the machine proposes for a conflicting reception: the held row
; H that owns the identity, the offering ingress, the conflicting wire.
(defun fn-bpnf-conflict-of (epoch op h ingress wire)
  (declare (xargs :guard t))
  (fn-bpnf-conflict-record
   epoch op (fn-bpn-nth 3 h) (fn-bpah-held-primary-identity h)
   (fn-bpn-nth 3 ingress) (fn-bpn-nth 1 ingress) (fn-bpn-nth 2 ingress)
   (fn-digest wire)))
