; The guard closure of bp-fnbs-codec (lane depth-debt-3, row K2) changed
; two bodies: the recognizer recognises its held record (fn-bpnf-heldp)
; before reading its slots, and the codec refuses a wire that does not
; decode to a bundle before building a held record from it.  This book keeps the earlier definitions under
; -before-guards names and proves each served function equal to its earlier
; one on every input, so every theorem an includer states about the served
; names carries over unchanged.  Nothing includes this book; it is the
; evidence, and tests/acl2/bp-fnbs-codec-equivalence-tests holds its teeth.
(in-package "ACL2")
(include-book "bp-fnbs-codec")

(set-verify-guards-eagerness 0)

; -----------------------------------------------------------------------------
; The earlier definitions, verbatim (bp-fnbs-codec at origin/dev fa6294e09).

(defun fn-bpnf-stored-recordp-before-guards (record)
  (declare (xargs :guard t))
  (and (true-listp record) (equal (len record) 4)
       (equal (car record) :bpnf-stored)
       (fn-frame-natp (nth 1 record))
       (fn-frame-natp (nth 2 record))
       (let* ((held (nth 3 record))
              (ingress (nth 4 held))
              (wire (fn-bpnf-held-wire held))
              (bundle (fn-bpnf-held-bundle held)))
         (and (fn-bpnf-frame-ingressp ingress)
              (fn-bpnf-heldp held)
              (fn-frame-natp (nth 3 held))
              (<= (len wire) *fn-bpnf-max-held-image*)
              (or (equal held (fn-bpnf-frame-held ingress (nth 3 held)
                                                   bundle wire))
                  (and (fn-bpnf-stored-anchorp (nth 9 held))
                       (equal held
                              (fn-bpnf-frame-held-with-anchor
                               ingress (nth 3 held) bundle wire
                               (nth 9 held)))))))))

(defun fn-bpnf-stored-from-values-before-guards (values)
  (declare (xargs :guard t))
  (let* ((peer (fn-bpn-peer-from-octets (nth 6 values)))
         (wire (nth 10 values))
         (decoded (if (and (fn-cbor-octet-listp wire)
                           (<= (len wire) *fn-bpnf-max-held-image*))
                      (fn-bpb-decode wire *fn-bpnf-max-held-image*)
                    (fn-cbor-error :malformed)))
         (bundle (if (fn-cbor-result-okp decoded)
                     (fn-cbor-result-value decoded) nil))
         (principal-ok (or (and (equal (nth 7 values) 0)
                                (equal (nth 8 values) '(0)))
                           (and (equal (nth 7 values) 1)
                                (consp (nth 8 values))
                                (fn-bpn-machine-textp (nth 8 values)))))
         (ingress (list :cl (cons (nth 3 values) (nth 4 values))
                        (nth 5 values) peer
                        (if (equal (nth 7 values) 0) nil (nth 8 values))
                        (nth 9 values)))
         (anchor
           (cond ((equal (len values) 11) nil)
                 ((and (equal (len values) 15)
                       (equal (nth 11 values) 1)
                       (equal (nth 12 values) 0)
                       (equal (nth 13 values) 0)
                       (equal (nth 14 values) 0))
                  '(:wall))
                 ((and (equal (len values) 15)
                       (equal (nth 11 values) 1)
                       (equal (nth 12 values) 1))
                  (list :observed-age (nth 13 values) (nth 14 values)))
                 (t :bad)))
         (held (fn-bpnf-frame-held-with-anchor
                ingress (nth 2 values) bundle wire anchor))
         (record (fn-bpnf-stored-record (nth 0 values) (nth 1 values) held)))
    (if (and principal-ok (not (equal anchor :bad))
             (fn-bpnf-stored-recordp record)) record nil)))

; -----------------------------------------------------------------------------
; fn-bpn-nth reads any list the way nth does: on an atom both answer nil,
; and fn-cbor-ag-car is car on a cons.  (bp-node-machine-invariants states
; the true-list case; every input is what the codec's values need, since a
; parse result is not known there to be a true list.)

(defthm fn-bpn-nth-is-nth
  (equal (fn-bpn-nth n xs) (nth n xs))
  :hints (("Goal" :in-theory (enable fn-bpn-nth fn-cbor-ag-car nth))))

; -----------------------------------------------------------------------------
; The recognizer: the same conjuncts, the held record recognised before its
; slots are read; the same function on every input.

(defthm fn-bpnf-stored-recordp-equals-before-guards
  (equal (fn-bpnf-stored-recordp record)
         (fn-bpnf-stored-recordp-before-guards record))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bpnf-stored-recordp
                                   fn-bpnf-stored-recordp-before-guards)
                                  (fn-bpnf-heldp fn-bpnf-held-bundle
                                   fn-bpnf-held-wire fn-bpnf-frame-held
                                   fn-bpnf-frame-held-with-anchor
                                   fn-bpnf-frame-ingressp
                                   fn-bpnf-stored-anchorp)))))

; -----------------------------------------------------------------------------
; The codec: a wire that does not decode to a bundle named no record before
; either (the record it built failed the recognizer, whose held record must
; carry a bundle), so refusing before building it is the same function.

(defthm fn-bpnf-stored-recordp-refuses-a-non-bundle
  (implies (not (fn-bpb-bundlep bundle))
           (not (fn-bpnf-stored-recordp
                 (fn-bpnf-stored-record
                  epoch operation-id
                  (fn-bpnf-frame-held-with-anchor
                   ingress arrival bundle wire anchor)))))
  :hints (("Goal" :in-theory (e/d (fn-bpnf-stored-recordp fn-bpnf-heldp
                                   fn-bpnf-stored-record
                                   fn-bpnf-frame-held-with-anchor
                                   fn-bpnf-held fn-bpnf-held-bundle)
                                  (fn-bpb-bundlep fn-bpb-bundle-id
                                   fn-bpb-encode fn-bpnf-frame-ingressp
                                   fn-bpnf-stored-anchorp
                                   fn-bpnf-ingress-principal)))))

(defthm fn-bpnf-stored-from-values-equals-before-guards
  (equal (fn-bpnf-stored-from-values values)
         (fn-bpnf-stored-from-values-before-guards values))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bpnf-stored-from-values
                                   fn-bpnf-stored-from-values-before-guards)
                                  (fn-bpnf-stored-recordp fn-bpb-bundlep
                                   fn-bpb-decode fn-bpn-peer-from-octets
                                   fn-bpn-machine-textp
                                   fn-bpnf-frame-held-with-anchor
                                   fn-bpnf-stored-record fn-cbor-result-okp
                                   fn-cbor-result-value fn-cbor-error
                                   fn-cbor-octet-listp)))))
