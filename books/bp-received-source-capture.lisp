; Actual registered CURRENT receive-source projection, core-only. No native
; CURRENT/held row/source nonce input and no allocation/crypto permission.
; Kind5 publication must remain held while the original source is borrowed.
(in-package "ACL2")
(include-book "bp-controller-registry")
(set-verify-guards-eagerness 2)

(defun fn-bprx-fixed-recordp (x fields)
 (declare (xargs :guard (natp fields) :measure fields))
 (if (zp fields) (null x)
  (and (consp x) (fn-bprx-fixed-recordp (cdr x) (1- fields)))))

; Fixed field checks, not a served held/wire/bundle recognizer. Proper held
; semantics and canonical byte identity must be maintained by producer carry.
(defun fn-bprx-pending-sourcep (current)
 (declare (xargs :guard t))
 (let* ((issued (fn-bpnf-issued current)) (held (fn-bpn-nth 4 issued)))
  (and (fn-bprx-fixed-recordp issued 6)
       (eq (fn-bpn-nth 0 issued) :bpnf-operation)
       (natp (fn-bpn-nth 1 issued)) (natp (fn-bpn-nth 2 issued))
       (equal (fn-bpn-nth 1 issued) (fn-bpnf-epoch current))
       (eq (fn-bpn-nth 3 issued) :store)
       (eq (fn-bpn-nth 5 issued) :pending)
       (fn-bprx-fixed-recordp held 16)
       (eq (fn-bpn-nth 0 held) :bpnf-held)
       (natp (fn-bpn-nth 3 held)))))

; Proof-only: this includes the actual held wire=encode(bundle) relation.
; It is never invoked by a served reader and is not an installed grant.
(defun fn-bprx-received-source-carryp (current)
 (declare (xargs :guard t))
 (implies (fn-bprx-pending-sourcep current)
          (fn-bpnf-heldp (fn-bpn-nth 4 (fn-bpnf-issued current)))))

; Readonly registered lookup. CAPTURE retains the actual held reference, not
; a materialized copy; native must never receive this internal source tuple.
(defun fn-bprx-registered-source-read (controller fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal" :in-theory (disable fn-bpc-current)))))
 (mv-let (word current left)
  (fn-bpc-current controller fuel fn-bp-controller-registry)
  (cond
   ((not (eq word :current)) (mv word nil left))
   ((and (eq (fn-bpn-nth 3 (fn-bpnf-issued current)) :store)
         (eq (fn-bpn-nth 5 (fn-bpnf-issued current)) :uncertain))
    (mv :received-source-uncertain nil left))
   ((not (fn-bprx-pending-sourcep current))
    (mv :received-source-unavailable nil left))
   (t
    (let* ((issued (fn-bpnf-issued current)) (held (fn-bpn-nth 4 issued)))
     (mv :received-source
         (list :bp-received-source controller (fn-bpn-nth 1 issued)
               (fn-bpn-nth 2 issued) (fn-bpn-nth 3 held) held)
         left))))))
