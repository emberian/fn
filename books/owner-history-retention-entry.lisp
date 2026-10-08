; Exact retention boundary, with a resident-history prepare.
(in-package "ACL2")
(include-book "owner-history-prepare-entry")
(include-book "owner-identity-prepare")
(include-book "post-fields")
(include-book "store-octet-entry")

(defun fn-hsp-idrp-prepare-retention (oc event grant fn-arena fn-hist)
 (declare (xargs :stobjs (fn-arena fn-hist)
                 :guard (and (fn-sn-statep (fn-sbud-oc-store oc)) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc)))))
          (ignorable fn-arena))
 (mv-let (allowed remaining) (fn-idr-consume-grant (fn-sbud-oc-store oc) event grant)
  (if (not allowed) (mv :refused oc remaining nil)
   (mv-let (word next) (fn-hsp-pout-prepare-retention oc event fn-hist)
    (mv word next remaining t)))))

(defthm fn-hsp-idrp-prepare-retention-is-reference
 (implies (and (fn-lgoc-invariantp oc)
               (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-idrp-prepare-retention oc event grant arena hist)
         (fn-idrp-prepare-retention oc event grant arena)))
 :hints (("Goal" :in-theory '(fn-hsp-idrp-prepare-retention fn-idrp-prepare-retention
 fn-hsp-pout-prepare-retention-is-reference))))

(defthm fn-hsp-idrp-prepare-retention-preserves-invariant
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (mv-nth 1 (fn-hsp-idrp-prepare-retention oc event grant arena hist))))
 :hints (("Goal" :in-theory '(fn-hsp-idrp-prepare-retention fn-hsp-pout-prepare-retention
 fn-hsp-ocfg-prepare-retention-preserves-invariant mv-nth nth zp car-cons cdr-cons
 (:executable-counterpart zp)))))

(in-theory (disable fn-hsp-idrp-prepare-retention))

(defun fn-owner-prepare-retention
  (kind id-octets subject-octets evidence-octets charge fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :verify-guards t
                  :guard (and (fn-cbor-octet-listp id-octets)
                              (fn-cbor-octet-listp subject-octets)
                              (fn-cbor-octet-listp evidence-octets)
                              (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state))))))
  (let* ((oc (fn-owner-ocfg state))
         (s (fn-sbud-oc-store oc))
         (node (fn-sn-node s))
         (grant (if (boundp-global 'fn-owner-identity-grant state)
                    (f-get-global 'fn-owner-identity-grant state) nil))
         ; Consume this capability even when preparation refuses.  A retry
         ; must acquire another fresh ID; no callback can reuse the grant.
         (state (f-put-global 'fn-owner-identity-grant nil state)))
    ; books/post-fields.lisp fn-pfld-retention-inputsp.
    (if (not (fn-pfld-retention-inputsp kind id-octets subject-octets
                                        evidence-octets charge))
        (value :invalid)
      (let* ((txid (fn-state-next-txid (fn-node-acceptance node)))
             (event (fn-store-retention-event-make
                     kind (fn-sn-identity-next s) txid txid
                     (fn-store-octets->string id-octets)
                     (fn-store-octets->string subject-octets)
                     (fn-store-octets->string evidence-octets) charge)))
        ; The fused grant/prepare boundary also decides whether installation
        ; is allowed; a denied capability invokes no owner refresh.
        (mv-let (word next remaining installp)
          ; OC is the configured owner read before the grant's reset (a
          ; write of another global; fn-owner-ocfg-of-other-global-put).
          (fn-idrp-prepare-retention oc event grant fn-arena)
          (let* ((state (f-put-global 'fn-owner-identity-grant remaining state))
                 (state (if installp (fn-owner-install-ocfg next state) state)))
            (value word)))))))

(defun fn-owner-prepare-retention-served
  (kind id-octets subject-octets evidence-octets charge fn-arena fn-hist state)
  (declare (xargs :stobjs (state fn-arena fn-hist) :verify-guards t
                  :guard (and (and (fn-cbor-octet-listp id-octets)
                              (fn-cbor-octet-listp subject-octets)
                              (fn-cbor-octet-listp evidence-octets)
                              (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))) (fn-cst-relation (fn-owner-store state)))))
  (let* ((oc (fn-owner-ocfg state))
         (s (fn-sbud-oc-store oc))
         (node (fn-sn-node s))
         (grant (if (boundp-global 'fn-owner-identity-grant state)
                    (f-get-global 'fn-owner-identity-grant state) nil))
         ; Consume this capability even when preparation refuses.  A retry
         ; must acquire another fresh ID; no callback can reuse the grant.
         (state (f-put-global 'fn-owner-identity-grant nil state)))
    ; books/post-fields.lisp fn-pfld-retention-inputsp.
    (if (not (fn-pfld-retention-inputsp kind id-octets subject-octets
                                        evidence-octets charge))
        (value :invalid)
      (let* ((txid (fn-state-next-txid (fn-node-acceptance node)))
             (event (fn-store-retention-event-make
                     kind (fn-sn-identity-next s) txid txid
                     (fn-store-octets->string id-octets)
                     (fn-store-octets->string subject-octets)
                     (fn-store-octets->string evidence-octets) charge)))
        ; The fused grant/prepare boundary also decides whether installation
        ; is allowed; a denied capability invokes no owner refresh.
        (mv-let (word next remaining installp)
          ; OC is the configured owner read before the grant's reset (a
          ; write of another global; fn-owner-ocfg-of-other-global-put).
          (fn-hsp-idrp-prepare-retention oc event grant fn-arena fn-hist)
          (let* ((state (f-put-global 'fn-owner-identity-grant remaining state))
                 (state (if installp (fn-owner-install-ocfg next state) state)))
            (value word)))))))

(defthm fn-owner-prepare-retention-served-is-reference
 (implies (and (fn-owner-retain-statep state)
               (fn-hist-of-storep hist (fn-owner-store state)))
  (equal (fn-owner-prepare-retention-served kind id-octets subject-octets evidence-octets charge arena hist state)
         (fn-owner-prepare-retention kind id-octets subject-octets evidence-octets charge arena state)))
 :hints (("Goal" :in-theory '(fn-owner-prepare-retention-served fn-owner-prepare-retention
 fn-owner-retain-statep fn-owner-store fn-owner-core fn-owner-ocfg
 fn-hsp-idrp-prepare-retention-is-reference))))

(defthm fn-owner-prepare-retention-served-preserves-carried-state
 (implies (fn-owner-retain-statep state)
  (fn-owner-retain-statep
   (mv-nth 2 (fn-owner-prepare-retention-served kind id-octets subject-octets evidence-octets charge fn-arena fn-hist state))))
 :hints (("Goal" :in-theory
 (union-theories '(fn-owner-prepare-retention-served
 fn-orh-retain-statep-of-other-global-put fn-orh-retain-statep-of-install-ocfg
 fn-hsp-idrp-prepare-retention-preserves-invariant) (theory 'minimal-theory))
 :use ((:instance fn-owner-retain-statep-implies-lgoc)))))

(in-theory (disable fn-owner-prepare-retention-served))
