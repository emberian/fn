; RET-010: actual decoded retention preparation subject called by
; host/owner-host.lisp fn-owner-prepare-retention. The host clears its global
; before validating input; this seam handles the decoded event only.
(in-package "ACL2")
(include-book "store-identity-reserve")
(include-book "owner-prepare-outcome")
(include-book "owner-prepare-deferred-carried")

(defun fn-idrp-prepare-retention (oc event grant fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :verify-guards nil)
           (ignorable fn-arena))
  (mv-let (allowed remaining)
    (fn-idr-consume-grant (fn-sbud-oc-store oc) event grant)
    (if (not allowed) (mv :refused oc remaining nil)
      ; The carried Store prepare (lane served-incremental-2): no
      ; appended-history replay; fn-pout-prepare-retention's under
      ; fn-snt-relation and whenever the reference stages
      ; (books/owner-prepare-deferred-carried.lisp).
      (mv-let (word next) (fn-pdc-pout-prepare-retention oc event)
        (mv word next remaining t)))))

(verify-guards fn-idrp-prepare-retention)

; Complete output/effect refinement of the host-called fused boundary.
; INSTALLP preserves the original denied-capability branch: no reinstall.
(defthm fn-idrp-retention-preparation-consumes-exact-current-grant
  (let* ((result (fn-idrp-prepare-retention oc event grant fn-arena))
         (authorized (fn-idr-grant-boundp (fn-sbud-oc-store oc) event grant)))
    (and (null (mv-nth 2 result))
         (equal (mv-nth 3 result) (if authorized t nil))
         (equal (mv-nth 1 result)
                (if authorized
                    (fn-pdc-ocfg-prepare-retention oc event)
                  oc))
         (equal (mv-nth 0 result)
                (if (and authorized
                         (not (equal (fn-sbud-oc-store (mv-nth 1 result))
                                     (fn-sbud-oc-store oc))))
                    :prepared :refused))))
  :hints (("Goal"
           :use ((:instance fn-pdc-pout-prepares-answer-the-store-change
                            (e event)))
           :in-theory (e/d (fn-idrp-prepare-retention fn-idr-consume-grant)
                            (fn-idr-grant-boundp fn-pdc-pout-prepare-retention
                             fn-pdc-ocfg-prepare-retention fn-sbud-oc-store)))))

; The owner it installs is the configured owner's (:store (:prepare-retention
; E)) -- the reference the host called before -- on every owner whose Store
; the live-history relation admits; and keeps the host-carried invariant
; (fn-pdc-ocfg-prepare-retention-preserves-invariant).
(defthm fn-idrp-retention-preparation-is-ocfg-step-under-relation
  (implies (fn-snt-relation (fn-sbud-oc-store oc))
           (equal (mv-nth 1 (fn-idrp-prepare-retention oc event grant fn-arena))
                  (if (fn-idr-grant-boundp (fn-sbud-oc-store oc) event grant)
                      (fn-ocfg-step oc (list :store (list :prepare-retention event)) fn-arena)
                    oc)))
  :hints (("Goal"
           :use (fn-idrp-retention-preparation-consumes-exact-current-grant
                 (:instance fn-pdc-ocfg-prepare-retention-is-ocfg-step-under-relation))
           :in-theory '(fn-sbud-oc-store))))

(in-theory (disable fn-idrp-prepare-retention))
