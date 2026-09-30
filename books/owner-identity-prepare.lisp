; RET-010: actual decoded retention preparation subject called by
; host/owner-host.lisp fn-owner-prepare-retention. The host clears its global
; before validating input; this seam handles the decoded event only.
(in-package "ACL2")
(include-book "store-identity-reserve")
(include-book "owner-prepare-outcome")

(defun fn-idrp-prepare-retention (oc event grant fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-sn-statep (fn-sbud-oc-store oc))
                  :verify-guards nil))
  (mv-let (allowed remaining)
    (fn-idr-consume-grant (fn-sbud-oc-store oc) event grant)
    (if (not allowed) (mv :refused oc remaining nil)
      (mv-let (word next) (fn-pout-prepare-retention oc event fn-arena)
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
                    (fn-ocfg-step oc (list :store (list :prepare-retention event)) fn-arena)
                  oc))
         (equal (mv-nth 0 result)
                (if (and authorized
                         (not (equal (fn-sbud-oc-store (mv-nth 1 result))
                                     (fn-sbud-oc-store oc))))
                    :prepared :refused))))
  :hints (("Goal"
           :use ((:instance fn-pout-prepare-retention-answers-the-store-change
                            (e event)))
           :in-theory (e/d (fn-idrp-prepare-retention fn-idr-consume-grant)
                            (fn-idr-grant-boundp fn-pout-prepare-retention
                             fn-ocfg-step fn-sbud-oc-store)))))

(in-theory (disable fn-idrp-prepare-retention))
