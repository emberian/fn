; Paired once-only installation: shared-pool capacity transition is the source
; of the receiver/controller association. No post-installed attach operation.
; Actual factory reserves provider+turn constructors before creating either;
; constructor workspace/profile and native alias settlement remain separate.
(in-package "ACL2")
(include-book "receiver-resource-host")
(include-book "../books/receiver-turn-controller")
(defun fn-rxt-installation-freshp (fn-receiver-turn)
  (declare (xargs :stobjs fn-receiver-turn :guard t))
  (and (eq (fn-rxt-phase fn-receiver-turn) :idle)
       (null (fn-rxt-ticket fn-receiver-turn))
       (null (fn-rxt-source fn-receiver-turn))
       (null (fn-rxt-demand fn-receiver-turn))
       (null (fn-rxt-job fn-receiver-turn))
       (null (fn-rxt-receipt fn-receiver-turn))
       ; Modern controller7 retains an ordinary output job independently.
       ; Idle input fields cannot authorize binding over that live root.
       (null (fn-rxt-output-bundle fn-receiver-turn))))
(defun fn-owner-rx-capacity-install-turn
  (token fn-rx-provider fn-receiver-turn fn-page-read-pool)
  (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool) :guard t))
  (if (not (fn-rxt-installation-freshp fn-receiver-turn))
      (mv :receiver-turn-busy fn-rx-provider fn-receiver-turn fn-page-read-pool)
    (mv-let (word fn-rx-provider fn-page-read-pool)
      (fn-owner-rx-capacity-install token fn-rx-provider fn-page-read-pool)
      (if (not (eq word :installed))
          (mv word fn-rx-provider fn-receiver-turn fn-page-read-pool)
        ; Installed pool U and provider carry precede controller readiness.
        ; An escape before receipt publication retains installed debt and
        ; leaves this controller unavailable; it must not repeat allocation.
        (let ((fn-receiver-turn
               (update-fn-rxt-receipt
                 (list :receiver-install (fn-rxp-token fn-rx-provider)
                       (fn-rxp-instance fn-rx-provider)) fn-receiver-turn)))
          (mv :installed fn-rx-provider fn-receiver-turn fn-page-read-pool))))))
(verify-guards fn-rxt-installation-freshp)
(verify-guards fn-owner-rx-capacity-install-turn)
