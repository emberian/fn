; Standalone inspect has no owner install. Load once before its served reads.
(in-package "ACL2")
(include-book "owner-history-sync")
(include-book "owner-retain-transitions")

(defun fn-store-history-startup (fn-hist state)
  (declare (xargs :stobjs (fn-hist state)
                  :guard (boundp-global 'fn-store-sn state)))
  (mv-let (fn-hist state)
      (fn-host-hist-startup (f-get-global 'fn-store-sn state) fn-hist state)
    (mv nil :loaded fn-hist state)))

(defthm fn-store-history-startup-consumes-reload
  (not (fn-host-hist-reloadp
        (mv-nth 3 (fn-store-history-startup hist st)))))

(defthm fn-store-history-startup-preserves-retain-state
  (implies (fn-owner-retain-statep state)
           (fn-owner-retain-statep
            (mv-nth 3 (fn-store-history-startup fn-hist state))))
  :hints (("Goal" :in-theory (enable fn-store-history-startup fn-host-hist-startup
                                     fn-owner-retain-statep fn-owner-ocfg
                                     fn-owner-retain-carry))))
(in-theory (disable fn-store-history-startup))
