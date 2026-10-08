(in-package "ACL2")
(include-book "../../books/store-history-startup")
(include-book "../../books/defkeystone")
(defun fn-host-store-startup-state ()
  (declare (xargs :guard t :verify-guards nil))
  (update-nth 2
    (add-pair 'fn-store-sn (fn-sn-initial nil 0)
      (add-pair 'fn-store-sn-hist-reload t (nth 2 (build-state))))
    (build-state)))
(defthm fn-host-store-startup-positive
  (not (fn-host-hist-reloadp
        (mv-nth 3 (fn-store-history-startup nil (fn-host-store-startup-state))))))
(defthm fn-host-store-startup-skipped
  (and (not (fn-host-hist-reloadp
             (mv-nth 3 (fn-store-history-startup nil (fn-host-store-startup-state)))))
       (not (not (fn-host-hist-reloadp (fn-host-store-startup-state))))))
(defteeth fn-store-history-startup-consumes-reload
  :claim (() (not (fn-host-hist-reloadp (mv-nth 3 (fn-store-history-startup hist st)))))
  :subject fn-store-history-startup
  :witness ((hist nil) (st (fn-host-store-startup-state)))
  :witness-lemma fn-host-store-startup-positive
  :breaks ()
  :mutations ((skipped-startup (:conclusion (not (fn-host-hist-reloadp st)))
                ((hist nil) (st (fn-host-store-startup-state)))
                :fault "standalone inspect omits its startup load"
                :lemma fn-host-store-startup-skipped)))
