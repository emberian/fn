(in-package "ACL2")
(include-book "../../books/decoded-worker-factory")

; Explicitly unfunded local-stobj storage mutation. This seeds neither a
; genuine issuer nor an installed source/BODY allowance. It tests actual
; one-child effects and unresolved-intent nonretry, not service readiness.
(defun fn-dwf-storage-fixture (fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard t :verify-guards nil))
 (let ((token '(:decoded-window 1 7 100 320 120 40 200 99 250 0)))
  (let ((fn-pww-node
         (stobj-let
          ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
          (fn-pww-carry)
          (let* ((fn-pww-carry (update-fn-pww-token token fn-pww-carry))
                 (fn-pww-carry (update-fn-pww-phase :storage-constructing fn-pww-carry)))
           fn-pww-carry)
          fn-pww-node)))
   (mv-let (first fn-pww-node) (fn-dwf-node-one token fn-pww-node)
    (let ((first-only (and (eq first :decoded-child-created)
                          (fn-pww-children-boundp 'fn-octets fn-pww-node)
                          (not (fn-pww-children-boundp 'pgs-digest-state fn-pww-node))
                          (not (fn-pww-children-boundp 'fn-zin-st fn-pww-node)))))
     (mv-let (second fn-pww-node) (fn-dwf-node-one token fn-pww-node)
      (let* ((second-only (and (eq second :decoded-child-created)
                              (fn-pww-children-boundp 'pgs-digest-state fn-pww-node)
                              (not (fn-pww-children-boundp 'fn-zin-st fn-pww-node))))
             (fn-pww-node
              (stobj-let
               ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
               (fn-pww-carry)
               (update-fn-pww-observation (list :constructor-intent token 'fn-zin-st) fn-pww-carry)
               fn-pww-node)))
       (mv-let (third fn-pww-node) (fn-dwf-node-one token fn-pww-node)
        (mv (and (fn-pwz-tokenp token) first-only second-only
                 (eq third :decoded-constructor-uncertain)
                 (not (fn-pww-children-boundp 'fn-zin-st fn-pww-node))
                 (fn-pww-children-boundp 'fn-octets fn-pww-node)
                 (fn-pww-children-boundp 'pgs-digest-state fn-pww-node))
            fn-pww-node)))))))))

(defun fn-dwf-storage-fixture-run ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-pww-node
  (mv-let (answer fn-pww-node) (fn-dwf-storage-fixture fn-pww-node) answer)))

(assert-event (fn-dwf-storage-fixture-run))
