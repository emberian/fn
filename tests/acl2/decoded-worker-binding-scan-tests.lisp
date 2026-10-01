; Unfunded storage mutation fixture: no source issuer or constructor permission.
(in-package "ACL2")
(include-book "../../books/decoded-worker-binding-scan")

(defun fn-dwb-storage-fixture (fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard t :verify-guards nil))
 (let* ((rows (list (cons '(:incarnation 3) '(old :incarnation nil))
                    (cons '(:incarnation 7) '(paid :incarnation nil))))
        (source '(:captured-source :unfunded-test))
        (scan (fn-dwb-start 7 9 rows source))
        (fn-pww-node
         (stobj-let
          ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
          (fn-pww-carry)
          (let* ((fn-pww-carry (update-fn-pww-phase :admission-scanning fn-pww-carry))
                 (fn-pww-carry (update-fn-pww-pending-action scan fn-pww-carry)))
            fn-pww-carry)
          fn-pww-node)))
  (mv-let (first fn-pww-node) (fn-dwb-node-one fn-pww-node)
   (mv-let (second fn-pww-node) (fn-dwb-node-one fn-pww-node)
    (stobj-let
     ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
     (ok)
     (let ((current (fn-pww-pending-action fn-pww-carry)))
      (and (eq first :yield) (eq second :binding-resolved)
           (equal (fn-prl-nth 2 current) 9)
           (equal (fn-prl-nth 3 current) rows)
           (equal (fn-prl-nth 5 current) (fn-prl-binding '(:incarnation 7) rows))
           (equal (fn-prl-nth 7 current) source)
           (eq (fn-pww-phase fn-pww-carry) :admission-scanning)
           (null (fn-pww-token fn-pww-carry))))
     (mv ok fn-pww-node))))))

(defun fn-dwb-local-fixture ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-pww-node
  (mv-let (ok fn-pww-node) (fn-dwb-storage-fixture fn-pww-node) ok)))
(assert-event (fn-dwb-local-fixture))
