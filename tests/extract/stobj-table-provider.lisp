(in-package "ACL2")
(defstobj fn-ibp-node
  (fn-ibp-node-children :type (stobj-table 16))
  (fn-ibp-node-id :type (integer 0 *) :initially 0)
  :inline t)
(defstobj fn-ibp-node-left
  (fn-ibp-node-left-children :type (stobj-table 16))
  (fn-ibp-node-left-id :type (integer 0 *) :initially 0)
  :congruent-to fn-ibp-node :inline t)
(defstobj fn-ibp-node-right
  (fn-ibp-node-right-children :type (stobj-table 16))
  (fn-ibp-node-right-id :type (integer 0 *) :initially 0)
  :congruent-to fn-ibp-node :inline t)
(defun fn-ibp-node-add-left (id fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :guard (posp id)))
  (if (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node)
      (mv :already-present fn-ibp-node)
    (stobj-let ((fn-ibp-node-left
                 (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                           (create-fn-ibp-node-left))))
      (fn-ibp-node-left)
      (update-fn-ibp-node-id id fn-ibp-node-left)
      (mv :installed fn-ibp-node))))
(defun fn-ibp-node-left-id-read (fn-ibp-node)
  (declare (xargs :stobjs fn-ibp-node :guard t))
  (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
      (mv :unavailable nil)
    (stobj-let ((fn-ibp-node-left
                 (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                           (create-fn-ibp-node-left))))
      (id)
      (fn-ibp-node-id fn-ibp-node-left)
      (mv :present id))))
