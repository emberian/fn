; Representation-only construction for the actual P2 read-root differential.
; This is not funded builder/publication/admission or faithful-O evidence.
(in-package "ACL2")

(defun fn-xp2-install-path (slot depth id incarnation tag encoded-seq fn-ibp-node)
  (declare (xargs :mode :program :stobjs fn-ibp-node
                  :guard (and (natp slot) (natp depth) (posp id) (natp incarnation)
                              (unsigned-byte-p 64 tag) (unsigned-byte-p 64 encoded-seq))))
  (cond
   ((zp depth)
    (stobj-let ((fn-ibp-table-page
                 (fn-ibp-node-children-get 'fn-ibp-table-page fn-ibp-node
                                           (create-fn-ibp-table-page))))
      (fn-ibp-table-page)
      (mv-let (status fn-ibp-table-page)
        (fn-ibp-table-initialize id incarnation fn-ibp-table-page)
        (declare (ignore status))
        (let* ((fn-ibp-table-page (fn-ibp-table-set 0 tag fn-ibp-table-page))
               (fn-ibp-table-page (fn-ibp-table-set 1024 encoded-seq fn-ibp-table-page)))
          (mv-let (status fn-ibp-table-page)
            (fn-ibp-table-seal id incarnation fn-ibp-table-page)
            (declare (ignore status))
            fn-ibp-table-page)))
      fn-ibp-node))
   ((equal (mod slot 2) 0)
    (stobj-let ((fn-ibp-node-left
                 (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                           (create-fn-ibp-node-left))))
      (fn-ibp-node-left)
      (fn-xp2-install-path (floor slot 2) (- depth 1) id incarnation tag encoded-seq fn-ibp-node-left)
      fn-ibp-node))
   (t
    (stobj-let ((fn-ibp-node-right
                 (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                           (create-fn-ibp-node-right))))
      (fn-ibp-node-right)
      (fn-xp2-install-path (floor slot 2) (- depth 1) id incarnation tag encoded-seq fn-ibp-node-right)
      fn-ibp-node))))

(defun fn-xp2-query ()
  (declare (xargs :mode :program :guard t))
  (fn-miq-make 1 1 nil 1 1 1 nil 7 '(0 1 0) nil nil :probing))

(defun fn-xp2-observe (label fuel slot depth id incarnation fn-ibp-node state)
  (declare (xargs :mode :program :stobjs (fn-ibp-node state)
                  :guard (and (stringp label) (natp fuel) (<= fuel 2048)
                              (natp slot) (natp depth) (posp id) (natp incarnation))))
  (let ((query (fn-xp2-query)))
    (mv-let (status next-query candidate fuel-left)
      (fn-ibp-node-query-next query fuel slot depth id incarnation fn-ibp-node)
      (pprogn (princ$ label *standard-co* state)
              (princ$ " " *standard-co* state)
              (xt-json-datum (list status next-query candidate fuel-left
                                   (fn-ibp-node-children-count fn-ibp-node))
                             *standard-co* state)
              (newline *standard-co* state)))))
