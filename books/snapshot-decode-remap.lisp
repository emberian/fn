; PRF-1081: shallow remap over borrowed decoder nodes, not materialized rows.
; Structural refinement below does not yet establish the decoder's shape
; carry or its physical source byte correspondence.
(in-package "ACL2")
(include-book "history-decode-nodes")
(defun fn-odm-pairp (node)
  (declare (xargs :guard t))
  (and (consp node) (eq (car node) :pair)))
(defun fn-odm-prefixp (n node)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) t
    (and (fn-odm-pairp node) (fn-odm-prefixp (1- n) (fn-hdc-cdr node)))))
(defun fn-odm-at (n node)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) (fn-hdc-car node)
    (fn-odm-at (1- n) (fn-hdc-cdr node))))
(defun fn-odm-put (n value node)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) (fn-hdc-pair value (fn-hdc-cdr node))
    (fn-hdc-pair (fn-hdc-car node)
                 (fn-odm-put (1- n) value (fn-hdc-cdr node)))))
(local
 (defthm fn-odm-abstract-pair-components
   (implies (fn-odm-pairp node)
            (equal (fn-hdc-abstract node pool)
                   (cons (fn-hdc-abstract (fn-hdc-car node) pool)
                         (fn-hdc-abstract (fn-hdc-cdr node) pool))))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-odm-pairp fn-hdc-abstract fn-hdc-car fn-hdc-cdr)))))
(local
 (defthm fn-odm-one-prefix-is-pair-by-definition
   (equal (fn-odm-prefixp 1 node) (fn-odm-pairp node))
   :hints (("Goal" :expand ((fn-odm-prefixp 1 node)
                            (fn-odm-prefixp 0 (fn-hdc-cdr node)))))))
(defthm fn-odm-put-refines-the-logical-field-replacement
  (implies (and (natp n) (fn-odm-prefixp (1+ n) node))
           (equal (fn-hdc-abstract (fn-odm-put n value node) pool)
                  (update-nth n (fn-hdc-abstract value pool)
                              (fn-hdc-abstract node pool))))
  :hints (("Goal" :induct (fn-odm-put n value node)
           :in-theory (e/d (fn-odm-put fn-odm-prefixp update-nth) (fn-odm-pairp)))))
(defthm fn-odm-at-refines-the-logical-field-read
  (implies (and (natp n) (fn-odm-prefixp (1+ n) node))
           (equal (fn-hdc-abstract (fn-odm-at n node) pool)
                  (nth n (fn-hdc-abstract node pool))))
  :hints (("Goal" :induct (fn-odm-at n node)
           :in-theory (e/d (fn-odm-at fn-odm-prefixp nth) (fn-odm-pairp)))))
(defun fn-odm-held (node handle)
  (declare (xargs :guard (natp handle)))
  (fn-odm-put 4 (fn-hdc-atom handle) node))
(defthm fn-odm-held-preserves-the-complete-logical-field-frame
  (implies (fn-odm-prefixp 5 node)
           (equal (fn-hdc-abstract (fn-odm-held node handle) pool)
                  (update-nth 4 handle (fn-hdc-abstract node pool))))
  :hints (("Goal" :in-theory (enable fn-odm-held))))
(defun fn-odm-composite (node handle)
  (declare (xargs :guard (natp handle)))
  (fn-odm-put 2 (fn-odm-held (fn-odm-at 2 node) handle) node))
(local
 (defthm fn-odm-inner-shape-establishes-the-composite-path
   (implies (fn-odm-prefixp 5 (fn-odm-at 2 node))
            (fn-odm-prefixp 3 node))
   :hints (("Goal" :do-not-induct t
            :cases ((fn-odm-pairp node)
                    (fn-odm-pairp (fn-hdc-cdr node))
                    (fn-odm-pairp (fn-hdc-cdr (fn-hdc-cdr node))))
            :expand ((fn-odm-at 2 node)
                     (fn-odm-at 1 (fn-hdc-cdr node))
                     (fn-odm-at 0 (fn-hdc-cdr (fn-hdc-cdr node)))
                     (fn-odm-prefixp 3 node)
                     (fn-odm-prefixp 2 (fn-hdc-cdr node))
                     (fn-odm-prefixp 1 (fn-hdc-cdr (fn-hdc-cdr node))))
            :in-theory (enable fn-odm-prefixp fn-odm-pairp fn-hdc-car fn-hdc-cdr)))))
(defthm fn-odm-composite-preserves-the-original-statement-and-held-frame
  (implies (fn-odm-prefixp 5 (fn-odm-at 2 node))
           (equal (fn-hdc-abstract (fn-odm-composite node handle) pool)
                  (update-nth 2
                              (update-nth 4 handle (nth 2 (fn-hdc-abstract node pool)))
                              (fn-hdc-abstract node pool))))
  :hints (("Goal" :in-theory (enable fn-odm-composite))))
(in-theory (disable fn-odm-pairp fn-odm-prefixp fn-odm-at fn-odm-put
                    fn-odm-held fn-odm-composite))
