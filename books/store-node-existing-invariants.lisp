; Exact duplicate and conflicting-binding outcomes of the host-called Store
; decision.  The lookup is over the live node carried by the composed Store.
(in-package "ACL2")
(include-book "store-node")

(defthm fn-sn-existing-action-is-duplicate-iff-byte-identical
  (let ((held (fn-find-article
               msgid (fn-state-articles
                      (fn-node-acceptance (fn-sn-node s))))))
    (equal (equal (fn-sn-existing-action msgid payload groups s) :duplicate)
           (and held
                (equal payload (fn-article-payload held))
                (equal groups (fn-article-groups held)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-existing-action))))

(defthm fn-sn-existing-action-is-conflict-iff-held-binding-differs
  (let ((held (fn-find-article
               msgid (fn-state-articles
                      (fn-node-acceptance (fn-sn-node s))))))
    (equal (equal (fn-sn-existing-action msgid payload groups s) :conflict)
           (and held
                (or (not (equal payload (fn-article-payload held)))
                    (not (equal groups (fn-article-groups held)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-existing-action))))

(defthm fn-sn-existing-action-is-missing-iff-no-held-binding
  (equal (null (fn-sn-existing-action msgid payload groups s))
         (null (fn-find-article
                msgid (fn-state-articles
                       (fn-node-acceptance (fn-sn-node s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-existing-action))))
