; Exact duplicate and conflicting-binding outcomes of the byte-identity
; decision over an octet-model article list (books/store-node.lisp
; fn-sn-action-over).  Since D25 the verdict is source-keyed
; (books/poster-bytes.lisp fn-pb-action-over), which refines this one
; (fn-pb-action-over-refines-the-byte-identity-decision,
; books/poster-bytes-invariants.lisp); the host's entry is
; books/store-intern.lisp fn-store-existing-action, read against both over
; ALPHA of the Store's articles in books/store-existing-alpha.lisp.  The three
; equations restate the definition (-by-definition), no keystone.
(in-package "ACL2")
(include-book "store-node")

(defthm fn-sn-action-over-is-duplicate-iff-byte-identical-by-definition
  (let ((held (fn-find-article msgid articles)))
    (equal (equal (fn-sn-action-over msgid payload groups articles) :duplicate)
           (and held
                (equal payload (fn-article-payload held))
                (equal groups (fn-article-groups held)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-action-over))))

(defthm fn-sn-action-over-is-conflict-iff-held-binding-differs-by-definition
  (let ((held (fn-find-article msgid articles)))
    (equal (equal (fn-sn-action-over msgid payload groups articles) :conflict)
           (and held
                (or (not (equal payload (fn-article-payload held)))
                    (not (equal groups (fn-article-groups held)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-action-over))))

(defthm fn-sn-action-over-is-missing-iff-no-held-binding-by-definition
  (equal (null (fn-sn-action-over msgid payload groups articles))
         (null (fn-find-article msgid articles)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-action-over))))
