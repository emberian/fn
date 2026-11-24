; Pointwise effect of the member-table write in fn2-commit-put-txn-member.
(in-package "ACL2")
(include-book "commit-members")
(fn2-book-layer :b)

(defthm fn2-commit-txn-member-install-row
 (let ((after (fn2-commit-member-put r (kind *fn2-commit-member-kind-txn*)
               (slot slot) (gen gen) (len len) (okind okind) (oslot oslot) (ogen ogen)
               (entries 0) (entry-bytes 0) (schema 0) (event event) (settled settled))))
  (implies (and (natp i) (natp r))
           (equal (fn2-commit-member-row-snapshot i after)
                  (if (equal i r)
                      (list *fn2-commit-member-kind-txn* slot gen len okind oslot ogen
                            0 0 0 event settled)
                    (fn2-commit-member-row-snapshot i fn2-commit-member)))))
 :hints (("Goal" :in-theory (enable fn2-commit-member-row-snapshot))))
