; Compare every observed member row across the write made by transaction
; admission, including the untouched prefix and suffix of the batch table.
(in-package "ACL2")
(include-book "commit-admission-observation")
(include-book "commit-member-install-proof")
(fn2-book-layer :b)

(defthm fn2-ctp-member-fields-of-install
 (let ((after (fn2-commit-member-put r (kind *fn2-commit-member-kind-txn*)
               (slot slot) (gen gen) (len len) (okind okind) (oslot oslot) (ogen ogen)
               (entries 0) (entry-bytes 0) (schema 0) (event event) (settled settled))))
  (implies (and (natp i) (natp r) (< r (fn2-commit-member-rows fn2-commit-member)))
           (equal (fn2-ctp-member-fields i after)
                  (if (equal i r)
                      (list *fn2-commit-member-kind-txn* slot gen len okind oslot ogen event settled)
                    (fn2-ctp-member-fields i fn2-commit-member)))))
 :hints (("Goal" :in-theory (e/d (fn2-ctp-member-fields)
                                 (fn2-commit-member-rows
                                  fn2-commit-member-row-snapshot)))))

(defthm fn2-ctp-member-range-of-install
 (let* ((row (list *fn2-commit-member-kind-txn* slot gen len okind oslot ogen event settled))
        (after (fn2-commit-member-put r (kind *fn2-commit-member-kind-txn*)
                (slot slot) (gen gen) (len len) (okind okind) (oslot oslot) (ogen ogen)
                (entries 0) (entry-bytes 0) (schema 0) (event event) (settled settled)))
        (before-rows (fn2-ctp-member-fields-range start count fn2-commit-member)))
  (implies (and (natp start) (natp r) (< r (fn2-commit-member-rows fn2-commit-member)))
           (equal (fn2-ctp-member-fields-range start count after)
                  (if (and (<= start r) (< r (+ start (nfix count))))
                      (update-nth (- r start) row before-rows)
                    before-rows))))
 :hints (("Goal" :induct (fn2-ctp-member-fields-range start count fn2-commit-member)
          :in-theory (disable fn2-ctp-member-fields fn2-commit-member-rows))))

(defthm fn2-ctp-member-at-range-index
 (implies (and (natp start) (natp r) (<= start r) (< r (+ start (nfix count))))
          (equal (nth (- r start) (fn2-ctp-member-fields-range start count fn2-commit-member))
                 (fn2-ctp-member-fields r fn2-commit-member)))
 :hints (("Goal" :induct (fn2-ctp-member-fields-range start count fn2-commit-member)
          :in-theory (disable fn2-ctp-member-fields))))
