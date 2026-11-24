; Compare every observed member row across the write made by transaction
; admission, including the untouched prefix and suffix of the batch table.
(in-package "ACL2")
(include-book "commit-admission-observation")
(include-book "commit-member-install-proof")
(include-book "commit-settled-reservation-proof")
(fn2-book-layer :b)

(defthmd fn2-ctp-member-fields-from-snapshot
 (equal (fn2-ctp-member-fields i fn2-commit-member)
        (and (< (nfix i) (fn2-commit-member-rows fn2-commit-member))
             (let ((row (fn2-commit-member-row-snapshot i fn2-commit-member)))
               (append (take 7 row) (nthcdr 10 row)))))
 :hints (("Goal" :in-theory (e/d (fn2-commit-member-row-snapshot)
                   (fn2-commit-member-rows fn2-commit-member-kind fn2-commit-member-slot
                    fn2-commit-member-gen fn2-commit-member-len fn2-commit-member-okind
                    fn2-commit-member-oslot fn2-commit-member-ogen fn2-commit-member-event
                    fn2-commit-member-settled fn2-commit-member-schema fn2-commit-member-entries
                    fn2-commit-member-entry-bytes)))))

(defthm fn2-ctp-member-fields-of-install
 (let ((after (fn2-commit-member-put r (kind *fn2-commit-member-kind-txn*)
               (slot slot) (gen gen) (len len) (okind okind) (oslot oslot) (ogen ogen)
               (entries 0) (entry-bytes 0) (schema 0) (event event) (settled settled))))
  (implies (and (natp i) (natp r) (< r (fn2-commit-member-rows fn2-commit-member)))
           (equal (fn2-ctp-member-fields i after)
                  (if (equal i r)
                      (list *fn2-commit-member-kind-txn* slot gen len okind oslot ogen event settled)
                    (fn2-ctp-member-fields i fn2-commit-member)))))
 :hints (("Goal" :in-theory (e/d (fn2-ctp-member-fields-from-snapshot)
                                 (fn2-ctp-member-fields fn2-commit-member-rows
                                  fn2-commit-member-row-snapshot)))))

(defthm fn2-ctp-member-differences-of-install
 (let* ((row (list *fn2-commit-member-kind-txn* slot gen len okind oslot ogen event settled))
        (after (fn2-commit-member-put r (kind *fn2-commit-member-kind-txn*)
                (slot slot) (gen gen) (len len) (okind okind) (oslot oslot) (ogen ogen)
                (entries 0) (entry-bytes 0) (schema 0) (event event) (settled settled))))
  (implies (and (natp start) (natp r) (< r (fn2-commit-member-rows fn2-commit-member)))
           (equal (fn2-ctp-diffs (fn2-ctp-member-fields-range start count fn2-commit-member)
                                 (fn2-ctp-member-fields-range start count after))
                  (if (and (<= start r) (< r (+ start (nfix count)))
                           (not (equal row (fn2-ctp-member-fields r fn2-commit-member))))
                      (list row) nil))))
 :hints (("Goal" :induct (fn2-ctp-member-fields-range start count fn2-commit-member)
          :in-theory (disable fn2-ctp-member-fields fn2-commit-member-rows))))

; With room in the settled table, its reservation succeeds. The observed
; change is exactly the workspace and owner, even when reusing a batch row.
(defthm fn2-ctp-reserved-member-admission-observation
 (b* (((mv code settled &) (fn2-cs-reserve 9 oslot 5 fn2-commit-settled))
      (after (fn2-commit-member-put r (kind *fn2-commit-member-kind-txn*)
              (slot slot) (gen gen) (len len) (okind 9) (oslot oslot) (ogen 5)
              (entries 0) (entry-bytes 0) (schema 0) (event event) (settled settled)))
      (before-view (cons (fn2-ctp-member-fields-range 0 *fn2-commit-member-count*
                                                       fn2-commit-member) before-rest))
      (after-view (cons (fn2-ctp-member-fields-range 0 *fn2-commit-member-count* after)
                        after-rest)))
  (implies (and (unsigned-byte-p 32 (fn2-commit-settled-rows fn2-commit-settled))
                (< 0 (fn2-cs-free-count 0 0 fn2-commit-settled))
                (unsigned-byte-p 32 oslot) (natp r) (< r *fn2-commit-member-count*)
                (< r (fn2-commit-member-rows fn2-commit-member))
                (not (equal (list *fn2-commit-member-kind-txn* slot gen len 9 oslot 5 event settled)
                            (fn2-ctp-member-fields r fn2-commit-member))))
           (and (equal code :ok)
                (fn2-ctp-totalp code slot gen len oslot before-view after-view))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-cs-room-implies-reservation (okind 9) (ogen 5)))
          :in-theory (disable fn2-cs-reserve fn2-cs-free-count fn2-commit-settled-rows
                                      fn2-ctp-diffs fn2-ctp-member-fields fn2-ctp-member-fields-range
                                      fn2-commit-member-rows))))
