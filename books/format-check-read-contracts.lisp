; Actual page-verification effects, independent of the full caller guard.
(in-package "ACL2")
(include-book "format-check")
(fn2-book-layer :b)

(defthm fn2-fc-byte-page-check-pool-frame
 (equal (mv-nth 3 (fn2-fc-byte row :page nil slot gen off len base okind oslot ogen fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool)
 :hints (("Goal" :in-theory (enable fn2-fc-byte))))

(defthm fn2-fc-advance-page-check-pool-frame
 (equal (mv-nth 4 (fn2-fc-advance fuel row :page nil slot gen off len base okind oslot ogen fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool)
 :hints (("Goal" :in-theory (enable fn2-fc-advance))))

(defthm fn2-fc-run-bytes-page-check-pool-frame
 (equal (mv-nth 3 (fn2-fc-run-bytes fuel row :page nil slot gen off len base okind oslot ogen fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool)
 :hints (("Goal" :in-theory (enable fn2-fc-run-bytes) :induct (fn2-fc-run-bytes fuel row :page nil slot gen off len base okind oslot ogen fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))

(defthm fn2-fc-step-page-check-pool-frame
 (equal (mv-nth 4 (fn2-fc-step row :page nil slot gen off len base okind oslot ogen budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool)
 :hints (("Goal" :in-theory (enable fn2-fc-step))))

(defthm fn2-format-run-page-check-pool-frame
 (equal (mv-nth 4 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool)
 :hints (("Goal" :in-theory (enable fn2-format-run))))

(defthm fn2-fc-decoded-never-ok
 (not (equal (mv-nth 0 (fn2-fc-decoded row kind off len base next fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) :ok))
 :hints (("Goal" :in-theory (enable fn2-fc-decoded))))

(defthm fn2-fc-step-page-check-ok-fields-frame
 (implies (equal (mv-nth 0 (fn2-fc-step row :page nil slot gen off len base okind oslot ogen budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) :ok)
          (equal (mv-nth 3 (fn2-fc-step row :page nil slot gen off len base okind oslot ogen budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-fields))
 :hints (("Goal" :in-theory (enable fn2-fc-step))))

(defthm fn2-format-run-page-check-ok-fields-frame
 (implies (equal (mv-nth 0 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) :ok)
          (equal (mv-nth 3 (fn2-format-run :page nil row slot gen off len base okind oslot ogen budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-fields))
 :hints (("Goal" :in-theory (enable fn2-format-run))))
