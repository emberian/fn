; Complete single-call cache walks: structure, byte soundness, completeness.
(in-package "ACL2")
(include-book "extent-cache-storage-rows")

(defthm fn-xc-decoded-span-at-structure
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) (s (mv-nth 2 r)) (rr (fn-xc-decoded-span-row s ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)))
    (implies (equal (mv-nth 0 r) :span)
      (and (natp from) (natp s) (<= from s) (< s (fn-xcs-count slots))
           (fn-xc-readyp slots cells) (natp p) (natp end) (natp decoded)
           (fn-xc-slot-matchp s nil 3 file eoff elen poff compressed decoded dict-id trailer p slots) (equal (mv-nth 0 rr) :span)
           (equal (mv-nth 1 r) (- (mv-nth 1 rr) p))
           (equal (mv-nth 3 r) (mv-nth 2 rr))
           (equal (mv-nth 4 r) (mv-nth 1 (fn-xc-touch s slots cells)))
           (equal (mv-nth 5 r) (mv-nth 2 (fn-xc-touch s slots cells))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)
           :in-theory (disable fn-xc-decoded-span-row fn-xc-touch fn-xc-slot-matchp fn-xc-decoded-planp))))

(defthm fn-xc-decoded-span-at-miss-changes-nothing
  (let ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)))
    (implies (not (equal (mv-nth 0 r) :span)) (equal r (list :miss 0 nil dst slots cells))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)
           :in-theory (disable fn-xc-decoded-span-row fn-xc-touch fn-xc-slot-matchp fn-xc-decoded-planp))))

(defthm fn-xc-entry-span-at-structure
  (let* ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)) (s (mv-nth 2 r)) (rr (fn-xc-entry-span-row s file eoff elen poff plen trailer p end slots entries dst)))
    (implies (equal (mv-nth 0 r) :span)
      (and (natp from) (natp s) (<= from s) (< s (fn-xcs-count slots))
           (fn-xc-readyp slots cells) (natp p) (natp end) (natp eoff) (natp elen) (natp poff) (natp plen) (< s (fn-xc-ne cells))
           (fn-xc-slot-matchp s nil 1 file eoff elen 0 0 0 0 trailer 0 slots) (equal (mv-nth 0 rr) :span)
           (equal (mv-nth 1 r) (- (mv-nth 1 rr) p))
           (equal (mv-nth 3 r) (mv-nth 2 rr))
           (equal (mv-nth 4 r) (mv-nth 1 (fn-xc-touch s slots cells)))
           (equal (mv-nth 5 r) (mv-nth 2 (fn-xc-touch s slots cells))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)
           :in-theory (disable fn-xc-entry-span-row fn-xc-touch fn-xc-slot-matchp fn-xc-decoded-planp))))

(defthm fn-xc-entry-span-at-miss-changes-nothing
  (let ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)))
    (implies (not (equal (mv-nth 0 r) :span)) (equal r (list :miss 0 nil dst slots cells))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)
           :in-theory (disable fn-xc-entry-span-row fn-xc-touch fn-xc-slot-matchp fn-xc-decoded-planp))))

