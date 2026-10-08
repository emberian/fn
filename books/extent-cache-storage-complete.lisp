; A matching, covering row cannot be hidden by an earlier declining row.
(in-package "ACL2")
(include-book "extent-cache-storage-sound")

(defthm fn-xc-decoded-row-answers-a-byte
  (let* ((token (fn-xc-slot-token slot slots))
         (row (fn-xc-row slot cells))
         (z (fn-xcw-plan row wins)) (window (fn-xcw-window row wins)))
    (implies (and (natp p) (natp end) (natp decoded) (< p end)
                  (<= (fn-xc-ne cells) slot) (< row (fn-xcw-plans-length wins))
                  (fn-xc-decoded-planp z token)
                  (equal (mv-nth 0 (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed trailer decoded dict-id p window)) :byte))
             (equal (mv-nth 0 (fn-xc-decoded-span-row slot ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) :span)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (e/d (fn-xc-decoded-span-row fn-xcw-plan fn-xcw-window fn-pwz-cache-byte-at fn-pwz-cache-span-at fn-xc-span-end)
                                (fn-xc-slot-token fn-xc-decoded-planp fn-pwr-span-copy)))))

(defthm fn-xc-entry-row-answers-a-byte
  (implies (and (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end)
                (<= eoff poff) (<= (+ poff plen) (+ eoff elen)) (< p end) (< p plen)
                (< slot (fn-xce-keys-length entries))
                (equal (nth slot (nth 0 entries)) (fn-xc-entry-key file eoff elen trailer (fn-xc-slot-token slot slots)))
                (equal (len (nth slot (nth 1 entries))) (+ elen *fn-frame-trailer-octets*)))
           (equal (mv-nth 0 (fn-xc-entry-span-row slot file eoff elen poff plen trailer p end slots entries dst)) :span))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (e/d (fn-xc-entry-span-row) (fn-xc-slot-token fn-xce-copy)))))

(defthm fn-xc-decoded-walk-covers-a-ready-row
  (let ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)))
    (implies (and (fn-xc-readyp slots cells) (natp from) (natp i) (<= from i)
                  (< i (fn-xcs-count slots)) (natp p) (natp end) (natp decoded)
                  (fn-xc-slot-matchp i nil 3 file eoff elen poff compressed decoded dict-id trailer p slots) (equal (mv-nth 0 (fn-xc-decoded-span-row i ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) :span))
             (and (equal (mv-nth 0 r) :span) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst) :in-theory (disable fn-xc-decoded-span-row fn-xc-slot-matchp fn-xc-touch fn-xc-decoded-planp))))

(defthm fn-xc-entry-walk-covers-a-ready-row
  (let ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)))
    (implies (and (fn-xc-readyp slots cells) (natp from) (natp i) (<= from i)
                  (< i (fn-xcs-count slots)) (natp p) (natp end) (natp eoff) (natp elen) (natp poff) (natp plen) (< i (fn-xc-ne cells))
                  (fn-xc-slot-matchp i nil 1 file eoff elen 0 0 0 0 trailer 0 slots) (equal (mv-nth 0 (fn-xc-entry-span-row i file eoff elen poff plen trailer p end slots entries dst)) :span))
             (and (equal (mv-nth 0 r) :span) (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst) :in-theory (disable fn-xc-entry-span-row fn-xc-slot-matchp fn-xc-touch fn-xc-decoded-planp))))
(defthm fn-xc-decoded-span-at-answers-a-covered-slot
  (let* ((token (fn-xc-slot-token i slots))
         (z (fn-xcw-plan (fn-xc-row i cells) wins))
         (window (fn-xcw-window (fn-xc-row i cells) wins))
         (r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)))
    (implies
     (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
          (natp from) (natp i) (<= from i) (<= (fn-xc-ne cells) i)
          (< i (+ (fn-xc-ne cells) (fn-xc-nw cells)))
          (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))
          (natp p) (natp end) (natp decoded) (< p end)
          (fn-xc-slot-matchp i nil 3 file eoff elen poff compressed decoded dict-id trailer p slots)
          (fn-xc-decoded-planp z token)
          (equal (mv-nth 0 (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed trailer decoded dict-id p window)) :byte))
     (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r))
          (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-row fn-xc-readyp) (fn-xc-decoded-span-at fn-xc-decoded-span-row fn-xc-slot-matchp fn-xc-touch fn-xc-slot-token fn-xcw-plan fn-xcw-window fn-xc-decoded-planp fn-xcwp fn-xcep fn-xc-decoded-row-answers-a-byte fn-xc-entry-row-answers-a-byte))
           :use (fn-xc-decoded-walk-covers-a-ready-row fn-xc-decoded-span-at-span-count
                 (:instance fn-xc-decoded-row-answers-a-byte (slot i))))))

(defthm fn-xc-entry-span-at-answers-a-covered-slot
  (let ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)))
    (implies
     (and (fn-xcsp slots) (fn-xccp cells) (fn-xcep entries) (fn-xc-readyp slots cells)
          (natp from) (natp i) (<= from i) (< i (fn-xc-ne cells))
          (<= (fn-xc-ne cells) (fn-xce-keys-length entries))
          (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end)
          (<= eoff poff) (<= (+ poff plen) (+ eoff elen)) (< p end) (< p plen)
          (fn-xc-slot-matchp i nil 1 file eoff elen 0 0 0 0 trailer 0 slots)
          (equal (nth i (nth 0 entries)) (fn-xc-entry-key file eoff elen trailer (fn-xc-slot-token i slots)))
          (equal (len (nth i (nth 1 entries))) (+ elen *fn-frame-trailer-octets*)))
     (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r))
          (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-row fn-xc-readyp) (fn-xc-entry-span-at fn-xc-entry-span-row fn-xc-slot-matchp fn-xc-touch fn-xc-slot-token fn-xcw-plan fn-xcw-window fn-xc-decoded-planp fn-xcwp fn-xcep fn-xc-decoded-row-answers-a-byte fn-xc-entry-row-answers-a-byte))
           :use (fn-xc-entry-walk-covers-a-ready-row fn-xc-entry-span-at-span-count
                 (:instance fn-xc-entry-row-answers-a-byte (slot i))))))

