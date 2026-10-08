; Per-row byte and frame contracts used by both complete walks.
(in-package "ACL2")
(include-book "extent-cache-storage")

(defthm fn-xce-copy-exact-output-and-effects
  (implies (and (natp src) (natp count) (natp dst) (natp k))
           (equal (nth k (nth 0 (fn-xce-copy src count dst entry span)))
                  (if (and (<= dst k) (< k (+ dst count)))
                      (nth (+ src (- k dst)) entry)
                    (nth k (nth 0 span)))))
  :hints (("Goal" :induct (fn-xce-copy src count dst entry span)
           :in-theory (enable fn-xce-copy update-fn-ew-span-bytesi fn-xce-entry-get))))
(in-theory (disable fn-xce-copy))

(defthm fn-xc-decoded-span-row-miss-keeps-span
  (implies (not (equal (mv-nth 0 (fn-xc-decoded-span-row slot ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) :span))
           (equal (mv-nth 2 (fn-xc-decoded-span-row slot ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) dst))
  :hints (("Goal" :in-theory (enable fn-xc-decoded-span-row fn-pwz-cache-span-at))))
(defthm fn-xc-entry-span-row-miss-keeps-span
  (implies (not (equal (mv-nth 0 (fn-xc-entry-span-row slot file eoff elen poff plen trailer p end slots entries dst)) :span))
           (equal (mv-nth 2 (fn-xc-entry-span-row slot file eoff elen poff plen trailer p end slots entries dst)) dst))
  :hints (("Goal" :in-theory (enable fn-xc-entry-span-row))))

(defthm fn-xc-decoded-span-row-unfolds-to-cache
  (let* ((r (fn-xc-decoded-span-row slot ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (row (fn-xc-row slot cells)) (token (fn-xc-slot-token slot slots))
         (z (fn-xcw-plan row wins)) (window (fn-xcw-window row wins))
         (j (fn-xc-span-end p end decoded (fn-pwz-nth 7 token) (fn-pwz-token-window-length token))))
    (implies (equal (mv-nth 0 r) :span)
             (and (<= (fn-xc-ne cells) slot) (< row (fn-xcw-plans-length wins))
                  (fn-xc-decoded-planp z token) (< p j) (equal (mv-nth 1 r) j)
                  (equal (mv-nth 0 (fn-pwz-cache-span-at ledger token file eoff elen poff compressed trailer decoded dict-id p j window dst)) :span)
                  (equal (mv-nth 2 r) (mv-nth 1 (fn-pwz-cache-span-at ledger token file eoff elen poff compressed trailer decoded dict-id p j window dst))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-decoded-span-row fn-xcw-plan fn-xcw-window) (fn-xc-decoded-planp fn-xc-slot-token)))))

(defthm fn-xc-entry-span-row-facts
  (let* ((r (fn-xc-entry-span-row slot file eoff elen poff plen trailer p end slots entries dst))
         (j (min (min end plen) (+ p *fn-ew-span-capacity*))))
    (implies (equal (mv-nth 0 r) :span)
             (and (< slot (fn-xce-keys-length entries))
                  (<= eoff poff) (<= (+ poff plen) (+ eoff elen))
                  (equal (nth slot (nth 0 entries)) (fn-xc-entry-key file eoff elen trailer (fn-xc-slot-token slot slots)))
                  (equal (len (nth slot (nth 1 entries))) (+ elen *fn-frame-trailer-octets*))
                  (< p j) (equal (mv-nth 1 r) j)
                  (equal (mv-nth 2 r) (fn-xce-copy (+ (- poff eoff) p) (- j p) 0 (nth slot (nth 1 entries)) dst)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-entry-span-row) (fn-xc-slot-token fn-xce-copy)))))

(defthm fn-xc-decoded-cache-span-facts
  (implies (equal (mv-nth 0 (fn-pwz-cache-span-at ledger token file eoff elen poff compressed trailer decoded dict-id p j window dst)) :span)
           (and (fn-pwz-cachedp ledger token)
                (natp decoded) (natp (fn-pwz-nth 7 token))
                (<= (fn-pwz-nth 7 token) p) (<= j decoded)
                (<= j (+ (fn-pwz-nth 7 token) (fn-pwz-token-window-length token)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-cache-span-at))))
