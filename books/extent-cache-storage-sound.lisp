; Strong byte contracts; the exact round-5a statements follow as corollaries.
(in-package "ACL2")
(include-book "extent-cache-storage-walk")

(defthm fn-xc-decoded-span-at-span-count
  (implies (equal (mv-nth 0 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) :span)
           (posp (mv-nth 1 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-decoded-span-at fn-xc-decoded-span-row fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window fn-xc-decoded-planp)
           :use (fn-xc-decoded-span-at-structure
                 (:instance fn-xc-decoded-span-row-unfolds-to-cache (slot (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))))))))

(defthm fn-xc-entry-span-at-span-count
  (implies (equal (mv-nth 0 (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)) :span)
           (posp (mv-nth 1 (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-entry-span-at fn-xc-entry-span-row fn-xc-slot-token fn-xce-copy)
           :use (fn-xc-entry-span-at-structure
                 (:instance fn-xc-entry-span-row-facts
                  (slot (mv-nth 2 (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst))))))))

(defthm fn-xc-decoded-span-at-is-the-per-slot-span
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r))
         (old (fn-pwz-cache-span-at ledger (fn-xc-slot-token s slots) file eoff elen poff compressed trailer decoded dict-id
                                     p (+ p n) (fn-xcw-window (fn-xc-row s cells) wins) dst)))
    (implies (and (equal (mv-nth 0 r) :span))
             (and (equal (mv-nth 0 old) :span) (equal (mv-nth 3 r) (mv-nth 1 old)))) )
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d () (fn-xc-decoded-span-at fn-xc-decoded-span-row fn-xc-entry-span-at fn-xc-entry-span-row fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window fn-xc-decoded-planp fn-xce-copy fn-xce-copy-exact-output-and-effects)) :use (fn-xc-decoded-span-at-structure (:instance fn-xc-decoded-span-row-unfolds-to-cache (slot (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))))))))

(defthm fn-xc-decoded-span-at-is-the-cached-bytes
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r))
         (token (fn-xc-slot-token s slots))
         (window (fn-xcw-window (fn-xc-row s cells) wins))
         (old (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed trailer decoded dict-id (+ p k) window)))
    (implies (and (equal (mv-nth 0 r) :span) (natp k) (< k n))
             (and (equal (mv-nth 0 old) :byte)
                  (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 old)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d () (fn-xc-decoded-span-at fn-xc-decoded-span-row fn-xc-entry-span-at fn-xc-entry-span-row fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window fn-xc-decoded-planp fn-xce-copy fn-xce-copy-exact-output-and-effects)) :use (fn-xc-decoded-span-at-is-the-per-slot-span fn-xc-decoded-span-at-span-count fn-xc-decoded-span-at-structure (:instance fn-pwz-cache-span-at-is-the-cached-bytes (i p) (j (+ p (mv-nth 1 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)))) (token (fn-xc-slot-token (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) slots)) (fn-ew-buffer (fn-xcw-window (fn-xc-row (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) cells) wins)) (fn-ew-span dst))))))

(defthm fn-xc-decoded-span-at-answers-from-a-matching-slot
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r)) (token (fn-xc-slot-token s slots)))
    (implies (and (equal (mv-nth 0 r) :span))
             (and (natp s) (<= from s) (<= (fn-xc-ne cells) s)
                  (< s (+ (fn-xc-ne cells) (fn-xc-nw cells)))
                  (fn-xc-slot-matchp s nil 3 file eoff elen poff compressed decoded dict-id trailer p slots)
                  (fn-pwz-cachedp ledger token)
                  (fn-xc-decoded-planp (fn-xcw-plan (fn-xc-row s cells) wins) token)
                  (posp n) (<= (+ p n) end) (<= (+ p n) decoded)
                  (<= (+ p n) (+ (fn-pwz-nth 7 token) (fn-pwz-token-window-length token)))
                  (<= n *fn-ew-span-capacity*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d () (fn-xc-decoded-span-at fn-xc-decoded-span-row fn-xc-entry-span-at fn-xc-entry-span-row fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window fn-xc-decoded-planp fn-xce-copy fn-xce-copy-exact-output-and-effects)) :use (fn-xc-decoded-span-at-structure fn-xc-decoded-span-at-span-count (:instance fn-xc-decoded-span-row-unfolds-to-cache (slot (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)))) (:instance fn-xc-decoded-cache-span-facts (token (fn-xc-slot-token (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) slots)) (j (+ p (mv-nth 1 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)))) (window (fn-xcw-window (fn-xc-row (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) cells) wins))) fn-xc-decoded-span-at-is-the-per-slot-span))))

(defthm fn-xc-entry-span-at-answers-from-a-matching-slot
  (let* ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r)))
    (implies
     (and (equal (mv-nth 0 r) :span))
     (and (natp s) (<= from s) (< s (fn-xc-ne cells))
          (fn-xc-slot-matchp s nil 1 file eoff elen 0 0 0 0 trailer 0 slots)
          (equal (nth s (nth 0 entries)) (fn-xc-entry-key file eoff elen trailer (fn-xc-slot-token s slots)))
          (equal (len (nth s (nth 1 entries))) (+ elen *fn-frame-trailer-octets*))
          (<= eoff poff) (<= (+ poff plen) (+ eoff elen))
          (posp n) (<= (+ p n) end) (<= (+ p n) plen) (<= n *fn-ew-span-capacity*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d () (fn-xc-decoded-span-at fn-xc-decoded-span-row fn-xc-entry-span-at fn-xc-entry-span-row fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window fn-xc-decoded-planp fn-xce-copy fn-xce-copy-exact-output-and-effects)) :use (fn-xc-entry-span-at-structure (:instance fn-xc-entry-span-row-facts (slot (mv-nth 2 (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst))))))))

(defthm fn-xc-entry-span-at-is-the-entry-bytes
  (let ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)))
    (implies
     (and (equal (mv-nth 0 r) :span) (natp k) (< k (mv-nth 1 r)))
     (equal (nth k (nth 0 (mv-nth 3 r)))
            (nth (+ (- poff eoff) p k) (nth (mv-nth 2 r) (nth 1 entries))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d () (fn-xc-decoded-span-at fn-xc-decoded-span-row fn-xc-entry-span-at fn-xc-entry-span-row fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window fn-xc-decoded-planp fn-xce-copy fn-xce-copy-exact-output-and-effects)) :use (fn-xc-entry-span-at-structure (:instance fn-xc-entry-span-row-facts (slot (mv-nth 2 (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)))) (:instance fn-xce-copy-exact-output-and-effects (src (+ (- poff eoff) p)) (count (mv-nth 1 (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst))) (dst 0) (entry (nth (mv-nth 2 (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)) (nth 1 entries))) (span dst))))))

(defthm fn-xc-decoded-span-at-is-the-returned-bytes
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r))
         (token (fn-xc-slot-token s slots))
         (z (fn-xcw-plan (fn-xc-row s cells) wins))
         (window (fn-xcw-window (fn-xc-row s cells) wins))
         (old (fn-pwz-byte-at returned-ledger worker token z file eoff elen poff compressed trailer decoded dict-id (+ p k) window)))
    (implies (and (equal (mv-nth 0 r) :span) (natp k) (< k n) (equal (fn-pwz-outcome returned-ledger worker token z) :ready))
             (and (equal (mv-nth 0 old) :byte)
                  (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 old)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-decoded-span-at fn-xc-decoded-span-row fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window fn-xc-decoded-planp)
           :use (fn-xc-decoded-span-at-is-the-cached-bytes
                 (:instance fn-pwz-a-hit-is-the-published-window
                  (ledger returned-ledger) (ledger2 ledger) (token (fn-xc-slot-token (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) slots)) (z (fn-xcw-plan (fn-xc-row (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) cells) wins))
                  (i (+ p k)) (fn-ew-buffer (fn-xcw-window (fn-xc-row (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) cells) wins)))
                 (:instance fn-pwz-hit-requires-a-cached-exact-window
                  (token (fn-xc-slot-token (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) slots)) (i (+ p k)) (fn-ew-buffer (fn-xcw-window (fn-xc-row (mv-nth 2 (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)) cells) wins)))))))

(defthm fn-xc-decoded-span-at-is-the-per-slot-span-round5a
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r))
         (old (fn-pwz-cache-span-at ledger (fn-xc-slot-token s slots) file eoff elen poff compressed trailer decoded dict-id
                                     p (+ p n) (fn-xcw-window (fn-xc-row s cells) wins) dst)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
                  (natp from) (natp p) (natp end) (natp decoded) (equal (mv-nth 0 r) :span))
             (and (equal (mv-nth 0 old) :span) (equal (mv-nth 3 r) (mv-nth 1 old)))) )
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-decoded-span-at fn-xc-entry-span-at fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window) :use fn-xc-decoded-span-at-is-the-per-slot-span)))

(defthm fn-xc-decoded-span-at-is-the-cached-bytes-round5a
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r))
         (token (fn-xc-slot-token s slots))
         (window (fn-xcw-window (fn-xc-row s cells) wins))
         (old (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed trailer decoded dict-id (+ p k) window)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
                  (natp from) (natp p) (natp end) (natp decoded)
                  (equal (mv-nth 0 r) :span) (natp k) (< k n))
             (and (equal (mv-nth 0 old) :byte)
                  (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 old)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-decoded-span-at fn-xc-entry-span-at fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window) :use fn-xc-decoded-span-at-is-the-cached-bytes)))

(defthm fn-xc-decoded-span-at-answers-from-a-matching-slot-round5a
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r)) (token (fn-xc-slot-token s slots)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
                  (natp from) (natp p) (natp end) (natp decoded) (equal (mv-nth 0 r) :span))
             (and (natp s) (<= from s) (<= (fn-xc-ne cells) s)
                  (< s (+ (fn-xc-ne cells) (fn-xc-nw cells)))
                  (fn-xc-slot-matchp s nil 3 file eoff elen poff compressed decoded dict-id trailer p slots)
                  (fn-pwz-cachedp ledger token)
                  (fn-xc-decoded-planp (fn-xcw-plan (fn-xc-row s cells) wins) token)
                  (posp n) (<= (+ p n) end) (<= (+ p n) decoded)
                  (<= (+ p n) (+ (fn-pwz-nth 7 token) (fn-pwz-token-window-length token)))
                  (<= n *fn-ew-span-capacity*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-decoded-span-at fn-xc-entry-span-at fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window) :use fn-xc-decoded-span-at-answers-from-a-matching-slot)))

(defthm fn-xc-entry-span-at-answers-from-a-matching-slot-round5a
  (let* ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r)))
    (implies
     (and (fn-xcsp slots) (fn-xccp cells) (fn-xcep entries) (fn-xc-readyp slots cells)
          (natp from) (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end)
          (equal (mv-nth 0 r) :span))
     (and (natp s) (<= from s) (< s (fn-xc-ne cells))
          (fn-xc-slot-matchp s nil 1 file eoff elen 0 0 0 0 trailer 0 slots)
          (equal (nth s (nth 0 entries)) (fn-xc-entry-key file eoff elen trailer (fn-xc-slot-token s slots)))
          (equal (len (nth s (nth 1 entries))) (+ elen *fn-frame-trailer-octets*))
          (<= eoff poff) (<= (+ poff plen) (+ eoff elen))
          (posp n) (<= (+ p n) end) (<= (+ p n) plen) (<= n *fn-ew-span-capacity*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-decoded-span-at fn-xc-entry-span-at fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window) :use fn-xc-entry-span-at-answers-from-a-matching-slot)))

(defthm fn-xc-entry-span-at-is-the-entry-bytes-round5a
  (let ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)))
    (implies
     (and (fn-xcsp slots) (fn-xccp cells) (fn-xcep entries) (fn-xc-readyp slots cells)
          (natp from) (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end)
          (equal (mv-nth 0 r) :span) (natp k) (< k (mv-nth 1 r)))
     (equal (nth k (nth 0 (mv-nth 3 r)))
            (nth (+ (- poff eoff) p k) (nth (mv-nth 2 r) (nth 1 entries))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-decoded-span-at fn-xc-entry-span-at fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window) :use fn-xc-entry-span-at-is-the-entry-bytes)))

(defthm fn-xc-decoded-span-at-is-the-returned-bytes-round5a
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r))
         (token (fn-xc-slot-token s slots))
         (z (fn-xcw-plan (fn-xc-row s cells) wins))
         (window (fn-xcw-window (fn-xc-row s cells) wins))
         (old (fn-pwz-byte-at returned-ledger worker token z file eoff elen poff compressed trailer decoded dict-id (+ p k) window)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
                  (natp from) (natp p) (natp end) (natp decoded)
                  (equal (mv-nth 0 r) :span) (natp k) (< k n)
                  (equal (fn-pwz-outcome returned-ledger worker token z) :ready))
             (and (equal (mv-nth 0 old) :byte)
                  (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 old)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-decoded-span-at fn-xc-entry-span-at fn-xc-slot-token fn-xc-row fn-xcw-plan fn-xcw-window) :use fn-xc-decoded-span-at-is-the-returned-bytes)))

