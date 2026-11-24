; The transaction admission preflight counts free rows. Reservation scans
; for the first one. Both scans must agree before the member is installed.
(in-package "ACL2")
(include-book "commit-members")
(fn2-book-layer :b)

(local (in-theory (disable fn2-commit-settled-rows fn2-commit-settled-state)))

(local (defthm fn2-cs-count-lower-bound
 (implies (natp k) (<= k (fn2-cs-free-count i k fn2-commit-settled)))
 :rule-classes :linear
 :hints (("Goal" :induct (fn2-cs-free-count i k fn2-commit-settled)))))

(defthm fn2-cs-count-finds-free-row
 (implies (natp k)
          (iff (< k (fn2-cs-free-count i k fn2-commit-settled))
               (fn2-cs-find-free i fn2-commit-settled)))
 :hints (("Goal" :induct (fn2-cs-free-count i k fn2-commit-settled))))

(defthm fn2-cs-found-row-properties
 (let ((r (fn2-cs-find-free i fn2-commit-settled)))
  (implies r
           (and (natp r) (<= i r) (< r (fn2-commit-settled-rows fn2-commit-settled))
                (equal (fn2-commit-settled-state r fn2-commit-settled)
                       *fn2-commit-settled-state-free*))))
 :hints (("Goal" :induct (fn2-cs-find-free i fn2-commit-settled))))

(defthm fn2-cs-refusal-preserves-table
 (let ((reservation (fn2-cs-reserve okind oslot ogen fn2-commit-settled)))
  (implies (not (equal (mv-nth 0 reservation) :ok))
           (equal (mv-nth 2 reservation) fn2-commit-settled)))
 :hints (("Goal" :in-theory (e/d (fn2-cs-reserve) (fn2-cs-rowp fn2-cs-find-free)))))

(defthm fn2-cs-room-implies-reservation
 (implies (and (unsigned-byte-p 32 (fn2-commit-settled-rows fn2-commit-settled))
               (< 0 (fn2-cs-free-count 0 0 fn2-commit-settled))
               (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))
          (equal (mv-nth 0 (fn2-cs-reserve okind oslot ogen fn2-commit-settled)) :ok))
 :hints (("Goal" :in-theory (e/d (fn2-cs-reserve fn2-cs-rowp)
                                 (fn2-cs-find-free fn2-cs-free-count fn2-cs-count-finds-free-row
                                  fn2-cs-found-row-properties))
                 :use ((:instance fn2-cs-count-finds-free-row (i 0) (k 0))
                       (:instance fn2-cs-found-row-properties (i 0))))))

(defthm fn2-cs-reserved-owner-and-frame
 (b* (((mv code r after) (fn2-cs-reserve okind oslot ogen fn2-commit-settled)))
  (implies (and (eq code :ok) (natp i))
           (and (equal (fn2-commit-settled-state i after)
                       (if (equal i r) *fn2-commit-settled-state-reserved*
                         (fn2-commit-settled-state i fn2-commit-settled)))
                (equal (fn2-commit-settled-okind i after)
                       (if (equal i r) okind (fn2-commit-settled-okind i fn2-commit-settled)))
                (equal (fn2-commit-settled-oslot i after)
                       (if (equal i r) oslot (fn2-commit-settled-oslot i fn2-commit-settled)))
                (equal (fn2-commit-settled-ogen i after)
                       (if (equal i r) ogen (fn2-commit-settled-ogen i fn2-commit-settled))))))
 :hints (("Goal" :in-theory (e/d (fn2-cs-reserve fn2-cs-rowp
                                  fn2-commit-settled-state fn2-commit-settled-state$ai
                                  fn2-commit-settled-okind fn2-commit-settled-okind$ai
                                  fn2-commit-settled-oslot fn2-commit-settled-oslot$ai
                                  fn2-commit-settled-ogen fn2-commit-settled-ogen$ai)
                                 (fn2-cs-find-free))))
 :rule-classes nil)
