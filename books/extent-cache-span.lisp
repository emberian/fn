; The warm span walk.  The slot table (extent-cache.lisp) selects candidates by
; start bound only, so the first selected slot can be one whose window ends before
; the requested octet while a later slot holds it.  fn-xc-span-at therefore walks
; the candidates itself, in one call: lookup from FROM, try the selected slot's own
; plan and window (the sibling stobj FN-XCW, one row per window slot), and on a
; decline continue from the next slot, bounded by the slot count.  The host
; decides nothing: it passes FROM = 0 and the descriptor, and installs a window
; with fn-xc-install-window-bytes, which stores the plan and the staged window
; with the slot.  A row left by an evicted or plainly installed window is
; refused by fn-pwc-span-at (the plan must match the slot's token).
(in-package "ACL2")
(include-book "extent-cache")
(include-book "page-window-span")

(defun fn-xc-span-end (p end plen start count)
  (declare (xargs :guard (and (natp p) (natp end) (natp plen))))
  (min (min end plen)
       (min (+ p *fn-ew-span-capacity*) (+ (nfix start) (nfix count)))))

(defthm fn-xc-span-end-bounds
  (implies (and (natp p) (natp end) (natp plen))
           (and (natp (fn-xc-span-end p end plen start count))
                (<= (fn-xc-span-end p end plen start count) end)
                (<= (fn-xc-span-end p end plen start count) plen)
                (<= (fn-xc-span-end p end plen start count) (+ p *fn-ew-span-capacity*))
                (<= (fn-xc-span-end p end plen start count) (+ (nfix start) (nfix count)))))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable fn-xc-span-end))))

(defthm fn-xc-span-end-positive
  (implies (and (natp p) (natp end) (natp plen) (natp start) (natp count)
                (< p end) (< p plen) (< p (+ start count)))
           (< p (fn-xc-span-end p end plen start count)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (enable fn-xc-span-end))))

(defthm fn-xc-span-end-bounds-linear
  (implies (and (natp p) (natp end) (natp plen))
           (and (<= (fn-xc-span-end p end plen start count) end)
                (<= (fn-xc-span-end p end plen start count) plen)
                (<= (fn-xc-span-end p end plen start count) (+ p *fn-ew-span-capacity*))
                (<= (fn-xc-span-end p end plen start count) (+ (nfix start) (nfix count)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-xc-span-end))))

(defthm fn-xc-span-end-natp
  (implies (and (natp p) (natp end) (natp plen))
           (natp (fn-xc-span-end p end plen start count)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-xc-span-end))))

(in-theory (disable fn-xc-span-end))

(defconst *fn-xcw-rows* (fn-profile-limit :extent-cache-windows))

(defmacro fn-xcw-define-window ()
  `(defstobj fn-xcw-win
     (fn-xcw-win-bytes :type (array (unsigned-byte 8) (,(fn-profile-limit :read-window-octets)))
                       :initially 0)
     :inline t :congruent-to fn-ew-buffer))
(fn-xcw-define-window)

(defmacro fn-xcw-define ()
  `(defstobj fn-xcw
     (fn-xcw-plans :type (array t (,(fn-profile-limit :extent-cache-windows))) :initially nil)
     (fn-xcw-wins :type (array fn-xcw-win (,(fn-profile-limit :extent-cache-windows))))))
(fn-xcw-define)

(defun fn-xc-row (slot fn-xcc)
  (declare (xargs :stobjs fn-xcc :guard (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc) (natp slot))))
  (nfix (- slot (fn-xc-ne fn-xcc))))

(defun-nx fn-xcw-plan (row fn-xcw) (nth row (nth 0 fn-xcw)))
(defun-nx fn-xcw-window (row fn-xcw) (nth row (nth 1 fn-xcw)))

(defun fn-xc-span-row (slot ledger file eoff elen poff plen trailer p end
                            fn-xcs fn-xcc fn-xcw fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xcw fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc)
                              (natp slot) (< slot (fn-xcs-count fn-xcs))
                              (natp p) (natp end) (natp plen))))
  (let ((row (fn-xc-row slot fn-xcc)))
    (if (< row (fn-xcw-plans-length fn-xcw))
        (let ((plan (fn-xcw-plansi row fn-xcw))
              (token (fn-xc-slot-token slot fn-xcs)))
          (if (true-listp plan)
              (let ((j (fn-xc-span-end p end plen (fn-prl-nth 7 token) (nth 5 plan))))
                (if (< p j)
                    (stobj-let ((fn-xcw-win (fn-xcw-winsi row fn-xcw)))
                               (answer fn-ew-span)
                      (fn-pwc-span-at ledger token plan file eoff elen poff plen trailer
                                      p j fn-xcw-win fn-ew-span)
                      (mv answer j fn-ew-span))
                  (mv :miss j fn-ew-span)))
            (mv :miss 0 fn-ew-span)))
      (mv :miss 0 fn-ew-span))))

(defthm fn-xc-find-result-bounded
  (implies (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)
           (and (natp (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))
                (< (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs) hi)
                (natp i) (<= i (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)
           :in-theory (enable fn-xc-find))))
(defthm fn-xc-lookup-result-bounded
  (implies (equal (mv-nth 0 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)) :hit)
           (and (natp (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)))
                (< (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)) (fn-xcs-count fn-xcs))
                (implies (natp from) (<= from (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-lookup fn-xc-readyp fn-xc-hi fn-xc-lo)
           :use (:instance fn-xc-find-result-bounded
                            (i (if (< from (fn-xc-ne fn-xcc)) (fn-xc-ne fn-xcc) from))
                            (hi (+ (fn-xc-ne fn-xcc) (fn-xc-nw fn-xcc)))
                            (exactp nil) (kind 2) (a poff) (b plen) (c 0) (d 0) (pos p)))))
(defthm fn-xc-lookup-result-bounded-linear
  (implies (and (equal (mv-nth 0 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)) :hit)
                (natp from))
           (and (<= from (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)))
                (< (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)) (fn-xcs-count fn-xcs))))
  :rule-classes :linear
  :hints (("Goal" :use fn-xc-lookup-result-bounded)))
(defun fn-xc-span-at (from ledger file eoff elen poff plen trailer p end
                         fn-xcs fn-xcc fn-xcw fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xcw fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (natp from) (natp p)
                              (natp end) (natp plen))
                  :measure (nfix (- (fn-xcs-count fn-xcs) (nfix from)))))
  (mv-let (word slot)
    (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)
    (if (and (equal word :hit) (natp from) (natp slot) (< slot (fn-xcs-count fn-xcs))
             (fn-xc-cellsp fn-xcc) (natp p) (natp end) (natp plen))
        (mv-let (answer j fn-ew-span)
          (fn-xc-span-row slot ledger file eoff elen poff plen trailer p end
                          fn-xcs fn-xcc fn-xcw fn-ew-span)
          (if (equal answer :span)
              (mv-let (touch fn-xcs fn-xcc) (fn-xc-touch slot fn-xcs fn-xcc)
                (declare (ignore touch))
                (mv :span (- j p) slot fn-ew-span fn-xcs fn-xcc))
            (fn-xc-span-at (1+ slot) ledger file eoff elen poff plen trailer p end
                           fn-xcs fn-xcc fn-xcw fn-ew-span)))
      (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc))))

(in-theory (disable fn-xc-token fn-xc-slot-token fn-xc-write-okp fn-xc-free fn-xc-yield))

(defthm fn-xc-cached-span-facts
  (implies (equal (mv-nth 0 (fn-pwc-span-at ledger token plan file eoff elen poff plen trailer p j fn-ew-buffer fn-ew-span)) :span)
           (and (fn-pwc-cachedp ledger token)
                (natp (fn-prl-nth 7 token)) (natp (nth 5 plan))
                (<= j plen) (<= j (+ (fn-prl-nth 7 token) (nth 5 plan)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-span-at))))

(defthm fn-xc-cached-span-is-returned
  (implies (and (natp p) (natp j) (< p j) (natp k) (< k (- j p))
                (equal (fn-pwr-outcome returned-ledger worker token plan) :ready)
                (equal (mv-nth 0 (fn-pwc-span-at ledger token plan file eoff elen poff plen trailer p j fn-ew-buffer fn-ew-span)) :span))
           (and (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) fn-ew-buffer)) :byte)
                (equal (nth k (nth 0 (mv-nth 1 (fn-pwc-span-at ledger token plan file eoff elen poff plen trailer p j fn-ew-buffer fn-ew-span))))
                       (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan file eoff elen poff plen trailer (+ p k) fn-ew-buffer)))))
  :rule-classes nil
  :hints (("Goal" :use (fn-xc-cached-span-facts
                         (:instance fn-pwc-span-at-is-the-cached-bytes (s plan) (i p))
                         (:instance fn-pwc-a-hit-is-the-published-window
                                    (ledger returned-ledger) (ledger2 ledger) (s plan) (i (+ p k)))))))


(defthm fn-xc-span-row-unfolds-to-the-cached-span
  (let* ((rr (fn-xc-span-row slot ledger file eoff elen poff plen trailer p end slots cells wins dst))
         (row (fn-xc-row slot cells))
         (plan (fn-xcw-plan row wins))
         (window (fn-xcw-window row wins))
         (token (fn-xc-slot-token slot slots))
         (j (fn-xc-span-end p end plen (fn-prl-nth 7 token) (nth 5 plan))))
    (implies (equal (mv-nth 0 rr) :span)
             (and (< row (fn-xcw-plans-length wins))
                  (true-listp plan)
                  (< p j)
                  (equal (mv-nth 1 rr) j)
                  (equal (mv-nth 0 (fn-pwc-span-at ledger token plan file eoff elen poff plen trailer p j window dst)) :span)
                  (equal (mv-nth 2 rr) (mv-nth 1 (fn-pwc-span-at ledger token plan file eoff elen poff plen trailer p j window dst))))))
  :hints (("Goal" :in-theory (e/d (fn-xc-span-row fn-xcw-plan fn-xcw-window) (fn-xc-slot-token fn-xc-token)))))

(defthm fn-xc-span-row-miss-keeps-the-span-buffer
  (implies (not (equal (mv-nth 0 (fn-xc-span-row slot ledger file eoff elen poff plen trailer p end slots cells wins dst)) :span))
           (equal (mv-nth 2 (fn-xc-span-row slot ledger file eoff elen poff plen trailer p end slots cells wins dst))
                  dst))
  :hints (("Goal" :in-theory (e/d (fn-xc-span-row fn-pwc-span-at) (fn-xc-slot-token fn-xc-token)))))

(defthm fn-xc-lookup-hit-matches
  (implies (equal (mv-nth 0 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) :hit)
           (fn-xc-slot-matchp (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
                              nil 2 file eoff elen poff plen 0 0 trailer p slots))
  :hints (("Goal" :in-theory (enable fn-xc-lookup fn-xc-readyp fn-xc-hi fn-xc-lo)
           :use (:instance fn-xc-find-matches
                            (i (if (< from (fn-xc-ne cells)) (fn-xc-ne cells) from))
                            (hi (+ (fn-xc-ne cells) (fn-xc-nw cells)))
                            (exactp nil) (kind 2) (a poff) (b plen) (c 0) (d 0) (pos p)
                            (fn-xcs slots)))))


(defthm fn-xc-span-at-span-structure
  (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))
         (s (mv-nth 2 r))
         (rr (fn-xc-span-row s ledger file eoff elen poff plen trailer p end slots cells wins dst)))
    (implies (and (equal (mv-nth 0 r) :span))
             (and (natp s) (natp p) (natp end) (natp plen) (and (natp from) (<= from s)) (< s (fn-xcs-count slots))
                  (fn-xc-slot-matchp s nil 2 file eoff elen poff plen 0 0 trailer p slots)
                  (equal (mv-nth 0 rr) :span)
                  (equal (mv-nth 1 r) (- (mv-nth 1 rr) p))
                  (equal (mv-nth 3 r) (mv-nth 2 rr))
                  (equal (mv-nth 4 r) (mv-nth 1 (fn-xc-touch s slots cells)))
                  (equal (mv-nth 5 r) (mv-nth 2 (fn-xc-touch s slots cells))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)
           :in-theory (disable fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp))
          ("Subgoal *1/2" :do-not-induct t :expand ((fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :in-theory (disable fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp fn-xc-span-at)
           :use (fn-xc-lookup-hit-matches fn-xc-lookup-result-bounded-linear))
          ("Subgoal *1/1" :expand ((fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :in-theory (disable fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp))))

(defthm fn-xc-span-at-miss-changes-nothing
  (let ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)))
    (implies (not (equal (mv-nth 0 r) :span))
             (and (equal (mv-nth 0 r) :miss)
                  (equal (mv-nth 1 r) 0)
                  (equal (mv-nth 2 r) nil)
                  (equal (mv-nth 3 r) dst)
                  (equal (mv-nth 4 r) slots)
                  (equal (mv-nth 5 r) cells))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)
           :in-theory (disable fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp))
          ("Subgoal *1/2" :in-theory (disable fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp)
           :use (fn-xc-span-row-miss-keeps-the-span-buffer))))

(defthm fn-xc-span-at-span-count
  (implies (equal (mv-nth 0 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :span)
           (posp (mv-nth 1 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-span-row fn-xc-span-at fn-xcw-plan fn-xcw-window fn-xc-row)
           :use (fn-xc-span-at-span-structure
                 (:instance fn-xc-span-row-unfolds-to-the-cached-span (slot (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))))
                 (:instance fn-xc-span-end-bounds (start (fn-prl-nth 7 (fn-xc-slot-token (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) slots))) (count (nth 5 (fn-xcw-plan (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins))))))))

(defthm fn-xc-span-at-is-the-returned-bytes
  (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))
         (s (mv-nth 2 r))
         (token (fn-xc-slot-token s slots))
         (plan (fn-xcw-plan (fn-xc-row s cells) wins))
         (window (fn-xcw-window (fn-xc-row s cells) wins)))
    (implies
     (and (natp k)
          (< k (mv-nth 1 r))
          (equal (fn-pwr-outcome returned-ledger worker token plan) :ready))
     (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (<= (mv-nth 1 r) *fn-ew-span-capacity*)
          (<= (+ p (mv-nth 1 r)) end)
          (<= (+ p (mv-nth 1 r)) plen)
          (<= (+ p (mv-nth 1 r)) (+ (fn-prl-nth 7 token) (nth 5 plan)))
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer (+ p k) window))
                 :byte)
          (equal (nth k (nth 0 (mv-nth 3 r)))
                 (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer (+ p k) window))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-span-row fn-xc-span-at fn-xcw-plan fn-xcw-window fn-xc-row)
           :use (fn-xc-span-at-span-structure fn-xc-span-at-span-count fn-xc-span-at-miss-changes-nothing
                 (:instance fn-xc-span-row-unfolds-to-the-cached-span (slot (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))))
                 (:instance fn-xc-span-end-bounds (start (fn-prl-nth 7 (fn-xc-slot-token (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) slots))) (count (nth 5 (fn-xcw-plan (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins))))
                 (:instance fn-xc-cached-span-facts (fn-ew-buffer (fn-xcw-window (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins)) (fn-ew-span dst) (token (fn-xc-slot-token (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) slots)) (plan (fn-xcw-plan (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins)) (j (fn-xc-span-end p end plen (fn-prl-nth 7 (fn-xc-slot-token (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) slots)) (nth 5 (fn-xcw-plan (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins)))))
                 (:instance fn-xc-cached-span-is-returned (fn-ew-buffer (fn-xcw-window (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins)) (fn-ew-span dst) (token (fn-xc-slot-token (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) slots)) (plan (fn-xcw-plan (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins)) (j (fn-xc-span-end p end plen (fn-prl-nth 7 (fn-xc-slot-token (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) slots)) (nth 5 (fn-xcw-plan (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins)))))))))

(defthm fn-xc-lookup-covers-a-held-slot
  (implies (and (fn-xccp cells) (fn-xc-readyp slots cells)
                (natp from) (natp p) (natp i) (<= from i)
                (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells)))
                (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots))
           (and (equal (mv-nth 0 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) :hit)
                (<= (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) i)))
  :hints (("Goal" :in-theory (enable fn-xc-lookup fn-xc-readyp fn-xc-hi fn-xc-lo)
           :use (:instance fn-xc-find-complete
                            (i (if (< from (fn-xc-ne cells)) (fn-xc-ne cells) from))
                            (j i) (hi (+ (fn-xc-ne cells) (fn-xc-nw cells)))
                            (exactp nil) (kind 2) (a poff) (b plen) (c 0) (d 0) (pos p)
                            (fn-xcs slots)))))

(defthm fn-xc-row-bound
  (implies (and (fn-xccp cells) (fn-xc-cellsp cells) (natp i)
                (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells)))
                (<= (fn-xc-nw cells) (fn-xcw-plans-length wins)))
           (< (fn-xc-row i cells) (fn-xcw-plans-length wins)))
  :hints (("Goal" :in-theory (enable fn-xc-row fn-xcw-plans-length))))

(defthm fn-xc-cached-byte-gives-a-span
  (implies (and (fn-pwc-cachedp ledger token)
                (natp p) (natp j) (< p j) (<= j plen)
                (natp (fn-prl-nth 7 token)) (natp (nth 5 plan))
                (<= j (+ (fn-prl-nth 7 token) (nth 5 plan)))
                (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                                file eoff elen poff plen trailer p window))
                       :byte))
           (equal (mv-nth 0 (fn-pwc-span-at ledger token plan file eoff elen poff plen trailer p j window dst))
                  :span))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-span-at fn-pwr-byte-at fn-pwr-byte fn-pwr-outcome))))

(defthm fn-xc-byte-at-facts
  (implies (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                           file eoff elen poff plen trailer p window))
                  :byte)
           (and (natp (fn-prl-nth 7 token)) (natp (nth 5 plan)) (natp plen) (natp p)
                (<= (fn-prl-nth 7 token) p)
                (< p plen)
                (< p (+ (fn-prl-nth 7 token) (nth 5 plan)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-byte-at fn-pwr-byte fn-pwr-outcome))))


(defthm fn-xc-span-row-answers-a-covered-slot
  (let* ((row (fn-xc-row i cells))
         (token (fn-xc-slot-token i slots))
         (plan (fn-xcw-plan row wins))
         (window (fn-xcw-window row wins)))
    (implies (and (natp i) (< i (fn-xcs-count slots)) (fn-xccp cells) (fn-xc-cellsp cells)
                  (natp p) (natp end) (natp plen) (< p end)
                  (< row (fn-xcw-plans-length wins))
                  (fn-pwc-cachedp ledger token) (true-listp plan)
                  (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                                  file eoff elen poff plen trailer p window))
                         :byte))
             (equal (mv-nth 0 (fn-xc-span-row i ledger file eoff elen poff plen trailer p end slots cells wins dst))
                    :span)))
  :hints (("Goal" :in-theory (e/d (fn-xc-span-row fn-xcw-plan fn-xcw-window) (fn-xc-slot-token fn-xc-token fn-xc-row))
           :use ((:instance fn-xc-byte-at-facts (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan (fn-xc-row i cells) wins)) (window (fn-xcw-window (fn-xc-row i cells) wins)))
                 (:instance fn-xc-span-end-bounds (start (fn-prl-nth 7 (fn-xc-slot-token i slots))) (count (nth 5 (fn-xcw-plan (fn-xc-row i cells) wins))))
                 (:instance fn-xc-span-end-positive (start (fn-prl-nth 7 (fn-xc-slot-token i slots))) (count (nth 5 (fn-xcw-plan (fn-xc-row i cells) wins))))
                 (:instance fn-xc-cached-byte-gives-a-span (token (fn-xc-slot-token i slots)) (plan (fn-xcw-plan (fn-xc-row i cells) wins)) (window (fn-xcw-window (fn-xc-row i cells) wins))
                            (j (fn-xc-span-end p end plen (fn-prl-nth 7 (fn-xc-slot-token i slots)) (nth 5 (fn-xcw-plan (fn-xc-row i cells) wins)))))))))

(defthm fn-xc-lookup-covers-hit
  (implies (and (fn-xccp cells) (fn-xc-readyp slots cells)
                (natp from) (natp p) (natp i) (<= from i)
                (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells)))
                (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots))
           (equal (mv-nth 0 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) :hit))
  :hints (("Goal" :use fn-xc-lookup-covers-a-held-slot)))

(defthm fn-xc-lookup-covers-le
  (implies (and (fn-xccp cells) (fn-xc-readyp slots cells)
                (natp from) (natp p) (natp i) (<= from i)
                (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells)))
                (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots))
           (<= (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) i))
  :rule-classes :linear
  :hints (("Goal" :use fn-xc-lookup-covers-a-held-slot)))


(defthm fn-xc-span-at-reaches-a-covered-slot
  (implies
   (and (fn-xccp cells) (fn-xc-readyp slots cells)
        (natp from) (natp i) (<= from i)
        (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells)))
        (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)
        (natp p) (natp end) (natp plen)
        (fn-xc-cellsp cells) (< i (fn-xcs-count slots))
        (equal (mv-nth 0 (fn-xc-span-row i ledger file eoff elen poff plen trailer p end slots cells wins dst))
               :span))
   (let ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)))
     (and (equal (mv-nth 0 r) :span)
          (natp (mv-nth 2 r))
          (<= from (mv-nth 2 r))
          (<= (mv-nth 2 r) i))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)
           :in-theory (disable fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp))
          ("Subgoal *1/3" :cases ((equal (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) i)) :expand ((fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :in-theory (disable fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp fn-xc-span-at)
           :use (fn-xc-lookup-hit-matches
                 (:instance fn-xc-lookup-result-bounded-linear (fn-xcs slots) (fn-xcc cells))))
          ("Subgoal *1/2" :cases ((equal (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) i)) :expand ((fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :in-theory (disable fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp fn-xc-span-at)
           :use (fn-xc-lookup-hit-matches
                 (:instance fn-xc-lookup-result-bounded-linear (fn-xcs slots) (fn-xcc cells))))
          ("Subgoal *1/1" :cases ((equal (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) i)) :expand ((fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :in-theory (disable fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp fn-xc-span-at)
           :use (fn-xc-lookup-hit-matches
                 (:instance fn-xc-lookup-result-bounded-linear (fn-xcs slots) (fn-xcc cells))))))


(defthm fn-xc-span-at-answers-a-covered-slot
  (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))
         (row (fn-xc-row i cells))
         (token (fn-xc-slot-token i slots))
         (plan (fn-xcw-plan row wins))
         (window (fn-xcw-window row wins)))
    (implies
     (and (and (fn-xccp cells) (fn-xc-readyp slots cells))
          (and (natp from) (<= from i))
          (and (natp i) (<= (fn-xc-ne cells) i) (< i (+ (fn-xc-ne cells) (fn-xc-nw cells))))
          (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))
          (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots)
          (natp end)
          (< p end)
          (fn-pwc-cachedp ledger token)
          (true-listp plan)
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte))
     (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (natp (mv-nth 2 r))
          (<= from (mv-nth 2 r))
          (<= (mv-nth 2 r) i))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-span-at fn-xc-span-row fn-xcw-plan fn-xcw-window fn-xc-row)
           :use (fn-xc-readyp-facts fn-xc-row-bound
                 fn-xc-span-row-answers-a-covered-slot
                 fn-xc-span-at-reaches-a-covered-slot
                 (:instance fn-xc-byte-at-facts (token (fn-xc-slot-token i slots))
                            (plan (fn-xcw-plan (fn-xc-row i cells) wins))
                            (window (fn-xcw-window (fn-xc-row i cells) wins)))
                 (:instance fn-xc-span-at-span-count)))))


(defthm fn-xc-cached-span-binds-plan-to-token
  (implies (equal (mv-nth 0 (fn-pwc-span-at ledger token plan file eoff elen poff plen trailer p j fn-ew-buffer fn-ew-span)) :span)
           (and (fn-pwc-cachedp ledger token)
                (fn-pwr-plan-matches-token plan token)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-span-at))))

(defthm fn-xc-span-at-answers-from-a-matching-slot
  (let* ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))
         (s (mv-nth 2 r))
         (token (fn-xc-slot-token s slots))
         (plan (fn-xcw-plan (fn-xc-row s cells) wins)))
    (implies (equal (mv-nth 0 r) :span)
             (and (natp s)
                  (and (natp from) (<= from s))
                  (< s (fn-xcs-count slots))
                  (fn-xc-slot-matchp s nil 2 file eoff elen poff plen 0 0 trailer p slots)
                  (fn-pwc-cachedp ledger token)
                  (fn-pwr-plan-matches-token plan token))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-span-row fn-xc-span-at fn-xcw-plan fn-xcw-window fn-xc-row)
           :use (fn-xc-span-at-span-structure
                 (:instance fn-xc-span-row-unfolds-to-the-cached-span (slot (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))))
                 (:instance fn-xc-cached-span-binds-plan-to-token
                            (token (fn-xc-slot-token (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) slots)) (plan (fn-xcw-plan (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins)) (j (fn-xc-span-end p end plen (fn-prl-nth 7 (fn-xc-slot-token (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) slots)) (nth 5 (fn-xcw-plan (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins)))) (fn-ew-buffer (fn-xcw-window (fn-xc-row (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) cells) wins)) (fn-ew-span dst))))))

(defthm fn-xc-span-at-hit-touches-only-the-selected-slot
  (let ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)))
    (and (equal (mv-nth 4 r)
                (mv-nth 1 (fn-xc-touch (mv-nth 2 r) slots cells)))
         (equal (mv-nth 5 r)
                (mv-nth 2 (fn-xc-touch (mv-nth 2 r) slots cells)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-touch) (fn-xc-span-row fn-xc-span-at))
           :use (fn-xc-span-at-span-structure fn-xc-span-at-miss-changes-nothing))))

(defthm fn-xc-span-at-answers-in-the-window-region
  (implies (and (fn-xccp cells) (fn-xc-readyp slots cells) (natp from) (natp p)
                (equal (mv-nth 0 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :span))
           (and (<= (fn-xc-ne cells) (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)))
                (< (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) (+ (fn-xc-ne cells) (fn-xc-nw cells)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)
           :in-theory (disable fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp))
          ("Subgoal *1/3" :expand ((fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :in-theory (e/d (fn-xc-lo fn-xc-hi) (fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp fn-xc-span-at fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp))
           :use ((:instance fn-xc-lookup-hit-is-the-descriptor (kind 2) (a poff) (b plen) (c 0) (d 0) (pos p) (fn-xcs slots) (fn-xcc cells))))
          ("Subgoal *1/2" :expand ((fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :in-theory (e/d (fn-xc-lo fn-xc-hi) (fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp fn-xc-span-at fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp))
           :use ((:instance fn-xc-lookup-hit-is-the-descriptor (kind 2) (a poff) (b plen) (c 0) (d 0) (pos p) (fn-xcs slots) (fn-xcc cells))))
          ("Subgoal *1/1" :expand ((fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :in-theory (e/d (fn-xc-lo fn-xc-hi) (fn-xc-span-row fn-xc-touch fn-xc-lookup fn-xc-slot-matchp fn-xc-span-at fn-xc-span-row-unfolds-to-the-cached-span fn-xc-span-end-natp))
           :use ((:instance fn-xc-lookup-hit-is-the-descriptor (kind 2) (a poff) (b plen) (c 0) (d 0) (pos p) (fn-xcs slots) (fn-xcc cells))))))


(defthm fn-xc-span-at-answers-no-earlier-than-the-first-candidate
  (implies (and (fn-xccp cells) (fn-xc-readyp slots cells) (natp from) (natp p)
                (equal (mv-nth 0 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)) :span))
           (<= (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-span-at fn-xc-lookup fn-xc-slot-matchp fn-xc-lookup-covers-le fn-xc-lookup-covers-hit)
           :use (fn-xc-span-at-answers-in-the-window-region
                 fn-xc-span-at-answers-from-a-matching-slot
                 (:instance fn-xc-lookup-covers-le (i (mv-nth 2 (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst))))))))

(defthm fn-xc-span-at-answers-an-owed-hit
  (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (i (mv-nth 1 hit))
         (token (fn-xc-slot-token i slots))
         (plan (fn-xcw-plan (fn-xc-row i cells) wins))
         (window (fn-xcw-window (fn-xc-row i cells) wins))
         (r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst)))
    (implies
     (and (and (fn-xccp cells) (fn-xc-readyp slots cells))
          (natp from)
          (equal (mv-nth 0 hit) :hit)
          (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))
          (fn-pwc-cachedp ledger token)
          (true-listp plan)
          (natp end)
          (< p end)
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte))
     (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-lo fn-xc-hi) (fn-xc-span-at fn-xc-lookup fn-xcw-plan fn-xcw-window fn-xc-row fn-xc-slot-matchp))
           :use ((:instance fn-xc-span-at-answers-a-covered-slot (i (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))))
                 (:instance fn-xc-lookup-hit-is-the-descriptor (kind 2) (a poff) (b plen) (c 0) (d 0) (pos p) (fn-xcs slots) (fn-xcc cells))
                 (:instance fn-xc-byte-at-facts (token (fn-xc-slot-token (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) slots))
                            (plan (fn-xcw-plan (fn-xc-row (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) cells) wins))
                            (window (fn-xcw-window (fn-xc-row (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) cells) wins)))
                 fn-xc-lookup-hit-matches
                 fn-xc-span-at-answers-no-earlier-than-the-first-candidate))))

(local
 (defthm fn-xcw-bytesp-nth
   (implies (and (fn-ew-bytesp x) (natp i) (< i (len x)))
            (and (integerp (nth i x)) (<= 0 (nth i x)) (< (nth i x) 256)))
   :rule-classes
   ((:rewrite :corollary (implies (and (fn-ew-bytesp x) (natp i) (< i (len x)))
                                  (integerp (nth i x))))
    (:linear :corollary (implies (and (fn-ew-bytesp x) (natp i) (< i (len x)))
                                 (<= 0 (nth i x))))
    (:linear :corollary (implies (and (fn-ew-bytesp x) (natp i) (< i (len x)))
                                 (< (nth i x) 256))))))

(defun fn-xcw-copy (src count dst fn-ew-buffer fn-xcw-win)
  (declare (xargs :stobjs (fn-ew-buffer fn-xcw-win)
                  :guard (and (natp src) (natp count) (natp dst)
                              (<= (+ src count) (fn-profile-limit :read-window-octets))
                              (<= (+ dst count) (fn-profile-limit :read-window-octets)))
                  :measure (nfix count)))
  (if (zp count) fn-xcw-win
    (let ((fn-xcw-win
            (update-fn-xcw-win-bytesi dst (fn-ew-bytesi src fn-ew-buffer) fn-xcw-win)))
      (fn-xcw-copy (+ 1 src) (1- count) (+ 1 dst) fn-ew-buffer fn-xcw-win))))

(local
 (defthm fn-xcw-nth-update
   (implies (and (natp i) (natp j))
            (equal (nth i (update-nth j v xs))
                   (if (equal i j) v (nth i xs))))))

(defthm fn-xcw-copy-exact-output-and-effects
  (implies (and (natp src) (natp count) (natp dst) (natp j))
           (equal (nth j (nth 0 (fn-xcw-copy src count dst fn-ew-buffer fn-xcw-win)))
                  (if (and (<= dst j) (< j (+ dst count)))
                      (nth (+ src (- j dst)) (nth 0 fn-ew-buffer))
                    (nth j (nth 0 fn-xcw-win)))))
  :hints (("Goal" :induct (fn-xcw-copy src count dst fn-ew-buffer fn-xcw-win)
           :in-theory (enable update-fn-xcw-win-bytesi fn-ew-bytesi))))

(in-theory (disable fn-xcw-copy))

; The octets a plan publishes: its length column when it is a natural within
; the window, else none.
(defun fn-xcw-plan-octets (plan)
  (declare (xargs :guard t))
  (let ((c (and (true-listp plan) (nth 5 plan))))
    (if (and (natp c) (<= c (fn-profile-limit :read-window-octets))) c 0)))

; The store step: slot SLOT's row gets PLAN and the first octets of the staged window.
(defun fn-xcw-store (slot plan fn-xcc fn-xcw fn-ew-buffer)
  (declare (xargs :stobjs (fn-xcc fn-xcw fn-ew-buffer)
                  :guard (and (fn-xccp fn-xcc) (natp slot))))
  (if (and (fn-xc-cellsp fn-xcc) (<= (fn-xc-ne fn-xcc) slot)
           (< (fn-xc-row slot fn-xcc) (fn-xcw-plans-length fn-xcw)))
      (let* ((row (fn-xc-row slot fn-xcc))
             (fn-xcw (update-fn-xcw-plansi row plan fn-xcw)))
        (stobj-let ((fn-xcw-win (fn-xcw-winsi row fn-xcw)))
                   (fn-xcw-win)
          (fn-xcw-copy 0 (fn-xcw-plan-octets plan) 0 fn-ew-buffer fn-xcw-win)
          fn-xcw))
    fn-xcw))

(defun fn-xc-install-window-bytes (token plan fn-xcs fn-xcc fn-xcw fn-ew-buffer)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-xcw fn-ew-buffer)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (mv-let (word slot evicted fn-xcs fn-xcc)
    (fn-xc-install-window token fn-xcs fn-xcc)
    (if (and (member-equal word '(:installed :replaced)) (natp slot))
        (let ((fn-xcw (fn-xcw-store slot plan fn-xcc fn-xcw fn-ew-buffer)))
          (mv word slot evicted fn-xcs fn-xcc fn-xcw))
      (mv word slot evicted fn-xcs fn-xcc fn-xcw))))

(local
 (defthm fn-xcw-store-stores-the-plan
   (let ((wins2 (fn-xcw-store slot plan cells wins buf))
         (row (fn-xc-row slot cells)))
     (implies (and (fn-xc-cellsp cells) (<= (fn-xc-ne cells) slot)
                   (< row (fn-xcw-plans-length wins)))
              (equal (fn-xcw-plan row wins2) plan)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-xcw-store fn-xcw-plan)))))

(local
 (defthm fn-xcw-store-stores-the-octets
   (let ((wins2 (fn-xcw-store slot plan cells wins buf))
         (row (fn-xc-row slot cells)))
     (implies (and (fn-xc-cellsp cells) (<= (fn-xc-ne cells) slot)
                   (< row (fn-xcw-plans-length wins))
                   (natp j) (< j (fn-xcw-plan-octets plan)))
              (equal (nth j (nth 0 (fn-xcw-window row wins2)))
                     (nth j (nth 0 buf)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-xcw-store fn-xcw-window) (fn-xcw-copy-exact-output-and-effects))
            :use (:instance fn-xcw-copy-exact-output-and-effects
                            (src 0) (dst 0) (count (fn-xcw-plan-octets plan))
                            (fn-ew-buffer buf)
                            (fn-xcw-win (nth (fn-xc-row slot cells) (nth 1 wins))))))))

(defthm fn-xcw-store-stores-the-pair
  (let ((wins2 (fn-xcw-store slot plan cells wins buf))
        (row (fn-xc-row slot cells)))
    (implies (and (fn-xc-cellsp cells) (<= (fn-xc-ne cells) slot)
                  (< row (fn-xcw-plans-length wins)))
             (and (equal (fn-xcw-plan row wins2) plan)
                  (implies (and (natp j) (< j (fn-xcw-plan-octets plan)))
                           (equal (nth j (nth 0 (fn-xcw-window row wins2)))
                                  (nth j (nth 0 buf)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xcw-store fn-xcw-plan fn-xcw-window fn-xcw-plan-octets)
           :use (fn-xcw-store-stores-the-plan fn-xcw-store-stores-the-octets))))

(defthm fn-xcw-store-leaves-other-rows
  (implies (and (fn-xcwp wins) (fn-xccp cells) (fn-xc-cellsp cells) (natp slot)
                (natp other) (not (equal other (fn-xc-row slot cells))))
           (and (equal (fn-xcw-plan other (fn-xcw-store slot plan cells wins buf))
                       (fn-xcw-plan other wins))
                (equal (fn-xcw-window other (fn-xcw-store slot plan cells wins buf))
                       (fn-xcw-window other wins))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xcw-store fn-xcw-plan fn-xcw-window fn-xcwp))))

(defthm fn-xcw-store-refuses-outside-the-rows
  (implies (not (and (fn-xc-cellsp cells) (<= (fn-xc-ne cells) slot)
                     (< (fn-xc-row slot cells) (fn-xcw-plans-length wins))))
           (equal (fn-xcw-store slot plan cells wins buf) wins))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xcw-store))))

(defthm fn-xc-install-window-bytes-installs-the-table-decision
  (let ((r (fn-xc-install-window-bytes token plan slots cells wins buf))
        (q (fn-xc-install-window token slots cells)))
    (and (equal (mv-nth 0 r) (mv-nth 0 q))
         (equal (mv-nth 1 r) (mv-nth 1 q))
         (equal (mv-nth 2 r) (mv-nth 2 q))
         (equal (mv-nth 3 r) (mv-nth 3 q))
         (equal (mv-nth 4 r) (mv-nth 4 q))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-install-window-bytes) (fn-xc-install-window fn-xcw-store)))))

(defthm fn-xc-install-window-bytes-stores-the-pair
  (let* ((r (fn-xc-install-window-bytes token plan slots cells wins buf))
         (slot (mv-nth 1 r))
         (row (fn-xc-row slot (mv-nth 4 r)))
         (wins2 (mv-nth 5 r)))
    (implies (and (member-equal (mv-nth 0 r) '(:installed :replaced))
                  (natp slot) (fn-xc-cellsp (mv-nth 4 r))
                  (<= (fn-xc-ne (mv-nth 4 r)) slot)
                  (< row (fn-xcw-plans-length wins)))
             (and (equal (fn-xcw-plan row wins2) plan)
                  (implies (and (natp j) (< j (fn-xcw-plan-octets plan)))
                           (equal (nth j (nth 0 (fn-xcw-window row wins2)))
                                  (nth j (nth 0 buf)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-install-window-bytes) (fn-xc-install-window fn-xcw-store))
           :use (:instance fn-xcw-store-stores-the-pair
                           (slot (mv-nth 1 (fn-xc-install-window token slots cells)))
                           (cells (mv-nth 4 (fn-xc-install-window token slots cells)))))))

(defthm fn-xc-install-window-bytes-leaves-other-rows
  (let* ((r (fn-xc-install-window-bytes token plan slots cells wins buf))
         (slot (mv-nth 1 r))
         (row (fn-xc-row slot (mv-nth 4 r)))
         (wins2 (mv-nth 5 r)))
    (implies (and (fn-xcwp wins) (fn-xccp (mv-nth 4 r)) (fn-xc-cellsp (mv-nth 4 r))
                  (natp other) (not (equal other row)) (natp slot))
             (and (equal (fn-xcw-plan other wins2) (fn-xcw-plan other wins))
                  (equal (fn-xcw-window other wins2) (fn-xcw-window other wins)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-install-window-bytes) (fn-xc-install-window fn-xcw-store))
           :use (:instance fn-xcw-store-leaves-other-rows
                           (slot (mv-nth 1 (fn-xc-install-window token slots cells)))
                           (cells (mv-nth 4 (fn-xc-install-window token slots cells)))))))

(defthm fn-xc-install-window-bytes-keeps-the-rows-unless-it-installs
  (let ((r (fn-xc-install-window-bytes token plan slots cells wins buf)))
    (implies (not (member-equal (mv-nth 0 r) '(:installed :replaced)))
             (equal (mv-nth 5 r) wins)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-install-window-bytes) (fn-xc-install-window fn-xcw-store)))))

(defconst *fn-xcw-rows* (fn-profile-limit :extent-cache-windows))

(defun fn-xc-init-windows (ne nw fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (if (and (natp nw) (< *fn-xcw-rows* nw))
      (mv :refused-window-rows fn-xcs fn-xcc)
    (fn-xc-init ne nw fn-xcs fn-xcc)))


(defthm fn-xcw-plans-length-is-the-profile-row-count
  (equal (fn-xcw-plans-length wins) *fn-xcw-rows*))

(defthm fn-xc-init-windows-refuses-more-windows-than-rows
  (implies (and (natp nw) (< *fn-xcw-rows* nw))
           (and (equal (mv-nth 0 (fn-xc-init-windows ne nw slots cells)) :refused-window-rows)
                (equal (mv-nth 1 (fn-xc-init-windows ne nw slots cells)) slots)
                (equal (mv-nth 2 (fn-xc-init-windows ne nw slots cells)) cells)))
  :hints (("Goal" :in-theory (enable fn-xc-init-windows))))

(defthm fn-xc-init-windows-readies-the-rows
  (implies (and (fn-xcsp slots) (fn-xccp cells)
                (equal (fn-xcs-count slots) 0) (equal (fn-xcc-count cells) 0)
                (natp ne) (natp nw) (<= ne *fn-xc-max-slots*) (<= nw *fn-xcw-rows*))
           (let ((r (fn-xc-init-windows ne nw slots cells)))
             (and (equal (mv-nth 0 r) :initialized)
                  (fn-xcsp (mv-nth 1 r)) (fn-xccp (mv-nth 2 r))
                  (fn-xc-readyp (mv-nth 1 r) (mv-nth 2 r))
                  (equal (fn-xc-nw (mv-nth 2 r)) nw)
                  (<= (fn-xc-nw (mv-nth 2 r)) (fn-xcw-plans-length wins)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-init-windows)
           :use ((:instance fn-xc-init-initializes (fn-xcs slots) (fn-xcc cells))
                 fn-xcw-plans-length-is-the-profile-row-count))))

(defthm fn-xc-span-at-never-answers-a-freed-slot
  (implies (and (fn-xcsp slots) (natp i) (< i (fn-xcs-count slots))
                (not (equal (fn-xcs-get-kind i slots) 0)))
           (let ((r (fn-xc-span-at from ledger file eoff elen poff plen trailer p end
                                   (mv-nth 2 (fn-xc-free i slots)) cells wins dst)))
             (implies (equal (mv-nth 0 r) :span)
                      (not (equal (mv-nth 2 r) i)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-span-at fn-xc-free)
           :use ((:instance fn-xc-span-at-answers-from-a-matching-slot
                            (slots (mv-nth 2 (fn-xc-free i slots))))
                 (:instance fn-xc-freed-slot-matches-nothing
                            (fn-xcs slots) (kind 2) (exactp nil) (a poff) (b plen) (c 0) (d 0) (pos p) (j 0))))))
