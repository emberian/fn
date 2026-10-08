; The host supplies one slot's plan/window under its extent lock.
; FROM may be that slot: lookup repeats the decision without revisiting
; earlier declined slots. The export and theorem statements are unchanged.
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
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-xc-span-end))))

(in-theory (disable fn-xc-span-end))

(defun fn-xc-span-at (from ledger plan file eoff elen poff plen trailer p end
                         fn-xcs fn-xcc fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-ew-buffer fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                              (true-listp plan) (natp from) (natp p)
                              (natp end) (natp plen))))
  (mv-let (word slot)
    (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)
    (if (and (equal word :hit) (natp slot) (< slot (fn-xcs-count fn-xcs))
             (natp p) (natp end) (natp plen))
        (let* ((token (fn-xc-slot-token slot fn-xcs))
               (j (fn-xc-span-end p end plen (fn-prl-nth 7 token) (nth 5 plan))))
          (if (< p j)
              (mv-let (answer fn-ew-span)
                (fn-pwc-span-at ledger token plan file eoff elen poff plen trailer
                                p j fn-ew-buffer fn-ew-span)
                (if (equal answer :span)
                    (mv-let (touch fn-xcs fn-xcc) (fn-xc-touch slot fn-xcs fn-xcc)
                      (declare (ignore touch))
                      (mv :span (- j p) slot fn-ew-span fn-xcs fn-xcc))
                  (mv :miss 0 slot fn-ew-span fn-xcs fn-xcc)))
            (mv :miss 0 slot fn-ew-span fn-xcs fn-xcc)))
      (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc))))

(in-theory (disable fn-xc-token fn-xc-slot-token fn-xc-write-okp fn-xc-free fn-xc-yield))

(defthm fn-xc-find-result-bounded
  (implies (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)
           (and (natp (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))
                (< (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs) hi)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)
           :in-theory (enable fn-xc-find))))

(defthm fn-xc-lookup-result-bounded
  (implies (equal (mv-nth 0 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)) :hit)
           (and (natp (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)))
                (< (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)) (fn-xcs-count fn-xcs))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-lookup fn-xc-readyp fn-xc-hi fn-xc-lo)
           :use (:instance fn-xc-find-result-bounded
                            (i (if (< from (fn-xc-ne fn-xcc)) (fn-xc-ne fn-xcc) from))
                            (hi (+ (fn-xc-ne fn-xcc) (fn-xc-nw fn-xcc)))
                            (exactp nil) (kind 2) (a poff) (b plen) (c 0) (d 0) (pos p)))))

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

(defthm fn-xc-span-at-is-the-returned-bytes
(let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst))
         (token (fn-xc-slot-token (mv-nth 2 r) slots)))
    (implies
     (and (natp k)
          (< k (mv-nth 1 r))
          (equal (fn-pwr-outcome returned-ledger worker token plan) :ready))
     (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (<= (mv-nth 1 r) *fn-ew-span-capacity*)
          (<= (+ p (mv-nth 1 r)) end)
          (<= (+ p (mv-nth 1 r)) plen)
          (<= (+ p (mv-nth 1 r))
              (+ (fn-prl-nth 7 token) (nth 5 plan)))
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))
                 :byte)
          (equal (nth k (nth 0 (mv-nth 3 r)))
                 (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) window))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-span-at)
           :use ((:instance fn-xc-span-end-bounds (start (fn-prl-nth 7 (fn-xc-slot-token (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) slots))) (count (nth 5 plan)))
                 (:instance fn-xc-cached-span-facts (fn-ew-buffer window) (fn-ew-span dst) (token (fn-xc-slot-token (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) slots)) (j (fn-xc-span-end p end plen (fn-prl-nth 7 (fn-xc-slot-token (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) slots)) (nth 5 plan))))
                 (:instance fn-xc-cached-span-is-returned (fn-ew-buffer window) (fn-ew-span dst) (token (fn-xc-slot-token (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) slots)) (j (fn-xc-span-end p end plen (fn-prl-nth 7 (fn-xc-slot-token (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) slots)) (nth 5 plan))))))))

(defthm fn-xc-span-at-answers-an-owed-hit
  (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells))
         (token (fn-xc-slot-token (mv-nth 1 hit) slots))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           slots cells window dst)))
    (implies
     (and (equal (mv-nth 0 hit) :hit)
          (fn-pwc-cachedp ledger token)
          (natp end)
          (< p end)
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p window))
                 :byte))
     (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-span-at fn-pwc-span-at fn-pwr-byte-at fn-pwr-byte fn-pwr-outcome)
           :use ((:instance fn-xc-lookup-result-bounded (fn-xcs slots) (fn-xcc cells))
                 (:instance fn-xc-span-end-bounds (start (fn-prl-nth 7 (fn-xc-slot-token (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) slots))) (count (nth 5 plan)))
                 (:instance fn-xc-span-end-positive (start (fn-prl-nth 7 (fn-xc-slot-token (mv-nth 1 (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p slots cells)) slots))) (count (nth 5 plan)))))))

(defthm fn-xc-span-at-hit-touches-only-the-selected-slot
  (let ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                         slots cells window dst)))
    (implies (equal (mv-nth 0 r) :span)
             (and (equal (mv-nth 4 r)
                         (mv-nth 1 (fn-xc-touch (mv-nth 2 r) slots cells)))
                  (equal (mv-nth 5 r)
                         (mv-nth 2 (fn-xc-touch (mv-nth 2 r) slots cells))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-span-at))))

