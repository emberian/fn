; Discharges fn2-ops-stale-or-duplicate-post, fn2-ops-outbox-order and
; fn2-ops-result-reservation (books/vocab.lisp) against the runtime exports
; fn2-post-result, fn2-outbox-ack and fn2-op-enqueue themselves.
;
; Shape. Every ops writer is an UPDATE-NTH-ARRAY of one column at one row or
; an UPDATE-NTH of one scalar; those two forms stay closed and are read
; through NTH-UPDATE-NTH(-ARRAY). Each ring and reference traversal is first
; restated over the raw fields it reads (VOP-OB, VOP-PL, VOP-REFSP), so a
; write to any other field frames by rewriting alone.
(in-package "ACL2")
(include-book "vocab")
(include-book "owed-discharge")

; The only arithmetic fact about MOD the rings need: one wrap at most.
(local
 (encapsulate ()
   (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
   (defthm vop-mod-one-wrap
     (implies (and (natp x) (posp c) (< x (* 2 c)))
              (equal (mod x c) (if (< x c) x (- x c))))
     :hints (("Goal" :use ((:instance mod-+-cancel-0 (x (- x c)) (y c) (z c)))
              :in-theory (disable mod-+-cancel-0 mod floor))))))

(local
 (in-theory
  (e/d (fn2-ops-set-phase update-fn2-ops-phase$ai
        fn2-ops-set-c0-posted fn2-ops-set-c0-harvested fn2-ops-set-c0-event
        fn2-ops-set-c0-outcome fn2-ops-set-c0-reason fn2-ops-set-c0-count
        fn2-ops-set-c0-aux0 fn2-ops-set-c0-aux1
        update-fn2-ops-c0-posted$ai update-fn2-ops-c0-harvested$ai
        update-fn2-ops-c0-event$ai update-fn2-ops-c0-outcome$ai
        update-fn2-ops-c0-reason$ai update-fn2-ops-c0-count$ai
        update-fn2-ops-c0-aux0$ai update-fn2-ops-c0-aux1$ai
        update-fn2-ops-out-sloti update-fn2-ops-out-geni
        update-fn2-ops-posted-fifoi
        update-fn2-ops-out-head update-fn2-ops-out-tail update-fn2-ops-queued
        update-fn2-ops-reserved-credits update-fn2-ops-post-tail
        update-fn2-ops-post-count update-fn2-ops-stray
        fn2-ops-rows fn2-ops-out-sloti fn2-ops-out-geni fn2-ops-posted-fifoi
        fn2-ops-out-slot-length fn2-ops-out-gen-length
        fn2-ops-posted-fifo-length
        fn2-ops-out-head fn2-ops-out-tail fn2-ops-queued
        fn2-ops-reserved-credits fn2-ops-post-head fn2-ops-post-tail
        fn2-ops-post-count fn2-ops-stray)
       (update-nth-array update-nth mod floor fn2-ops-wfp fn2-opsp
        fn2-ops-semanticp fn2-ops-row-semanticp fn2-ops-same-membersp
        fn2-ops-ring-shapep fn2-ring-next
        fn2-ops-row-snapshot fn2-op-ack-phase))))

;; ---------------------------------------------------------------------------
;; fn2-ops-stale-or-duplicate-post

(local
 (defthm vop-stray-u60
   (implies (fn2-opsp p) (unsigned-byte-p 60 (nth 63 p)))
   :hints (("Goal" :in-theory (enable fn2-opsp fn2-ops-strayp)))))

(local
 (defthm vop-rows-snapshot-of-stray-write
   (equal (fn2-ops-rows-snapshot n (update-nth 63 v p))
          (fn2-ops-rows-snapshot n p))
   :hints (("Goal" :in-theory (enable fn2-ops-row-snapshot)))))
(local
 (defthm vop-out-slot-snapshot-of-stray-write
   (equal (fn2-ops-out-slot-snapshot n (update-nth 63 v p))
          (fn2-ops-out-slot-snapshot n p))))
(local
 (defthm vop-out-gen-snapshot-of-stray-write
   (equal (fn2-ops-out-gen-snapshot n (update-nth 63 v p))
          (fn2-ops-out-gen-snapshot n p))))
(local
 (defthm vop-posted-fifo-snapshot-of-stray-write
   (equal (fn2-ops-posted-fifo-snapshot n (update-nth 63 v p))
          (fn2-ops-posted-fifo-snapshot n p))))

(local
 (defthm vop-semanticp-opsp
   (implies (fn2-ops-semanticp p) (fn2-opsp p))
   :hints (("Goal" :in-theory (enable fn2-ops-semanticp)))))

(defthm fn2-ops-stale-or-duplicate-post-proved
  (fn2-ops-stale-or-duplicate-post$owed
   cell slot gen evkind outcome reason count aux0 aux1 p)
  :rule-classes nil
  :hints (("Goal"
           :use (vop-semanticp-opsp vop-stray-u60)
           :in-theory (e/d (fn2-ops-stale-or-duplicate-post$owed
                            fn2-ops-stray-hyps fn2-ops-stray-conclusion
                            fn2-ops-stray-resultp fn2-ops-nonstray-snapshot
                            fn2-post-result fn2-post-eligiblep
                            fn2-op-handle-code fn2-op-slotp
                            fn2-count-stray fn2-saturating-inc60)
                           (vop-semanticp-opsp vop-stray-u60
                            fn2-ops-rows-snapshot fn2-ops-out-slot-snapshot
                            fn2-ops-out-gen-snapshot
                            fn2-ops-posted-fifo-snapshot)))))
(fn2-owed-discharge fn2-ops-stale-or-duplicate-post
                    fn2-ops-stale-or-duplicate-post-proved)

;; ---------------------------------------------------------------------------
;; Rings and queued references over the raw fields they read

(local (in-theory (disable vop-mod-one-wrap)))

; From here on (nth k p) is the normal form of every field read, k = 0
; included, so NTH opens only against an explicit CONS.
(local
 (defthm vop-nth-of-cons
   (implies (syntaxp (quotep k))
            (equal (nth k (cons a b)) (if (zp k) a (nth (+ -1 k) b))))))
(local (in-theory (disable nth)))

(local
 (defthm vop-mod-next
   (implies (and (natp i) (natp c) (< i c))
            (equal (mod (+ 1 i) c) (fn2-ring-next i c)))
   :hints (("Goal" :in-theory (enable vop-mod-one-wrap fn2-ring-next)))))
(local
 (defthm vop-ring-next-type
   (implies (and (natp i) (natp c)) (natp (fn2-ring-next i c)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn2-ring-next)))))
(local
 (defthm vop-ring-next-bound
   (implies (and (natp i) (posp c)) (< (fn2-ring-next i c) c))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn2-ring-next)))))

; Forward distance from index i to index tl in a ring of capacity c.
(local
 (defun vop-dist (i tl c)
   (if (<= i tl) (- tl i) (+ (- tl i) c))))
(local
 (defthm vop-dist-type
   (implies (and (natp i) (natp tl) (natp c) (< i c))
            (natp (vop-dist i tl c)))
   :rule-classes :type-prescription))
(local
 (defthm vop-dist-zero
   (implies (and (natp i) (natp tl) (natp c) (< i c) (< tl c))
            (equal (equal (vop-dist i tl c) 0) (equal i tl)))))
(local
 (defthm vop-dist-next
   (implies (and (natp i) (natp tl) (natp c) (< i c) (< tl c)
                 (not (equal i tl)))
            (equal (vop-dist (fn2-ring-next i c) tl c)
                   (+ -1 (vop-dist i tl c))))
   :hints (("Goal" :in-theory (enable fn2-ring-next)))))
(local
 (defthm vop-dist-self
   (equal (vop-dist i i c) 0)))
(local (in-theory (disable vop-dist)))

(local
 (defun vop-ob (left idx slots gens)
   (declare (xargs :measure (nfix left)))
   (if (zp left) nil
     (cons (list (nth idx slots) (nth idx gens))
           (vop-ob (- left 1) (mod (+ 1 (nfix idx)) (len slots))
                   slots gens)))))
(local
 (defthm vop-outbox-list-aux-raw
   (equal (fn2-ops-outbox-list-aux left idx p)
          (vop-ob left idx (nth 45 p) (nth 46 p)))))
(local (in-theory (disable fn2-ops-outbox-list-aux)))

(local
 (defun vop-pl (left idx fifo)
   (declare (xargs :measure (nfix left)))
   (if (zp left) nil
     (cons (nth idx fifo)
           (vop-pl (- left 1) (mod (+ 1 (nfix idx)) (len fifo)) fifo)))))
(local
 (defthm vop-posted-list-aux-raw
   (equal (fn2-ops-posted-list-aux left idx p)
          (vop-pl left idx (nth 47 p)))))
(local (in-theory (disable fn2-ops-posted-list-aux)))

(local
 (defun vop-refsp (refs gens phases rows)
   (if (atom refs) (null refs)
     (and (natp (caar refs)) (< (caar refs) rows)
          (equal (cadar refs) (nth (caar refs) gens))
          (equal (nth (caar refs) phases) 2)
          (vop-refsp (cdr refs) gens phases rows)))))
(local
 (defthm vop-queued-refsp-raw
   (equal (fn2-ops-queued-refsp refs p)
          (vop-refsp refs (nth 0 p) (nth 1 p) (nth 44 p)))
   :hints (("Goal" :in-theory (enable fn2-op-slotp)))))
(local (in-theory (disable fn2-ops-queued-refsp)))

(local
 (defthm vop-pl-one
   (equal (vop-pl 1 i fifo) (list (nth i fifo)))
   :hints (("Goal" :expand ((vop-pl 1 i fifo))))))
(local
 (defthm vop-ob-one
   (equal (vop-ob 1 i slots gens) (list (list (nth i slots) (nth i gens))))
   :hints (("Goal" :expand ((vop-ob 1 i slots gens))))))

; Writing the tail position appends exactly one entry to a non-full ring.
(local
 (defthm vop-pl-push
   (implies (and (natp idx) (natp tl) (natp left)
                 (< idx (len fifo)) (< tl (len fifo))
                 (equal left (vop-dist idx tl (len fifo))))
            (equal (vop-pl (+ 1 left) idx (update-nth tl v fifo))
                   (append (vop-pl left idx fifo) (list v))))
   :hints (("Goal" :induct (vop-pl left idx fifo)
            :expand ((vop-pl (+ 1 left) idx (update-nth tl v fifo)))))))
(local
 (defthm vop-ob-push
   (implies (and (natp idx) (natp tl) (natp left)
                 (< idx (len slots)) (< tl (len slots))
                 (equal left (vop-dist idx tl (len slots))))
            (equal (vop-ob (+ 1 left) idx
                           (update-nth tl s slots) (update-nth tl g gens))
                   (append (vop-ob left idx slots gens) (list (list s g)))))
   :hints (("Goal" :induct (vop-ob left idx slots gens)
            :expand ((vop-ob (+ 1 left) idx
                             (update-nth tl s slots) (update-nth tl g gens)))))))
(local (in-theory (disable vop-pl-push vop-ob-push)))

(local
 (defun vop-ob-ind2 (n m i slots)
   (declare (xargs :measure (nfix n)))
   (if (zp n) (list m i slots)
     (vop-ob-ind2 (- n 1) (- m 1) (mod (+ 1 (nfix i)) (len slots)) slots))))
(local
 (defthm vop-take-of-ob
   (implies (and (natp n) (natp m) (<= n m))
            (equal (take n (vop-ob m i slots gens))
                   (vop-ob n i slots gens)))
   :hints (("Goal" :induct (vop-ob-ind2 n m i slots)))))
(local
 (defthm vop-refsp-ob-prefix
   (implies (and (vop-refsp (vop-ob m i slots gens) g ph r)
                 (natp n) (natp m) (<= n m))
            (vop-refsp (vop-ob n i slots gens) g ph r))
   :rule-classes nil
   :hints (("Goal" :induct (vop-ob-ind2 n m i slots)))))

(local
 (defun vop-slots-okp (refs rows)
   (if (atom refs) t
     (and (natp (caar refs)) (< (caar refs) rows)
          (vop-slots-okp (cdr refs) rows)))))
(local
 (defthm vop-refsp-slots-okp
   (implies (vop-refsp refs g ph r) (vop-slots-okp refs r))))

; On queued references a slot is named iff its (slot gen) pair is listed.
(local
 (defthm vop-ref-member-iff
   (implies (vop-refsp (vop-ob n i slots gens) g ph r)
            (iff (member-equal (list s (nth s g)) (vop-ob n i slots gens))
                 (member-equal s (fn2-ops-ref-slots (vop-ob n i slots gens)))))
   :rule-classes nil
   :hints (("Goal" :induct (vop-ob n i slots gens)))))

(local
 (defthm vop-prefixp-of-refsp
   (implies (and (vop-refsp (vop-ob n idx (nth 45 p) (nth 46 p))
                            (nth 0 p) (nth 1 p) (nth 44 p))
                 (natp idx)
                 (or (zp n) (< idx (len (nth 45 p))))
                 (equal (len (nth 46 p)) (len (nth 45 p))))
            (fn2-outbox-prefixp n idx p))
   :hints (("Goal" :induct (fn2-outbox-prefixp n idx p)
            :in-theory (enable fn2-op-phase-code fn2-op-handle-code
                               fn2-op-slotp)
            :expand ((vop-ob n idx (nth 45 p) (nth 46 p)))))))

;; ---------------------------------------------------------------------------
;; fn2-outbox-submit-prefix, one acknowledged descriptor at a time

; VOP-SUBMIT-OKP is what keeps the loop from stopping early: N descriptors
; are queued at the head and each names a row.
(local
 (defun vop-submit-okp (n p)
   (and (natp n) (integerp (nth 50 p)) (<= n (nth 50 p))
        (natp (nth 48 p))
        (or (zp n) (< (nth 48 p) (len (nth 45 p))))
        (< (len (nth 45 p)) 4294967296)
        (vop-slots-okp (vop-ob n (nth 48 p) (nth 45 p) (nth 46 p))
                       (nth 44 p)))))
(local
 (defun vop-step (p)
   (update-nth 50 (+ -1 (nth 50 p))
    (update-nth 48 (fn2-ring-next (nth 48 p) (len (nth 45 p)))
     (update-nth-array
      1 (nth (nth 48 p) (nth 45 p))
      (fn2-op-ack-phase (nth (nth (nth 48 p) (nth 45 p)) (nth 2 p)))
      p)))))
(local
 (defun vop-submit-ind (n p)
   (declare (xargs :measure (nfix n)))
   (if (zp n) p (vop-submit-ind (+ -1 n) (vop-step p)))))

(local
 (defthm vop-step-reads
   (and (equal (nth 1 (vop-step p))
               (update-nth (nth (nth 48 p) (nth 45 p))
                           (fn2-op-ack-phase
                            (nth (nth (nth 48 p) (nth 45 p)) (nth 2 p)))
                           (nth 1 p)))
        (equal (nth 48 (vop-step p))
               (fn2-ring-next (nth 48 p) (len (nth 45 p))))
        (equal (nth 50 (vop-step p)) (+ -1 (nth 50 p)))
        (implies (and (natp k) (not (equal k 1)) (not (equal k 48))
                      (not (equal k 50)))
                 (equal (nth k (vop-step p)) (nth k p))))))
(local
 (defthm vop-submit-okp-facts
   (implies (and (vop-submit-okp n p) (not (zp n)))
            (and (natp (nth 48 p)) (< (nth 48 p) (len (nth 45 p)))
                 (integerp (nth 50 p)) (<= n (nth 50 p))
                 (< (len (nth 45 p)) 4294967296)
                 (natp (nth (nth 48 p) (nth 45 p)))
                 (< (nth (nth 48 p) (nth 45 p)) (nth 44 p))))
   :rule-classes :forward-chaining
   :hints (("Goal" :expand ((vop-ob n (nth 48 p) (nth 45 p) (nth 46 p)))))))
(local
 (defthm vop-submit-okp-step
   (implies (and (vop-submit-okp n p) (not (zp n)))
            (vop-submit-okp (+ -1 n) (vop-step p)))
   :hints (("Goal" :expand ((vop-ob n (nth 48 p) (nth 45 p) (nth 46 p)))))))
(local
 (defthm vop-submit-zp
   (implies (zp n) (equal (fn2-outbox-submit-prefix n p) p))
   :hints (("Goal" :expand ((fn2-outbox-submit-prefix n p))))))
(local
 (defthm vop-submit-unfold
   (implies (and (vop-submit-okp n p) (not (zp n)))
            (equal (fn2-outbox-submit-prefix n p)
                   (fn2-outbox-submit-prefix (+ -1 n) (vop-step p))))
   :hints (("Goal" :in-theory (enable fn2-op-slotp)
            :expand ((fn2-outbox-submit-prefix n p)
                     (vop-ob n (nth 48 p) (nth 45 p) (nth 46 p)))))))
(local (in-theory (disable vop-submit-okp vop-step vop-submit-unfold)))

; Acknowledgment writes the phase column, the head and the queued count only.
(local
 (defthm vop-submit-frame
   (implies (and (natp k) (not (equal k 1)) (not (equal k 48))
                 (not (equal k 50)))
            (equal (nth k (fn2-outbox-submit-prefix n p)) (nth k p)))
   :hints (("Goal" :in-theory (enable fn2-outbox-submit-prefix)))))

(local
 (defthm vop-submit-phase
   (implies (and (vop-submit-okp n p) (natp s))
            (equal (nth s (nth 1 (fn2-outbox-submit-prefix n p)))
                   (if (member-equal
                        s (fn2-ops-ref-slots
                           (vop-ob n (nth 48 p) (nth 45 p) (nth 46 p))))
                       (fn2-op-ack-phase (nth s (nth 2 p)))
                     (nth s (nth 1 p)))))
   :hints (("Goal" :induct (vop-submit-ind n p)
            :in-theory (enable vop-submit-unfold)
            :expand ((vop-ob n (nth 48 p) (nth 45 p) (nth 46 p)))))))

(local
 (defthm vop-submit-outbox
   (implies (vop-submit-okp n p)
            (equal (vop-ob (nth 50 (fn2-outbox-submit-prefix n p))
                           (nth 48 (fn2-outbox-submit-prefix n p))
                           (nth 45 p) (nth 46 p))
                   (nthcdr n (vop-ob (nth 50 p) (nth 48 p)
                                     (nth 45 p) (nth 46 p)))))
   :hints (("Goal" :induct (vop-submit-ind n p)
            :in-theory (enable vop-submit-unfold)
            :expand ((vop-ob (nth 50 p) (nth 48 p) (nth 45 p) (nth 46 p)))))))

;; ---------------------------------------------------------------------------
;; Row snapshots across an acknowledgment

(local
 (defthm vop-update-nth-1-of-list
   (equal (update-nth 1 v (cons a (cons b rest))) (cons a (cons v rest)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm vop-submit-row
   (implies (and (vop-submit-okp n p)
                 (vop-refsp (vop-ob n (nth 48 p) (nth 45 p) (nth 46 p))
                            (nth 0 p) (nth 1 p) (nth 44 p))
                 (natp i))
            (equal (fn2-ops-row-snapshot i (fn2-outbox-submit-prefix n p))
                   (if (member-equal
                        (list i (car (fn2-ops-row-snapshot i p)))
                        (vop-ob n (nth 48 p) (nth 45 p) (nth 46 p)))
                       (update-nth 1 (fn2-op-ack-phase
                                      (nth 2 (fn2-ops-row-snapshot i p)))
                                   (fn2-ops-row-snapshot i p))
                     (fn2-ops-row-snapshot i p))))
   :hints (("Goal"
            :use ((:instance vop-ref-member-iff
                             (s i) (i (nth 48 p)) (slots (nth 45 p))
                             (gens (nth 46 p)) (g (nth 0 p)) (ph (nth 1 p))
                             (r (nth 44 p))))
            :in-theory (enable fn2-ops-row-snapshot)))))

; The row snapshot, front to back, so it recurs the way the result check does.
(local
 (defun-nx vop-rows-from (i m p)
   (declare (xargs :measure (nfix (- (nfix m) (nfix i)))))
   (if (and (natp i) (natp m) (< i m))
       (cons (fn2-ops-row-snapshot i p) (vop-rows-from (+ 1 i) m p))
     nil)))
(local
 (defthm vop-append-snoc
   (equal (append (append a (list x)) b) (append a (cons x b)))))
(local
 (defthm vop-true-listp-rows-snapshot
   (true-listp (fn2-ops-rows-snapshot n p))
   :rule-classes :type-prescription))
(local
 (defthm vop-append-nil
   (implies (true-listp a) (equal (append a nil) a))))
(local
 (defthm vop-rows-snapshot-split
   (implies (and (natp i) (natp m) (<= i m))
            (equal (append (fn2-ops-rows-snapshot i p) (vop-rows-from i m p))
                   (fn2-ops-rows-snapshot m p)))
   :rule-classes nil
   :hints (("Goal" :induct (vop-rows-from i m p)
            :expand ((fn2-ops-rows-snapshot (+ 1 i) p))))))
(local
 (defthm vop-rows-snapshot-as-rows-from
   (implies (natp m)
            (equal (fn2-ops-rows-snapshot m p) (vop-rows-from 0 m p)))
   :hints (("Goal" :use ((:instance vop-rows-snapshot-split (i 0)))
            :expand ((fn2-ops-rows-snapshot 0 p))))))
(local (in-theory (disable vop-rows-snapshot-as-rows-from)))

(local
 (defthm vop-submit-rows
   (implies (and (vop-submit-okp n p)
                 (vop-refsp (vop-ob n (nth 48 p) (nth 45 p) (nth 46 p))
                            (nth 0 p) (nth 1 p) (nth 44 p))
                 (natp i))
            (fn2-ops-order-rows-resultp
             i (vop-ob n (nth 48 p) (nth 45 p) (nth 46 p))
             (vop-rows-from i m p)
             (vop-rows-from i m (fn2-outbox-submit-prefix n p))))
   :hints (("Goal" :induct (vop-rows-from i m p)))))

;; ---------------------------------------------------------------------------
;; What the proofs read out of fn2-ops-semanticp

(local
 (defthm vop-wfp-rows
   (implies (fn2-ops-wfp p)
            (and (natp (nth 44 p)) (< (nth 44 p) 4294967296)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-ops-wfp)))))

(local
 (defthm vop-sem-facts
   (implies (fn2-ops-semanticp p)
            (and (fn2-ops-wfp p)
                 (unsigned-byte-p 32 (len (nth 45 p)))
                 (equal (len (nth 46 p)) (len (nth 45 p)))
                 (equal (len (nth 47 p)) (* 2 (nth 44 p)))
                 (fn2-ops-ring-shapep (len (nth 45 p)) (nth 48 p) (nth 49 p)
                                      (nth 50 p))
                 (fn2-ops-ring-shapep (* 2 (nth 44 p)) (nth 52 p) (nth 53 p)
                                      (nth 54 p))
                 (fn2-ops-row-semanticp (nth 44 p) p)
                 (equal (nth 51 p)
                        (len (fn2-ops-phase-slots (nth 44 p) 1 p)))
                 (equal (nth 50 p)
                        (len (fn2-ops-phase-slots (nth 44 p) 2 p)))
                 (<= (+ (len (fn2-ops-phase-slots (nth 44 p) 1 p))
                        (len (fn2-ops-phase-slots (nth 44 p) 2 p)))
                     (len (nth 45 p)))
                 (vop-refsp (vop-ob (nth 50 p) (nth 48 p)
                                    (nth 45 p) (nth 46 p))
                            (nth 0 p) (nth 1 p) (nth 44 p))
                 (fn2-ops-same-membersp
                  (vop-pl (nth 54 p) (nth 52 p) (nth 47 p))
                  (fn2-ops-pending-cells (nth 44 p) p))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-ops-semanticp fn2-ops-outbox-list
                                    fn2-ops-posted-list)
                                   (fn2-ops-phase-slots fn2-ops-pending-cells
                                    fn2-ops-free-chain fn2-ops-ref-slots
                                    fn2-ops-outbox-credits vop-ob vop-pl
                                    vop-refsp unsigned-byte-p))))))

(local
 (defthm vop-ring-shape-facts
   (implies (fn2-ops-ring-shapep c h tl n)
            (and (natp c) (natp h) (natp tl) (natp n) (<= n c)
                 (implies (< 0 c) (and (< h c) (< tl c)))
                 (implies (< n c) (equal (vop-dist h tl c) n))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance vop-mod-one-wrap (x (+ h n))))
            :in-theory (enable fn2-ops-ring-shapep vop-dist)))))

;; ---------------------------------------------------------------------------
;; fn2-ops-outbox-order

(local
 (defthm vop-sem-ack-ready
   (implies (and (fn2-ops-semanticp p) (natp n) (<= n (nth 50 p)))
            (and (vop-submit-okp n p)
                 (vop-refsp (vop-ob n (nth 48 p) (nth 45 p) (nth 46 p))
                            (nth 0 p) (nth 1 p) (nth 44 p))
                 (fn2-outbox-prefixp n (nth 48 p) p)
                 (natp (nth 44 p)) (natp (nth 50 p))
                 (< (len (nth 45 p)) 4294967296)))
   :hints (("Goal"
            :use (vop-sem-facts vop-wfp-rows
                  (:instance vop-ring-shape-facts
                             (c (len (nth 45 p))) (h (nth 48 p))
                             (tl (nth 49 p)) (n (nth 50 p)))
                  (:instance vop-refsp-ob-prefix
                             (m (nth 50 p)) (i (nth 48 p))
                             (slots (nth 45 p)) (gens (nth 46 p))
                             (g (nth 0 p)) (ph (nth 1 p)) (r (nth 44 p))))
            :in-theory (e/d (vop-submit-okp)
                            (vop-ob vop-refsp fn2-outbox-prefixp))))))

(defthm fn2-ops-outbox-order-proved
  (fn2-ops-outbox-order$owed n p)
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn2-ops-outbox-order$owed fn2-ops-order-hyps
                            fn2-ops-order-conclusion fn2-ops-order-resultp
                            fn2-outbox-ack fn2-ops-outbox-list
                            vop-rows-snapshot-as-rows-from)
                           (fn2-ops-rows-snapshot vop-rows-from vop-ob
                            vop-refsp fn2-outbox-prefixp
                            fn2-ops-order-rows-resultp take nthcdr)))))
(fn2-owed-discharge fn2-ops-outbox-order fn2-ops-outbox-order-proved)

;; ---------------------------------------------------------------------------
;; fn2-ops-result-reservation: counting facts

(local
 (defthm vop-len-pl
   (equal (len (vop-pl left idx fifo)) (nfix left))))

; A duplicate-free list inside another is no longer than it.
(local
 (defthm vop-len-remove1
   (implies (member-equal x b)
            (equal (len (remove1-equal x b)) (+ -1 (len b))))))
(local
 (defthm vop-member-remove1
   (implies (not (equal x y))
            (iff (member-equal y (remove1-equal x b)) (member-equal y b)))))
(local
 (defthm vop-subsetp-remove1
   (implies (and (subsetp-equal a b) (not (member-equal x a)))
            (subsetp-equal a (remove1-equal x b)))))
(local
 (defun vop-pigeon-ind (a b)
   (if (atom a) b (vop-pigeon-ind (cdr a) (remove1-equal (car a) b)))))
(local
 (defthm vop-pigeonhole
   (implies (and (no-duplicatesp-equal a) (subsetp-equal a b))
            (<= (len a) (len b)))
   :rule-classes nil
   :hints (("Goal" :induct (vop-pigeon-ind a b)))))

; Each row contributes at most its two cells, and an unposted terminal cell
; is one cell fewer.
(local
 (defthm vop-pending-len-bound
   (<= (len (fn2-ops-pending-cells n p)) (* 2 (nfix n)))
   :rule-classes :linear))
(local
 (defthm vop-pending-len-strict
   (implies (and (natp slot) (natp n) (< slot n)
                 (not (equal (nth slot (nth 19 p)) 1)))
            (< (len (fn2-ops-pending-cells n p)) (* 2 n)))
   :rule-classes nil))

(local
 (defthm vop-post-count-bound
   (implies (and (fn2-ops-same-membersp (vop-pl pc ph fifo)
                                        (fn2-ops-pending-cells rows p))
                 (natp pc) (natp slot) (natp rows) (< slot rows)
                 (not (equal (nth slot (nth 19 p)) 1)))
            (< pc (* 2 rows)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance vop-pigeonhole (a (vop-pl pc ph fifo))
                             (b (fn2-ops-pending-cells rows p)))
                  (:instance vop-pending-len-strict (n rows)))
            :in-theory (e/d (fn2-ops-same-membersp)
                            (fn2-ops-pending-cells vop-pl))))))

(local
 (defthm vop-phase-slots-nonempty
   (implies (and (natp slot) (natp n) (< slot n)
                 (equal (nth slot (nth 1 p)) ph))
            (< 0 (len (fn2-ops-phase-slots n ph p))))
   :rule-classes nil))

(local
 (defthm vop-row-semantic-reserved-unposted
   (implies (and (fn2-ops-row-semanticp n p) (natp slot) (natp n) (< slot n)
                 (equal (nth slot (nth 1 p)) 1))
            (equal (nth slot (nth 19 p)) 0))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-ops-row-semanticp n p)
            :in-theory (e/d (fn2-ops-row-semanticp)
                            (fn2-action-completionp))))))

; A payload accepted as cell 0 names a completion-bearing action.
(local
 (defthm vop-payload-ack-phase
   (implies (fn2-post-payloadp 0 slot evkind outcome reason count aux0 aux1 p)
            (equal (fn2-op-ack-phase (nth slot (nth 2 p))) 3))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-post-payloadp fn2-op-ack-phase
                                    fn2-terminal-event)
                                   (fn2-event-statusp))))))

; The payload check reads three fields of its row and nothing else.
(local
 (defthm vop-payload-frame
   (implies (and (fn2-post-payloadp cell slot evkind outcome reason count
                                    aux0 aux1 p)
                 (equal (nth slot (nth 2 r)) (nth slot (nth 2 p)))
                 (equal (nth slot (nth 15 r)) (nth slot (nth 15 p)))
                 (equal (nth slot (nth 10 r)) (nth slot (nth 10 p))))
            (fn2-post-payloadp cell slot evkind outcome reason count
                               aux0 aux1 r))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-post-payloadp)
                                   (fn2-event-statusp fn2-terminal-event))))))

;; ---------------------------------------------------------------------------
;; fn2-ops-result-reservation: the reserved row through enqueue, ack and post

; Everything the three calls read, in raw fields, for a reserved SLOT.
(local
 (defun vop-res-rawp (slot p)
   (let ((rows (nth 44 p)) (cap (len (nth 45 p))) (pcap (len (nth 47 p))))
     (and (natp slot) (natp rows) (< slot rows) (< rows 4294967296)
          (equal (nth slot (nth 1 p)) 1)
          (equal (nth slot (nth 19 p)) 0)
          (natp (nth 48 p)) (natp (nth 49 p)) (natp (nth 50 p))
          (< (nth 48 p) cap) (< (nth 49 p) cap) (< (nth 50 p) cap)
          (< cap 4294967296)
          (equal (len (nth 46 p)) cap)
          (equal (vop-dist (nth 48 p) (nth 49 p) cap) (nth 50 p))
          (integerp (nth 51 p)) (< 0 (nth 51 p))
          (vop-refsp (vop-ob (nth 50 p) (nth 48 p) (nth 45 p) (nth 46 p))
                     (nth 0 p) (nth 1 p) rows)
          (equal pcap (* 2 rows))
          (natp (nth 52 p)) (natp (nth 53 p)) (natp (nth 54 p))
          (< (nth 52 p) pcap) (< (nth 53 p) pcap) (< (nth 54 p) pcap)
          (equal (vop-dist (nth 52 p) (nth 53 p) pcap) (nth 54 p))))))

(local
 (defthm vop-res-rawp-facts
   (implies (vop-res-rawp slot p)
            (and (natp slot) (natp (nth 44 p)) (< slot (nth 44 p))
                 (< (nth 44 p) 4294967296)
                 (equal (nth slot (nth 1 p)) 1)
                 (equal (nth slot (nth 19 p)) 0)
                 (natp (nth 48 p)) (natp (nth 49 p)) (natp (nth 50 p))
                 (< (nth 48 p) (len (nth 45 p)))
                 (< (nth 49 p) (len (nth 45 p)))
                 (< (nth 50 p) (len (nth 45 p)))
                 (< (len (nth 45 p)) 4294967296)
                 (equal (len (nth 46 p)) (len (nth 45 p)))
                 (integerp (nth 51 p)) (< 0 (nth 51 p))
                 (equal (len (nth 47 p)) (* 2 (nth 44 p)))
                 (natp (nth 52 p)) (natp (nth 53 p)) (natp (nth 54 p))
                 (< (nth 52 p) (* 2 (nth 44 p)))
                 (< (nth 53 p) (* 2 (nth 44 p)))
                 (< (nth 54 p) (* 2 (nth 44 p)))))
   :rule-classes :forward-chaining))

(local
 (defthm vop-sem-res-rawp
   (implies (and (fn2-ops-semanticp p) (natp slot) (< slot (nth 44 p))
                 (equal (nth slot (nth 1 p)) 1))
            (vop-res-rawp slot p))
   :hints (("Goal"
            :use (vop-sem-facts vop-wfp-rows
                  (:instance vop-ring-shape-facts
                             (c (len (nth 45 p))) (h (nth 48 p))
                             (tl (nth 49 p)) (n (nth 50 p)))
                  (:instance vop-ring-shape-facts
                             (c (* 2 (nth 44 p))) (h (nth 52 p))
                             (tl (nth 53 p)) (n (nth 54 p)))
                  (:instance vop-phase-slots-nonempty
                             (n (nth 44 p)) (ph 1))
                  (:instance vop-row-semantic-reserved-unposted
                             (n (nth 44 p)))
                  (:instance vop-post-count-bound
                             (pc (nth 54 p)) (ph (nth 52 p))
                             (fifo (nth 47 p)) (rows (nth 44 p))))
            :in-theory (disable vop-ob vop-pl vop-refsp fn2-ops-phase-slots
                                fn2-ops-pending-cells)))))

; The reserved row's own queued reference and FIFO cell are the next ring
; positions: one push each.
(local
 (defthm vop-res-ob-push
   (implies (vop-res-rawp slot p)
            (equal (vop-ob (+ 1 (nth 50 p)) (nth 48 p)
                           (update-nth (nth 49 p) s (nth 45 p))
                           (update-nth (nth 49 p) g (nth 46 p)))
                   (append (vop-ob (nth 50 p) (nth 48 p)
                                   (nth 45 p) (nth 46 p))
                           (list (list s g)))))
   :hints (("Goal"
            :use ((:instance vop-ob-push (left (nth 50 p)) (idx (nth 48 p))
                             (tl (nth 49 p))
                             (slots (nth 45 p)) (gens (nth 46 p))))
            :in-theory (disable vop-ob vop-refsp)))))
(local
 (defthm vop-res-pl-push
   (implies (vop-res-rawp slot p)
            (equal (vop-pl (+ 1 (nth 54 p)) (nth 52 p)
                           (update-nth (nth 53 p) v (nth 47 p)))
                   (append (vop-pl (nth 54 p) (nth 52 p) (nth 47 p))
                           (list v))))
   :hints (("Goal"
            :use ((:instance vop-pl-push (left (nth 54 p)) (idx (nth 52 p))
                             (tl (nth 53 p)) (fifo (nth 47 p))))
            :in-theory (disable vop-pl vop-ob vop-refsp)))))
(local
 (defthm vop-res-rawp-refs
   (implies (vop-res-rawp slot p)
            (vop-refsp (vop-ob (nth 50 p) (nth 48 p) (nth 45 p) (nth 46 p))
                       (nth 0 p) (nth 1 p) (nth 44 p)))))
(local (in-theory (disable vop-res-rawp)))

(local
 (defun vop-enq (slot p)
   (update-nth-array 1 slot 2
    (update-nth 51 (+ -1 (nth 51 p))
     (update-nth 50 (+ 1 (nth 50 p))
      (update-nth 49 (fn2-ring-next (nth 49 p) (len (nth 45 p)))
       (update-nth-array 46 (nth 49 p) (nth slot (nth 0 p))
        (update-nth-array 45 (nth 49 p) slot p))))))))

(local
 (defthm vop-enqueue-of-res
   (implies (and (vop-res-rawp slot p) (equal gen (nth slot (nth 0 p))))
            (equal (fn2-op-enqueue slot gen p)
                   (list :ok (vop-enq slot p))))
   :hints (("Goal" :in-theory (enable fn2-op-enqueue fn2-op-phase-code
                                      fn2-op-handle-code fn2-op-slotp)))))

(local
 (defthm vop-enq-reads
   (and (equal (nth 1 (vop-enq slot p)) (update-nth slot 2 (nth 1 p)))
        (equal (nth 45 (vop-enq slot p))
               (update-nth (nth 49 p) slot (nth 45 p)))
        (equal (nth 46 (vop-enq slot p))
               (update-nth (nth 49 p) (nth slot (nth 0 p)) (nth 46 p)))
        (equal (nth 50 (vop-enq slot p)) (+ 1 (nth 50 p)))
        (implies (and (natp k) (not (member k '(1 45 46 49 50 51))))
                 (equal (nth k (vop-enq slot p)) (nth k p))))))
(local (in-theory (disable vop-enq)))

(local
 (defthm vop-refsp-append
   (implies (true-listp a)
            (equal (vop-refsp (append a b) g ph r)
                   (and (vop-refsp a g ph r) (vop-refsp b g ph r))))))
(local
 (defthm vop-refsp-other-phase
   (implies (and (vop-refsp refs g ph r) (natp slot)
                 (not (equal (nth slot ph) 2)))
            (vop-refsp refs g (update-nth slot v ph) r))))
(local
 (defthm vop-ref-slots-append
   (equal (fn2-ops-ref-slots (append a b))
          (append (fn2-ops-ref-slots a) (fn2-ops-ref-slots b)))))
(local
 (defthm vop-member-append
   (iff (member-equal x (append a b))
        (or (member-equal x a) (member-equal x b)))))

(local
 (defthm vop-enq-ack-ready
   (implies (vop-res-rawp slot p)
            (and (vop-submit-okp (+ 1 (nth 50 p)) (vop-enq slot p))
                 (fn2-outbox-prefixp (+ 1 (nth 50 p)) (nth 48 p)
                                     (vop-enq slot p))))
   :hints (("Goal"
            :use ((:instance vop-refsp-slots-okp
                             (refs (vop-ob (+ 1 (nth 50 p)) (nth 48 p)
                                           (nth 45 (vop-enq slot p))
                                           (nth 46 (vop-enq slot p))))
                             (g (nth 0 p))
                             (ph (update-nth slot 2 (nth 1 p)))
                             (r (nth 44 p))))
            :in-theory (e/d (vop-submit-okp)
                            (vop-ob fn2-outbox-prefixp
                             vop-refsp-slots-okp))))))

(local
 (defthm vop-ack-of-enq
   (implies (vop-res-rawp slot p)
            (equal (fn2-outbox-ack (+ 1 (nth 50 p)) (vop-enq slot p))
                   (list :ok (fn2-outbox-submit-prefix
                              (+ 1 (nth 50 p)) (vop-enq slot p)))))
   :hints (("Goal" :in-theory (e/d (fn2-outbox-ack)
                                   (vop-ob vop-refsp fn2-outbox-prefixp))))))

; The acknowledged row is submitted with its terminal cell still unposted,
; and the payload it was reserved for is still its payload.
(local
 (defthm vop-reservation-acked
   (implies (and (vop-res-rawp slot p)
                 (fn2-post-payloadp 0 slot evkind outcome reason count
                                    aux0 aux1 p))
            (let ((r (fn2-outbox-submit-prefix (+ 1 (nth 50 p))
                                               (vop-enq slot p))))
              (and (equal (nth slot (nth 1 r)) 3)
                   (fn2-post-payloadp 0 slot evkind outcome reason count
                                      aux0 aux1 r))))
   :hints (("Goal"
            :use (vop-payload-ack-phase
                  (:instance vop-payload-frame (cell 0)
                             (r (fn2-outbox-submit-prefix
                                 (+ 1 (nth 50 p)) (vop-enq slot p)))))
            :in-theory (disable vop-ob vop-refsp)))))

(local
 (defthm vop-post0-accepted
   (implies (and (natp slot) (< slot (nth 44 r))
                 (equal gen (nth slot (nth 0 r)))
                 (equal (nth slot (nth 1 r)) 3)
                 (equal (nth slot (nth 19 r)) 0)
                 (fn2-post-payloadp 0 slot evkind outcome reason count
                                    aux0 aux1 r)
                 (< (nth 53 r) (len (nth 47 r)))
                 (< (nth 54 r) (len (nth 47 r)))
                 (< (len (nth 47 r)) 8589934592))
            (let ((s (fn2-post-result 0 slot gen evkind outcome reason count
                                      aux0 aux1 r)))
              (and (equal (nth 63 s) (nth 63 r))
                   (equal (nth 54 s) (+ 1 (nth 54 r)))
                   (equal (nth 52 s) (nth 52 r))
                   (equal (nth 47 s)
                          (update-nth (nth 53 r) (* 2 slot) (nth 47 r)))
                   (equal (nth slot (nth 19 s)) 1)
                   (equal (nth slot (nth 20 s)) 0)
                   (equal (nth slot (nth 21 s)) evkind)
                   (equal (nth slot (nth 22 s)) outcome)
                   (equal (nth slot (nth 23 s)) reason)
                   (equal (nth slot (nth 24 s)) count)
                   (equal (nth slot (nth 25 s)) aux0)
                   (equal (nth slot (nth 26 s)) aux1))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-post-result fn2-post-eligiblep
                                      fn2-op-handle-code fn2-op-slotp)))))

(local
 (defthm vop-reservation-core
   (implies (and (vop-res-rawp slot p)
                 (equal gen (nth slot (nth 0 p)))
                 (fn2-post-payloadp 0 slot evkind outcome reason count
                                    aux0 aux1 p))
            (let ((s (fn2-post-result
                      0 slot gen evkind outcome reason count aux0 aux1
                      (fn2-outbox-submit-prefix (+ 1 (nth 50 p))
                                                (vop-enq slot p)))))
              (and (equal (nth 63 s) (nth 63 p))
                   (equal (vop-pl (nth 54 s) (nth 52 s) (nth 47 s))
                          (append (vop-pl (nth 54 p) (nth 52 p) (nth 47 p))
                                  (list (* 2 slot))))
                   (equal (nth slot (nth 19 s)) 1)
                   (equal (nth slot (nth 20 s)) 0)
                   (equal (nth slot (nth 21 s)) evkind)
                   (equal (nth slot (nth 22 s)) outcome)
                   (equal (nth slot (nth 23 s)) reason)
                   (equal (nth slot (nth 24 s)) count)
                   (equal (nth slot (nth 25 s)) aux0)
                   (equal (nth slot (nth 26 s)) aux1))))
   :hints (("Goal"
            :use (vop-reservation-acked
                  (:instance vop-post0-accepted
                             (r (fn2-outbox-submit-prefix
                                 (+ 1 (nth 50 p)) (vop-enq slot p)))))
            :in-theory (disable vop-ob vop-pl vop-refsp
                                vop-reservation-acked)))))

(defthm fn2-ops-result-reservation-proved
  (fn2-ops-result-reservation$owed
   slot gen evkind outcome reason count aux0 aux1 p)
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn2-ops-result-reservation$owed
                            fn2-ops-reservation-hyps
                            fn2-ops-reservation-conclusion
                            fn2-ops-reservation-resultp
                            fn2-op-slotp fn2-outbox-queued
                            fn2-ops-posted-list fn2-ops-cell-snapshot
                            fn2-op-cell)
                           (vop-ob vop-pl vop-refsp)))))
(fn2-owed-discharge fn2-ops-result-reservation
                    fn2-ops-result-reservation-proved)
