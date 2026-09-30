; Exact block boundary for the actual captured digest collector/formatter.
; Proof-only: no denotation or list operations are served. PRF-1148 full
; trajectory/parser/authority target remains planned.
(in-package "ACL2")
(include-book "post-identity-captured")
(include-book "pagestore-digest-block-predicate")

; Retain the exported dependency theory for the actual entry proof below.
(local (deftheory fn-pic-prefix-entry-theory (current-theory :here)))

(local (include-book "arithmetic-5/top" :dir :system))
(local
 (defun fn-pic-nth-prefix-ind (i n xs)
   (declare (xargs :measure (nfix i)))
   (if (zp (nfix i)) (list n xs)
     (fn-pic-nth-prefix-ind (- (nfix i) 1) (- (nfix n) 1) (cdr xs)))))
(local
 (defthm fn-pic-prefix-nthcdrx-true-listp
   (implies (true-listp xs) (true-listp (fn-b3-nthcdrx n xs)))
   :hints (("Goal" :induct (fn-b3-nthcdrx n xs) :in-theory (enable fn-b3-nthcdrx)))))
(local
 (defthm fn-pic-prefix-nthx-of-firstn
   (implies (and (natp i) (natp n) (< i n))
     (equal (fn-b3-nthx i (fn-b3-firstn n xs)) (fn-b3-nthx i xs)))
   :hints (("Goal" :induct (fn-pic-nth-prefix-ind i n xs)
                   :expand ((fn-b3-firstn n xs))
                   :in-theory (enable fn-b3-nthx fn-b3-firstn nfix)))))
(local
 (defthm fn-pic-prefix-nthcdrx-of-firstn
   (implies (and (natp m) (natp n) (<= m n))
     (equal (fn-b3-nthcdrx m (fn-b3-firstn n xs))
            (fn-b3-firstn (- n m) (fn-b3-nthcdrx m xs))))
   :hints (("Goal" :induct (fn-pic-nth-prefix-ind m n xs)
                   :expand ((fn-b3-firstn n xs))
                   :in-theory (enable fn-b3-nthcdrx fn-b3-firstn nfix)))))
(local
 (defun fn-pic-prefix-words-ind (k n xs)
   (declare (xargs :measure (nfix k)))
   (if (zp (nfix k)) (list n xs)
     (fn-pic-prefix-words-ind (- (nfix k) 1) (- (nfix n) 4)
                             (fn-b3-nthcdrx 4 xs)))))
(local
 (defthm fn-pic-prefix-words-of-firstn
   (implies (and (natp k) (natp n) (<= (* 4 k) n))
     (equal (fn-b3-words k (fn-b3-firstn n xs)) (fn-b3-words k xs)))
   :hints (("Goal" :induct (fn-pic-prefix-words-ind k n xs)
                   :in-theory (e/d (fn-b3-words)
                                    (fn-b3-nthx fn-b3-nthcdrx fn-b3-firstn fn-b3-le-word))))))
(local
 (defthm fn-pic-prefix-take-is-firstn
   (implies (and (natp n) (<= n (len xs)))
     (equal (take n xs) (fn-b3-firstn n xs)))
   :hints (("Goal" :induct (take n xs)
                   :expand ((fn-b3-firstn n xs))
                   :in-theory (enable take fn-b3-firstn nfix)))))
(local
 (defthm fn-pic-prefix-nthcdr-is-nthcdrx
   (implies (true-listp xs)
     (equal (nthcdr n xs) (fn-b3-nthcdrx n xs)))
   :hints (("Goal" :induct (nthcdr n xs)
                   :in-theory (enable nthcdr fn-b3-nthcdrx nfix)))))
(local
 (defthm fn-pic-prefix-firstn-firstn
   (implies (and (natp n) (natp m))
     (equal (fn-b3-firstn n (fn-b3-firstn m xs))
            (fn-b3-firstn (min n m) xs)))
   :hints (("Goal" :induct (fn-pic-nth-prefix-ind n m xs)
                   :expand ((fn-b3-firstn m xs) (fn-b3-firstn n xs))
                   :in-theory (enable fn-b3-firstn nfix min)))))
(local
 (defthm fn-pic-prefix-firstn-limited-by-len
   (implies (natp n)
     (equal (fn-b3-firstn n xs) (fn-b3-firstn (min n (len xs)) xs)))
   :hints (("Goal" :induct (fn-b3-firstn n xs)
                   :expand ((fn-b3-firstn n xs))
                   :in-theory (enable fn-b3-firstn nfix min)))))
(local
 (defthm fn-pic-prefix-firstn-true-listp
   (true-listp (fn-b3-firstn n xs))
   :hints (("Goal" :induct (fn-b3-firstn n xs) :in-theory (enable fn-b3-firstn)))))
(local
 (defthm fn-pic-prefix-min-demand
   (implies (and (natp start) (natp end) (<= start end) (natp total))
     (equal (min 64 (nfix (- (min total (* 8 end)) (* 8 start))))
            (min (min 64 (* 8 (- end start))) (nfix (- total (* 8 start))))))
   :hints (("Goal" :in-theory (enable min nfix)))))
(local (defthm fn-pic-prefix-nfix-nat (implies (natp x) (equal (nfix x) x)) :hints (("Goal" :in-theory (enable nfix)))))
(local (defthm fn-pic-prefix-min-nat (implies (and (natp x) (natp y)) (natp (min x y))) :hints (("Goal" :in-theory (enable min))) :rule-classes (:rewrite :type-prescription)))
(local (defthm fn-pic-prefix-min-bounds (and (<= (min x y) x) (<= (min x y) y)) :hints (("Goal" :in-theory (enable min))) :rule-classes (:rewrite :linear)))
(local
 (defthm fn-pic-prefix-len-of-nthcdr
   (implies (natp n) (equal (len (nthcdr n xs)) (nfix (- (len xs) n))))
   :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr nfix)))))
(local
 (defthm fn-pic-prefix-firstn-of-nthcdr
   (equal (fn-b3-firstn n (nthcdr m xs))
          (fn-b3-firstn n (fn-b3-nthcdrx m xs)))
   :hints (("Goal" :induct (nthcdr m xs)
                  :in-theory (enable nthcdr fn-b3-nthcdrx fn-b3-firstn nfix)))))
(local
 (defthm fn-pic-prefix-complete-byte-block
   (implies (and (natp start) (natp end) (<= start end))
     (equal
       (take (min 64 (nfix (- (min (len msg) (* 8 end)) (* 8 start))))
             (nthcdr (* 8 start) msg))
       (fn-b3-firstn 64 (pgs-dcr-span start end msg))))
   :hints (("Goal" :in-theory (e/d (pgs-dcr-span)
                  (fn-b3-firstn fn-b3-nthcdrx take nthcdr min nfix
                   fn-pic-prefix-firstn-limited-by-len))
            :use ((:instance fn-pic-prefix-min-demand (total (len msg)))
                  (:instance fn-pic-prefix-take-is-firstn
                    (n (min 64 (nfix (- (min (len msg) (* 8 end)) (* 8 start)))))
                    (xs (nthcdr (* 8 start) msg)))
                  (:instance fn-pic-prefix-firstn-limited-by-len
                    (n (min 64 (* 8 (- end start))))
                    (xs (fn-b3-nthcdrx (* 8 start) msg))))))))
(local
 (defthm fn-pic-prefix-span-true-listp
   (true-listp (pgs-dcr-span start end msg))
   :hints (("Goal" :in-theory (e/d (pgs-dcr-span) (fn-b3-firstn))))))
(local
 (defthm fn-pic-prefix-complete-word-block
   (implies (and (natp start) (natp end) (<= start end))
     (equal
       (fn-b3-words 16
         (take (min 64 (nfix (- (min (len msg) (* 8 end)) (* 8 start))))
               (nthcdr (* 8 start) msg)))
       (fn-b3-words 16 (pgs-dcr-span start end msg))))
   :hints (("Goal" :in-theory (disable fn-b3-words pgs-dcr-span fn-b3-firstn
                                      take nthcdr fn-b3-nthcdrx min nfix
                                      fn-pic-prefix-firstn-limited-by-len
                                      fn-pic-prefix-words-of-firstn)
            :use ((:instance fn-pic-prefix-complete-byte-block)
                  (:instance fn-pic-prefix-words-of-firstn
                    (k 16) (n 64) (xs (pgs-dcr-span start end msg)))
                  (:instance fn-pic-prefix-firstn-true-listp
                    (n (* 8 (- end start)))
                    (xs (fn-b3-nthcdrx (* 8 start) msg))))))))

; The actual completed collector supplies the exact sixteen words of the
; existing cursor's requested immutable virtual span, including short-final
; zero padding. No host decoder or whole virtual-source allocation is served.
(local
 (defthm fn-pic-completed-collector-satisfies-digest-block-ordered
  (let ((msg (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))
    (implies
      (and (fn-pic-block-prefixp c incoming)
           (equal (fn-pic-get pos c) (fn-pic-get block-count c))
           (natp (pgs-dc-pos pgs-digest-state))
           (natp (pgs-dc-end pgs-digest-state))
           (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
           (equal (fn-pic-get block-start c)
                  (pgs-dcb-next-byte-offset pgs-digest-state))
           (equal (fn-pic-get block-count c)
                  (pgs-dcb-read-demand (len msg) pgs-digest-state)))
      (pgs-dcs-blockp (fn-pic-digest-block c) msg pgs-digest-state)))
  :rule-classes nil
  :hints (("Goal"
    :use (fn-pic-digest-block-is-denoted-block
          (:instance fn-pic-prefix-complete-word-block
            (msg (fn-pic-span-value (fn-pic-get digest-desc c) incoming))
            (start (pgs-dc-pos pgs-digest-state)) (end (pgs-dc-end pgs-digest-state))))
    :in-theory (e/d (pgs-dcs-blockp pgs-dcb-read-demand pgs-dcb-next-byte-offset)
      (fn-pic-digest-block fn-pic-block-prefixp fn-pic-at fn-pic-span-value
       fn-pic-spanp fn-pic-span-length take nthcdr fn-b3-words pgs-dcr-span
       min nfix fn-pic-prefix-firstn-limited-by-len)))))
)
(defthm fn-pic-completed-collector-satisfies-digest-block
  (let ((msg (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))
    (implies
      (and (fn-pic-block-prefixp c incoming)
           (equal (fn-pic-get pos c) (fn-pic-get block-count c))
           (natp (pgs-dc-pos pgs-digest-state))
           (natp (pgs-dc-end pgs-digest-state))
           (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset pgs-digest-state))
           (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) pgs-digest-state)))
      (pgs-dcs-blockp (fn-pic-digest-block c) msg pgs-digest-state)))
  :rule-classes nil
  :hints (("Goal"
    :cases ((<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state)))
    :use (fn-pic-completed-collector-satisfies-digest-block-ordered)
    :in-theory (e/d (pgs-dcs-blockp pgs-dcb-read-demand pgs-dcb-next-byte-offset
                    pgs-dcr-span fn-pic-digest-block fn-pic-block-prefixp fn-pic-reverse-block
                    fn-b3-firstn fn-b3-words min nfix take revappend)
      (fn-pic-at fn-pic-span-value fn-pic-spanp fn-pic-span-length nthcdr
       fn-b3-le-word fn-b3-nthx fn-b3-nthcdrx
       fn-pic-prefix-firstn-limited-by-len)))))

; Actual readonly incoming-byte entry preserves the collector denotation.
(local (in-theory (theory 'fn-pic-prefix-entry-theory)))
(local
 (defthm fn-pic-trajectory-at-is-nth
   (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
   :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local
 (defthm fn-pic-block-prefixp-of-irrelevant-update
   (implies (and (natp field) (not (equal field 17)) (not (equal field 20))
                 (not (equal field 21)) (not (equal field 22)) (not (equal field 13)))
     (equal (fn-pic-block-prefixp (update-nth field value c) incoming)
            (fn-pic-block-prefixp c incoming)))
   :hints (("Goal" :in-theory (e/d (fn-pic-block-prefixp)
                    (fn-pic-at fn-pic-spanp fn-pic-span-length fn-pic-span-value
                     take nthcdr revappend update-nth nth))))))
(defthm fn-pic-next-preserves-exact-collector-prefix
  (implies (and (fn-pic-block-prefixp c fn-octets)
                (equal (fn-pic-get phase c) :digest-read))
    (fn-pic-block-prefixp (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets))
  :hints (("Goal"
     :use ((:instance fn-pic-block-add-preserves-prefix
              (incoming fn-octets)
              (byte (fn-octets-get
                      (fn-pic-span-offset (fn-pic-get digest-desc c)
                        (+ (fn-pic-get block-start c) (fn-pic-get pos c))) fn-octets)))
           (:instance fn-pic-span-byte-is-denoted-byte
              (d (fn-pic-get digest-desc c))
              (i (+ (fn-pic-get block-start c) (fn-pic-get pos c))) (xs fn-octets)))
     :in-theory (e/d (fn-pic-next fn-pic-feed-funded fn-pic-demand fn-pic-feed
                     fn-pic-finish fn-pic-observation-okp fn-pic-observed-byte
                     fn-octets-get fn-octets-len fn-pic-block-prefixp)
        (fn-pic-at fn-pic-spanp fn-pic-span-length fn-pic-span-value fn-pic-span-offset
         fn-pic-block-add nth nthcdr take update-nth revappend)))))

; Actual mutating digest entry establishes the requested collector before reads.
(local (defthm fn-pic-demand-take-zero (equal (take 0 x) nil) :hints (("Goal" :in-theory (enable take)))))
(local (defthm fn-pic-demand-at-is-nth
  (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
  :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-demand-len-take
  (implies (natp n) (equal (len (take n x)) n))))
(local (defthm fn-pic-demand-len-tail
  (implies (natp n) (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr len nfix)))))
(local (defthm fn-pic-demand-len-append
  (equal (len (append x y)) (+ (len x) (len y)))
  :hints (("Goal" :induct (append x y) :in-theory (enable binary-append len)))))
(local (defthm fn-pic-demand-span-length
  (implies (fn-pic-spanp d (len incoming))
    (equal (len (fn-pic-span-value d incoming)) (fn-pic-span-length d (len incoming))))
  :hints (("Goal" :in-theory (e/d (fn-pic-spanp fn-pic-span-value fn-pic-span-length)
                                   (take nthcdr fn-pic-at nth binary-append))))))
(defthm fn-pic-digest-next-establishes-requested-prefix
  (implies
    (and (equal (fn-pic-get phase c) :digest-next)
         (fn-pic-spanp (fn-pic-get digest-desc c) (len incoming))
         (equal (fn-pic-get incoming-n c) (len incoming)))
    (let ((next (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state))))
      (implies (equal (fn-pic-get phase next) :digest-read)
        (and (fn-pic-block-prefixp next incoming)
             (equal (fn-pic-get block-start next) (pgs-dcb-next-byte-offset pgs-digest-state))
             (equal (fn-pic-get block-count next)
                    (pgs-dcb-read-demand (len (fn-pic-span-value (fn-pic-get digest-desc c) incoming)) pgs-digest-state))
             (equal (mv-nth 3 (fn-pic-digest-next c fuel pgs-digest-state)) pgs-digest-state)))))
  :hints (("Goal" :in-theory
    (e/d (fn-pic-digest-next fn-pic-digest-effect fn-pic-feed-funded fn-pic-feed
          fn-pic-demand fn-pic-observation-okp fn-pic-block-prefixp
          fn-pic-digest-scalar-guardp pgs-dcb-read-demand pgs-dcb-next-byte-offset)
         (fn-pic-at fn-pic-spanp fn-pic-span-value fn-pic-span-length
          nth update-nth take nthcdr revappend pgs-dcb-step pgs-dcb-result-octets
          pgs-dc-pos pgs-dc-end pgs-dc-start pgs-dc-total pgs-dc-mode pgs-dc-capture pgs-dc-lease pgs-dc-needs-block pgs-dcb-begin pgs-dcb-word-count)))))
