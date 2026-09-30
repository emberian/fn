; Current FNADTSN2 header, emitted one word at a time from census scalars.
(in-package "ACL2")
(include-book "history-image-census")
(include-book "history-pages-placed")
(include-book "history-page-buffer")

(defun fn-hch-word (i count pool column-cap pool-cap)
  (declare (xargs :guard (and (natp i) (< i 2048)
                              (unsigned-byte-p 61 count) (unsigned-byte-p 64 pool)
                              (unsigned-byte-p 51 column-cap)
                              (unsigned-byte-p 51 pool-cap))))
  (cond ((equal i 0) *fn-hp-magic-word*)
        ((equal i 1) *adt-version*)
        ((equal i 2) (nth 0 *fn-hp-schema-words*))
        ((equal i 3) (nth 1 *fn-hp-schema-words*))
        ((equal i 4) (nth 2 *fn-hp-schema-words*))
        ((equal i 5) (nth 3 *fn-hp-schema-words*))
        ((equal i 6) count)
        ((equal i 7) 5)
        ((equal i 8) 1)
        ((equal i 9) (* 8 count))
        ((equal i 10) (+ 1 column-cap))
        ((equal i 11) (* 8 count))
        ((equal i 12) (+ 1 (* 2 column-cap)))
        ((equal i 13) (* 8 count))
        ((equal i 14) (+ 1 (* 3 column-cap)))
        ((equal i 15) (* 8 count))
        ((equal i 16) (+ 1 (* 4 column-cap)))
        ((equal i 17) pool)
        ((equal i 18) (fn-hcc-pages column-cap pool-cap))
        (t 0)))

(local
 (defun fn-hch-zero-ind (i n)
   (if (zp i) n (fn-hch-zero-ind (1- i) (1- n)))))
(local
 (defthm fn-hch-nth-zero
   (implies (and (natp i) (natp n) (< i n))
            (equal (nth i (adt-zeros n)) 0))
   :hints (("Goal" :induct (fn-hch-zero-ind i n)
            :in-theory (enable nth adt-zeros)))))

(local
 (defthm fn-hch-nth-cons
   (equal (nth i (cons a b)) (if (zp i) a (nth (1- i) b)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-hch-word-refines-current-header
  (implies (and (natp i) (< i 2048))
           (equal (fn-hch-word i count pool column-cap pool-cap)
                  (nth i (fn-hp-hdr2 count (fn-hcc-lens count pool)
                                    (fn-hcc-starts column-cap)
                                    (fn-hcc-pages column-cap pool-cap)))))
  :hints (("Goal" :in-theory (e/d (fn-hp-hdr2 fn-hcc-lens fn-hcc-starts
                                   fn-hp-meta-words)
                                  (nth adt-zeros (:executable-counterpart adt-zeros) fn-hcc-pages)))))

(in-theory (disable fn-hch-word))

(defthm fn-hch-word-is-u64
  (implies (and (unsigned-byte-p 61 count) (unsigned-byte-p 64 pool)
                (unsigned-byte-p 51 column-cap) (unsigned-byte-p 51 pool-cap))
           (unsigned-byte-p 64 (fn-hch-word i count pool column-cap pool-cap)))
  :hints (("Goal" :in-theory (enable fn-hch-word fn-hcc-pages))))


(defun fn-hch-tick (count pool column-cap pool-cap fn-hpb)
  (declare (xargs :stobjs fn-hpb
                  :guard-hints (("Goal" :in-theory (disable fn-hch-word-refines-current-header)))
                  :guard (and (unsigned-byte-p 61 count) (unsigned-byte-p 64 pool)
                              (unsigned-byte-p 51 column-cap)
                              (unsigned-byte-p 51 pool-cap))))
  (if (<= 2048 (fn-hpb-used fn-hpb))
      (mv :done fn-hpb)
    (fn-hpb-put (fn-hch-word (fn-hpb-used fn-hpb) count pool column-cap pool-cap)
                fn-hpb)))

(defthm fn-hch-tick-refines-current-header-effect
  (implies (and (natp (fn-hpb-used fn-hpb)) (< (fn-hpb-used fn-hpb) 2048))
           (and (equal (mv-nth 0 (fn-hch-tick count pool column-cap pool-cap fn-hpb))
                       :stored)
                (equal (fn-hpb-prefix
                        (mv-nth 1 (fn-hch-tick count pool column-cap pool-cap fn-hpb)))
                       (append (fn-hpb-prefix fn-hpb)
                               (list (nth (fn-hpb-used fn-hpb)
                                          (fn-hp-hdr2 count (fn-hcc-lens count pool)
                                                      (fn-hcc-starts column-cap)
                                                      (fn-hcc-pages column-cap pool-cap))))))))
  :hints (("Goal" :in-theory (disable fn-hch-word fn-hp-hdr2 fn-hpb-used))))

(defthm fn-hch-tick-keeps-identities
  (and (equal (fn-hpb-epoch (mv-nth 1 (fn-hch-tick count pool column-cap pool-cap fn-hpb)))
              (fn-hpb-epoch fn-hpb))
       (equal (fn-hpb-lease (mv-nth 1 (fn-hch-tick count pool column-cap pool-cap fn-hpb)))
              (fn-hpb-lease fn-hpb)))
  :hints (("Goal" :in-theory (disable fn-hpb-epoch fn-hpb-lease fn-hpb-used))))

(defthm fn-hch-tick-keeps-concrete
  (implies (and (fn-hpbp fn-hpb)
                (unsigned-byte-p 61 count) (unsigned-byte-p 64 pool)
                (unsigned-byte-p 51 column-cap) (unsigned-byte-p 51 pool-cap))
           (fn-hpbp (mv-nth 1 (fn-hch-tick count pool column-cap pool-cap fn-hpb))))
  :hints (("Goal" :in-theory (disable fn-hpbp fn-hpb-used fn-hch-word-refines-current-header))))

(in-theory (disable fn-hch-tick))
