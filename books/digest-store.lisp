; One scalar-word write boundary for native and logical BLAKE3 results.
(in-package "ACL2")
(include-book "digests")
(local (include-book "std/lists/update-nth" :dir :system))
(fn2-book-layer :b)

(defun fn2-digest-store-words (dst w0 w1 w2 w3 w4 w5 w6 w7 fn2-digests)
 (declare (xargs :stobjs fn2-digests
  :guard (and (fn2-digest-rowp dst fn2-digests)
              (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1)
              (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3)
              (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5)
              (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))))
 (fn2-digests-put dst (w0 w0) (w1 w1) (w2 w2) (w3 w3)
                      (w4 w4) (w5 w5) (w6 w6) (w7 w7)))

(defthm fn2-digest-store-words-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digest-rowp dst fn2-digests)
               (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1)
               (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3)
               (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5)
               (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  (and (fn2-digestsp (fn2-digest-store-words dst w0 w1 w2 w3 w4 w5 w6 w7 fn2-digests))
       (fn2-digests-wfp (fn2-digest-store-words dst w0 w1 w2 w3 w4 w5 w6 w7 fn2-digests))
       (equal (fn2-digests-rows (fn2-digest-store-words dst w0 w1 w2 w3 w4 w5 w6 w7 fn2-digests))
              (fn2-digests-rows fn2-digests))))
 :hints (("Goal" :in-theory (enable fn2-digest-store-words fn2-digest-rowp))))

; One indexed statement covers every word, every other row, all metadata,
; and any additional logical outer field. No representation is revalidated.
(defthm fn2-digest-store-words-effect
 (equal (nth field (fn2-digest-store-words dst w0 w1 w2 w3 w4 w5 w6 w7 fn2-digests))
        (if (< (nfix field) 8)
            (update-nth dst (nth field (list w0 w1 w2 w3 w4 w5 w6 w7))
                        (nth field fn2-digests))
          (nth field fn2-digests)))
 :hints (("Goal" :in-theory (enable fn2-digest-store-words)
          :cases ((equal (nfix field) 0) (equal (nfix field) 1)
                  (equal (nfix field) 2) (equal (nfix field) 3)
                  (equal (nfix field) 4) (equal (nfix field) 5)
                  (equal (nfix field) 6) (equal (nfix field) 7)))))

(defthm fn2-digest-store-words-observation
 (equal (nth i (nth field (fn2-digest-store-words dst w0 w1 w2 w3 w4 w5 w6 w7 fn2-digests)))
        (if (and (< (nfix field) 8) (equal (nfix i) (nfix dst)))
            (nth field (list w0 w1 w2 w3 w4 w5 w6 w7))
          (nth i (nth field fn2-digests))))
 :hints (("Goal" :in-theory (e/d (nth-update-nth)
                                (fn2-digest-store-words nth update-nth nfix)))))

(defthm fn2-digest-store-words-snapshot
 (equal (fn2-digests-row-snapshot dst
          (fn2-digest-store-words dst w0 w1 w2 w3 w4 w5 w6 w7 fn2-digests))
        (list w0 w1 w2 w3 w4 w5 w6 w7))
 :hints (("Goal" :in-theory (enable fn2-digests-row-snapshot
                 fn2-digests-w0 fn2-digests-w1 fn2-digests-w2 fn2-digests-w3
                 fn2-digests-w4 fn2-digests-w5 fn2-digests-w6 fn2-digests-w7))))

(defthm fn2-digest-store-words-overwrite
 (equal (fn2-digest-store-words dst a0 a1 a2 a3 a4 a5 a6 a7
          (fn2-digest-store-words dst b0 b1 b2 b3 b4 b5 b6 b7 fn2-digests))
        (fn2-digest-store-words dst a0 a1 a2 a3 a4 a5 a6 a7 fn2-digests))
 :hints (("Goal" :in-theory (e/d (fn2-digest-store-words
                 fn2-digests-set-w0 fn2-digests-set-w1 fn2-digests-set-w2 fn2-digests-set-w3
                 fn2-digests-set-w4 fn2-digests-set-w5 fn2-digests-set-w6 fn2-digests-set-w7
                 update-fn2-digests-w0$ai update-fn2-digests-w1$ai
                 update-fn2-digests-w2$ai update-fn2-digests-w3$ai
                 update-fn2-digests-w4$ai update-fn2-digests-w5$ai
                 update-fn2-digests-w6$ai update-fn2-digests-w7$ai)
                (nth update-nth)))))

(in-theory (disable fn2-digest-store-words))
