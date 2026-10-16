; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-bit-properties")

(local (defthm fn-lbsfs-nfix-natural
 (implies (natp x) (equal (nfix x) x)) :hints (("Goal" :in-theory (enable nfix)))))

(local (defthm fn-lbsfs-len-in-bounds-update
 (implies (and (natp j) (< j (len rows))) (equal (len (update-nth j value rows)) (len rows)))
 :hints (("Goal" :induct (update-nth j value rows) :in-theory (enable update-nth len)))))

(defthm fn-lbc-bit-0-of-in-bounds-slot-flag-set
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc))
               (unsigned-byte-p 64 (fn-lbc-word :flags j fn-lbc)))
  (equal (fn-lbc-flag i 0 (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j
            (logior (fn-lbc-rowwords-get-flags j (fn-lbc-row-store fn-lbc)) 8)
            (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-flag i 0 fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-flag fn-lbc-word-flags-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags fn-lbc-rowwords-get-flags fn-lbc-rowwords$a-get-flags adt-set-a fn-dm-nth-update-nth fn-lbsfs-len-in-bounds-update fn-lbsfs-nfix-natural fn-lbc-flag-word-or-eight-preserves-bit-0))
   '((:definition nfix) (:definition logbitp) (:definition binary-logior) (tau-system))))))

(defthm fn-lbc-bit-1-of-in-bounds-slot-flag-set
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc))
               (unsigned-byte-p 64 (fn-lbc-word :flags j fn-lbc)))
  (equal (fn-lbc-flag i 1 (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j
            (logior (fn-lbc-rowwords-get-flags j (fn-lbc-row-store fn-lbc)) 8)
            (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-flag i 1 fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-flag fn-lbc-word-flags-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags fn-lbc-rowwords-get-flags fn-lbc-rowwords$a-get-flags adt-set-a fn-dm-nth-update-nth fn-lbsfs-len-in-bounds-update fn-lbsfs-nfix-natural fn-lbc-flag-word-or-eight-preserves-bit-1))
   '((:definition nfix) (:definition logbitp) (:definition binary-logior) (tau-system))))))

(defthm fn-lbc-bit-2-of-in-bounds-slot-flag-set
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc))
               (unsigned-byte-p 64 (fn-lbc-word :flags j fn-lbc)))
  (equal (fn-lbc-flag i 2 (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j
            (logior (fn-lbc-rowwords-get-flags j (fn-lbc-row-store fn-lbc)) 8)
            (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-flag i 2 fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-flag fn-lbc-word-flags-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags fn-lbc-rowwords-get-flags fn-lbc-rowwords$a-get-flags adt-set-a fn-dm-nth-update-nth fn-lbsfs-len-in-bounds-update fn-lbsfs-nfix-natural fn-lbc-flag-word-or-eight-preserves-bit-2))
   '((:definition nfix) (:definition logbitp) (:definition binary-logior) (tau-system))))))

(defthm fn-lbc-bit-4-of-in-bounds-slot-flag-set
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc))
               (unsigned-byte-p 64 (fn-lbc-word :flags j fn-lbc)))
  (equal (fn-lbc-flag i 4 (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j
            (logior (fn-lbc-rowwords-get-flags j (fn-lbc-row-store fn-lbc)) 8)
            (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-flag i 4 fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-flag fn-lbc-word-flags-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags fn-lbc-rowwords-get-flags fn-lbc-rowwords$a-get-flags adt-set-a fn-dm-nth-update-nth fn-lbsfs-len-in-bounds-update fn-lbsfs-nfix-natural fn-lbc-flag-word-or-eight-preserves-bit-4))
   '((:definition nfix) (:definition logbitp) (:definition binary-logior) (tau-system))))))

(defthm fn-lbc-bit-5-of-in-bounds-slot-flag-set
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc))
               (unsigned-byte-p 64 (fn-lbc-word :flags j fn-lbc)))
  (equal (fn-lbc-flag i 5 (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j
            (logior (fn-lbc-rowwords-get-flags j (fn-lbc-row-store fn-lbc)) 8)
            (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-flag i 5 fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-flag fn-lbc-word-flags-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags fn-lbc-rowwords-get-flags fn-lbc-rowwords$a-get-flags adt-set-a fn-dm-nth-update-nth fn-lbsfs-len-in-bounds-update fn-lbsfs-nfix-natural fn-lbc-flag-word-or-eight-preserves-bit-5))
   '((:definition nfix) (:definition logbitp) (:definition binary-logior) (tau-system))))))
