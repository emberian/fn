; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-pointer-writer-frames")

(local (defthm fn-lbsc-len-in-bounds-update
 (implies (and (natp i) (< i (len rows))) (equal (len (update-nth i value rows)) (len rows)))
 :hints (("Goal" :induct (update-nth i value rows) :in-theory (enable update-nth len)))))

(local (defthm fn-lbsc-count-of-update-slot-store
 (equal (fn-lbc-count (update-fn-lbc-slot-store value fn-lbc)) (fn-lbc-count fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-count fn-lbc-row-store update-fn-lbc-slot-store fn-dm-nth-update-nth))))))

(local (defthm fn-lbsc-count-of-update-slot-escape-keys
 (equal (fn-lbc-count (update-fn-lbc-slot-escape-keys value fn-lbc)) (fn-lbc-count fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-count fn-lbc-row-store update-fn-lbc-slot-escape-keys fn-dm-nth-update-nth))))))

(local (defthm fn-lbsc-count-of-row-set-flags
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-count (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags i flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-count fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store fn-dm-nth-update-nth
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-lbsc-len-in-bounds-update))))))

(defthm fn-lbc-count-of-slot-put
 (equal (fn-lbc-count (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-count fn-lbc))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-count-of-slot-drop-owner (keys (fn-lbc-slot-escape-keys fn-lbc)))) :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '((:type-prescription fn-lbc-slot-drop-owner) fn-lbc-slot-put fn-lbsc-count-of-update-slot-store fn-lbsc-count-of-update-slot-escape-keys
     fn-lbsc-count-of-row-set-flags fn-lbc-count-of-slot-drop-owner fn-lbc-count-of-escape-store-put nfix))
   '((tau-system))))))

(defthm fn-lbc-count-of-slot-insert
 (equal (fn-lbc-count (fn-lbc-slot-insert i slot fuel fn-lbc)) (fn-lbc-count fn-lbc))
 :hints (("Goal" :induct (fn-lbc-slot-insert i slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-slot-insert fn-lbc-count-of-slot-put)))))

(defthm fn-lbc-count-of-index-slots
 (equal (fn-lbc-count (fn-lbc-index-slots i n fn-lbc)) (fn-lbc-count fn-lbc))
 :hints (("Goal" :induct (fn-lbc-index-slots i n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-index-slots fn-lbc-count-of-slot-insert)))))
