; Native test observation of the actual generic catalog, with an unbounded logical refinement.
(in-package "ACL2")
(include-book "../../books/lb-log-open-properties")
(include-book "../../books/def-loop")
(def-loop fn-lbw-unbound-catalog-rows (i fn-arena fn-cat log)
 :shape :step :over i :done (not (and (natp i) (< i (fn-cat-count fn-cat))))
 :skip (equal (fn-nntp-payload-bytes (fn-record-payload (fn-cat-at i fn-cat)) fn-arena)
              (fn-lb-log-payload (fn-cat-at i fn-cat) log))
 :body i :next (+ 1 i) :skip-next (+ 1 i)
 :measure (nfix (- (fn-cat-count fn-cat) (nfix i)))
 :stobjs (fn-arena fn-cat)
 :guard (and (natp i) (fn-cat-p fn-cat) (fn-lb-log-entries-guardp log))
 :guard-hints (("Goal" :in-theory (disable fn-cat-p fn-cat-count fn-cat-at
                   fn-lb-log-entries-guardp fn-lb-log-payload fn-nntp-payload-bytes))))

(local (defthm fn-lbw-less-shift
 (implies (and (rationalp a) (rationalp b))
          (equal (< (+ -1 a) b) (< a (+ 1 b))))
 :hints (("Goal" :cases ((< (+ -1 a) b)) :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbw-nthcdr-consp
 (implies (natp i) (equal (consp (nthcdr i xs)) (< i (len xs))))
 :hints (("Goal" :induct (nthcdr i xs)
 :in-theory (union-theories (theory 'ground-zero) '(nthcdr len natp zp fn-lbw-less-shift))))))

(local (defthm fn-lbw-nthcdr-car
 (equal (car (nthcdr i xs)) (nth i xs))
 :hints (("Goal" :induct (nthcdr i xs)
 :in-theory (union-theories (theory 'ground-zero) '(nthcdr nth zp))))))

(local (defthm fn-lbw-nthcdr-cdr
 (implies (natp i) (equal (cdr (nthcdr i xs)) (nthcdr (+ 1 i) xs)))
 :hints (("Goal" :induct (nthcdr i xs)
 :in-theory (union-theories (theory 'ground-zero) '(nthcdr natp zp))))))

(defthm fn-lbw-native-catalog-binding-is-model
 (implies (natp i)
 (equal (not (fn-lbw-unbound-catalog-rows i fn-arena fn-cat log))
        (fn-lb-arena-is-log fn-arena (nthcdr i fn-cat) log)))
 :hints (("Goal" :induct (fn-lbw-unbound-catalog-rows i fn-arena fn-cat log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbw-unbound-catalog-rows fn-lb-arena-is-log fn-cat-count-is-len
   fn-cat-at-is-nth fn-lbw-nthcdr-consp fn-lbw-nthcdr-car fn-lbw-nthcdr-cdr
   natp)))))

(defthm fn-lbw-unbound-catalog-rows-iff-not-binding
 (implies (natp i)
 (iff (fn-lbw-unbound-catalog-rows i fn-arena fn-cat log)
      (not (fn-lb-arena-is-log fn-arena (nthcdr i fn-cat) log))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbw-native-catalog-binding-is-model))
 :in-theory (theory 'ground-zero))))
