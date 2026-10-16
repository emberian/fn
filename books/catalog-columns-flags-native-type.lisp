; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-flag-setter")

(local (defthm fn-lbsft-nth-flags-index (equal (nth 15 xs) (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr xs))))))))))))))))) :hints (("Goal" :in-theory (enable nth)))))

(local (defthm fn-lbsft-row-flags-u64
 (implies (and (adt-seq-p *fn-lbc-rowwords-schema* rows) (natp i) (< i (len rows)))
  (unsigned-byte-p 64 (nth 15 (nth i rows))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance adt-tp-rec-p-nth (s *fn-lbc-rowwords-schema*) (a rows)))
  :in-theory (union-theories (theory 'ground-zero) '(adt-rec-p adt-val-okp fn-lbsft-nth-flags-index))))))

(local (defthm fn-lbsft-nth-zero
 (equal (nth 0 xs) (car xs)) :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-lbc-flags-word-has-native-type
 (implies (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
  (unsigned-byte-p 64 (fn-lbc-word :flags i fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbsft-row-flags-u64 (rows (car fn-lbc))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-p fn-lbc-count fn-lbc-row-store fn-lbc-row-storep fn-lbsft-nth-zero
     fn-lbc-rowwordsp-is-seq-p fn-lbc-rowwords-count-is-len fn-lbsft-nth-flags-index fn-lbc-word-flags-by-definition)))))
