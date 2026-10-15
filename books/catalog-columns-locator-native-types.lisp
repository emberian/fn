; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-reconstruction")

(local (defthm fn-lblnt-row-loc0-u64
 (implies (and (adt-seq-p *fn-lbc-rowwords-schema* rows) (natp i) (< i (len rows)))
 (unsigned-byte-p 64 (nth 1 (nth i rows))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance adt-tp-rec-p-nth (s *fn-lbc-rowwords-schema*) (a rows)))
 :expand ((nth 1 (nth i rows)))
 :in-theory (union-theories (theory 'ground-zero) '(adt-rec-p adt-val-okp nth))))))

(defthm fn-lbc-loc0-has-native-type
 (implies (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
 (unsigned-byte-p 64 (fn-lbc-loc0 i fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lblnt-row-loc0-u64 (rows (car fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-count fn-lbc-row-store fn-lbc-row-storep
 fn-lbc-rowwordsp-is-seq-p fn-lbc-rowwords-count-is-len fn-lbc-loc0
 fn-lbc-rowwords-get-loc0 fn-lbc-rowwords$a-get-loc0 nth)))))

(local (defthm fn-lblnt-row-loc1-u64
 (implies (and (adt-seq-p *fn-lbc-rowwords-schema* rows) (natp i) (< i (len rows)))
 (unsigned-byte-p 64 (nth 2 (nth i rows))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance adt-tp-rec-p-nth (s *fn-lbc-rowwords-schema*) (a rows)))
 :expand ((nth 2 (nth i rows)))
 :in-theory (union-theories (theory 'ground-zero) '(adt-rec-p adt-val-okp nth))))))

(defthm fn-lbc-loc1-has-native-type
 (implies (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
 (unsigned-byte-p 64 (fn-lbc-loc1 i fn-lbc)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lblnt-row-loc1-u64 (rows (car fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-count fn-lbc-row-store fn-lbc-row-storep
 fn-lbc-rowwordsp-is-seq-p fn-lbc-rowwords-count-is-len fn-lbc-loc1
 fn-lbc-rowwords-get-loc1 fn-lbc-rowwords$a-get-loc1 nth)))))

(defthm fn-lbc-locator-has-native-domain
 (implies (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
 (fn-locp (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-locp fn-lbc-loc0-has-native-type fn-lbc-loc1-has-native-type)))))
