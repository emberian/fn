; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-lookup-properties")

(local (defthm fn-lbrhr-guard-gives-entry
 (implies (fn-lbc-row-log-guardp row log) (fn-lb-log-model-row-entry row log))
 :hints (("Goal" :cases ((fn-lb-log-model-row-entry row log)) :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-row-log-guardp unsigned-byte-p integer-range-p))))))

(local (defthm fn-lbrhr-nfix-u32
 (implies (unsigned-byte-p 32 x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(unsigned-byte-p integer-range-p nfix))))))

(defthm fn-lbc-home-entry-of-append-row-new
 (implies (and (fn-lbc-row-log-guardp row log) (fn-lb-log-layoutp log))
  (equal (fn-lbc-home-entry (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc) log)
         (fn-lb-log-model-row-entry row log)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbrhr-guard-gives-entry)
        (:instance fn-lbc-locator-of-append-row-new)
        (:instance fn-lb-log-home-entry-of-row-locator))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-home-entry fn-lbc-row-log-guardp fn-lbrhr-nfix-u32)))))

(defthm fn-lb-log-row-entry-binds-identity
 (implies (fn-lb-log-model-row-entry row log)
  (and (equal (nth 8 (fn-lb-log-model-row-entry row log)) (fn-record-sequence row))
       (equal (nth 5 (fn-lb-log-model-row-entry row log)) (fn-record-payload row))))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry row log)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-row-entry fn-lb-log-row-entry-in-binds-identity)) '(nth)))))

(local (defthm fn-lbrhr-row-entry-in-type
 (implies (and (fn-lb-log-model-entriesp entries) (fn-lb-log-model-row-entry-in sequence handle entries))
  (fn-lb-log-model-entryp (fn-lb-log-model-row-entry-in sequence handle entries)))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-row-entry-in fn-lb-log-model-entriesp))))))

(defthm fn-lb-log-row-entry-has-native-directory-type
 (implies (and (fn-lb-log-model-segsp log) (fn-lb-log-model-row-entry row log))
  (fn-lb-log-model-entryp (fn-lb-log-model-row-entry row log)))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry row log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-row-entry fn-lb-log-model-segsp fn-lbrhr-row-entry-in-type)))))
