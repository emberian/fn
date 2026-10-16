; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-rebuild-old-frames")

(local (defthm fn-lbrrc-count-natural
 (natp (fn-lbc-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len))))))

(local (defthm fn-lbrrc-next-prefix-last
 (equal (if (zp (fn-lbc-count (fn-lbc-number-put-row numbers j (fn-lbc-append-row row log fn-lbc)))) 0 (fn-lbc-value (- (fn-lbc-count (fn-lbc-number-put-row numbers j (fn-lbc-append-row row log fn-lbc))) 1) :prefix-max (fn-lbc-number-put-row numbers j (fn-lbc-append-row row log fn-lbc)))) (max (nfix (if (zp (fn-lbc-count fn-lbc)) 0 (fn-lbc-value (- (fn-lbc-count fn-lbc) 1) :prefix-max fn-lbc))) (nfix (fn-record-stamp row))))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbc-count-of-number-put-row fn-lbc-count-of-append-row fn-lbc-value-of-number-put-row
 fn-lbc-prefix-max-of-append-row-new (:type-prescription fn-lbrrc-count-natural)))))))

(local (defthm fn-lbrrc-nfix-natural (implies (natp x) (equal (nfix x) x)) :hints (("Goal" :in-theory (enable nfix)))))

(local (defthm fn-lbrrc-rows-corr-atom (implies (not (consp rows)) (fn-lbc-rows-corr i rows pm fn-lbc log)) :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-rows-corr))))))

(defthm fn-lbc-rebuild-rows-establishes-rows-corr
 (implies (and (fn-cat-rowsp rows) (fn-lbc-rows-log-guardp rows log)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (fn-lb-log-rows-sourcep rows log)
 (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-columns-directory-alignedp fn-lbc))
 (fn-lbc-rows-corr (fn-lbc-count fn-lbc) rows (if (zp (fn-lbc-count fn-lbc)) 0 (fn-lbc-value (- (fn-lbc-count fn-lbc) 1) :prefix-max fn-lbc)) (fn-lbc-rebuild-rows rows log fn-lbc) log))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc)
 :expand ((:free (start pm columns) (fn-lbc-rows-corr start rows pm columns log)))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbrrc-nfix-natural fn-lbrrc-rows-corr-atom fn-lbc-rebuild-rows fn-cat-rowsp fn-lbc-rows-log-guardp
 fn-lb-log-rows-sourcep fn-lbc-prefix-max-of-append-row-new fn-lbc-value-of-number-put-row 
 fn-lbc-row-corr-of-number-put-row
 fn-lb-column-row-pointerp-of-number-put-row
 fn-lb-columns-pool-layoutp-of-append-row fn-lb-columns-pool-layoutp-of-number-put-row
 fn-lb-columns-directory-alignedp-of-append-row fn-lb-columns-directory-alignedp-of-number-put-row
 fn-lbc-count-of-append-row fn-lbc-count-of-number-put-row (:type-prescription fn-lbrrc-count-natural))) '(max nfix (tau-system))))
("Subgoal *1/1" :use ((:instance fn-lbc-row-corr-of-rebuild-rows-old
 (i (fn-lbc-count fn-lbc)) (old-row (car rows))
 (pm (max (nfix (if (zp (fn-lbc-count fn-lbc)) 0 (fn-lbc-value (- (fn-lbc-count fn-lbc) 1) :prefix-max fn-lbc))) (nfix (fn-record-stamp (car rows)))))
 (rows (cdr rows))
 (fn-lbc (fn-lbc-number-put-row (fn-held-numbers (car rows)) (fn-lbc-count fn-lbc)
            (fn-lbc-append-row (car rows) log fn-lbc)))) (:instance fn-lb-column-row-pointerp-of-append-row-new (row (car rows))) (:instance fn-lbc-row-corr-from-row-source (row (car rows)))
 (:instance fn-lbrrc-next-prefix-last (row (car rows)) (numbers (fn-held-numbers (car rows))) (j (fn-lbc-count fn-lbc)))))))
