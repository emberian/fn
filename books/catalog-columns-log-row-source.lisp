; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-type-preservation")
(include-book "lb-log-payload-agreement-properties")

(defun-nx fn-lb-log-row-sourcep (row log)
 (let* ((entry (fn-lb-log-model-row-entry row log))
        (seg (fn-lb-log-model-row-segment row log))
        (off (nth 3 entry)) (count (nth 4 entry)) (payload (nth 6 entry)))
 (and entry
  (fn-lb-log-row-copies-agreep row payload log)
  (equal (nth 7 entry) (fn-lb-log-model-homes row))
  (fn-arx-entry-ok (fn-lb-entry-octets seg off log) (fn-lb-entry-protected-len seg off log))
  (equal (fn-lb-log-model-read-range seg off count log) (fn-lb-log-model-next-range payload))
  (equal (fn-lb-log-model-read-home-frame (list seg (+ off count)) log)
         (fn-lb-log-model-home-frame row)))))

(defun-nx fn-lb-log-rows-sourcep (rows log)
 (if (consp rows) (and (fn-lb-log-row-sourcep (car rows) log)
                      (fn-lb-log-rows-sourcep (cdr rows) log)) t))

(defthm fn-lb-log-rows-sourcep-gives-payload-agreement
 (implies (fn-lb-log-rows-sourcep rows log) (fn-lb-retained-payloads-agreep rows log))
 :hints (("Goal" :induct (len rows) :in-theory (union-theories (theory 'ground-zero)
  '(len fn-lb-log-rows-sourcep fn-lb-log-row-sourcep fn-lb-retained-payloads-agreep fn-lb-log-payload)))))

(local (defthm fn-lblrs-handle-natural
 (implies (fn-cat-rowp row) (natp (fn-record-payload row)))
 :hints (("Goal" :in-theory (enable fn-cat-rowp)))))

(local (defthm fn-lblrs-next-entry-present
 (consp (fn-lb-log-model-next-entry row payload segment)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-next-entry (:executable-counterpart consp)))))))

(defthm fn-lb-log-row-sourcep-of-fresh-append
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload) (fn-lb-log-layoutp log)
               (not (fn-lb-log-model-row-entry row log)))
 (fn-lb-log-row-sourcep row (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-fresh-append-verified-entry)
       (:instance fn-lb-log-fresh-append-stored-range)
       (:instance fn-lb-log-fresh-append-home-frame))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-row-sourcep fn-lblrs-handle-natural fn-lb-log-append-fresh-row-entry
 fn-lb-log-append-fresh-row-segment fn-lb-log-next-entry-homes-by-definition
 fn-lb-log-next-entry-payload-by-definition fn-lb-log-row-copies-agree-of-fresh-append (:type-prescription fn-lblrs-next-entry-present))))))

(defthm fn-lbc-row-corr-from-row-source
 (implies (and (fn-cat-rowp row) (fn-lbc-row-log-guardp row log)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (fn-lb-log-row-sourcep row log)
 (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-columns-directory-alignedp fn-lbc))
 (fn-lbc-row-corr (fn-lbc-count fn-lbc) row
 (max (nfix (if (zp (fn-lbc-count fn-lbc)) 0 (fn-lbc-value (- (fn-lbc-count fn-lbc) 1) :prefix-max fn-lbc)))
      (nfix (fn-record-stamp row)))
 (fn-lbc-append-row row log fn-lbc) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-row-corr-of-append-row-from-log))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-row-sourcep fn-lb-log-payload fn-lb-log-model-next-range)))))

(defthm fn-lbc-row-corr-after-typed-fresh-log-append
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload)
 (fn-lb-log-layoutp log) (fn-lb-log-model-segsp log) (unsigned-byte-p 64 target)
 (not (fn-lb-log-model-row-entry row log))
 (fn-lbc-row-log-guardp row (fn-lb-log-model-append row payload target log))
 (fn-lb-columns-pool-layoutp fn-lbc) (fn-lb-columns-directory-alignedp fn-lbc))
 (fn-lbc-row-corr (fn-lbc-count fn-lbc) row
 (max (nfix (if (zp (fn-lbc-count fn-lbc)) 0 (fn-lbc-value (- (fn-lbc-count fn-lbc) 1) :prefix-max fn-lbc)))
      (nfix (fn-record-stamp row)))
 (fn-lbc-append-row row (fn-lb-log-model-append row payload target log) fn-lbc)
 (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-row-corr-after-fresh-log-append)
       (:instance fn-lb-log-append-preserves-type))
 :in-theory (theory 'minimal-theory))))
