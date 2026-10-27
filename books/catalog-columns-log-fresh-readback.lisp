; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-range-locator")

(local (defthm fn-lblfr-row-handle-natural
 (implies (fn-cat-rowp row) (natp (fn-record-payload row)))
 :hints (("Goal" :in-theory (enable fn-cat-rowp)))))

(local (defthm fn-lblfr-next-entry-present
 (consp (fn-lb-log-model-next-entry row payload segment))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-next-entry (:executable-counterpart consp)))))))

(local (defthm fn-lblfr-range-entry-is-new-entry
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload) (fn-lb-log-layoutp log) (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-log-model-range-entry (nth 3 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))) (caddr (fn-lb-log-model-segment target (fn-lb-log-model-append row payload target log)))) (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-range-entry-of-row-locator (log (fn-lb-log-model-append row payload target log))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append-preserves-layout fn-lb-log-append-fresh-row-entry
 fn-lb-log-append-fresh-row-segment fn-lblfr-row-handle-natural
 (:type-prescription fn-lblfr-next-entry-present)))))))

(defthm fn-lb-log-fresh-append-protected-length
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload) (fn-lb-log-layoutp log) (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-entry-protected-len target (nth 3 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))) (fn-lb-log-model-append row payload target log)) (len (fn-lb-log-model-next-prefix row payload))))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lb-entry-protected-len fn-lblfr-range-entry-is-new-entry fn-lb-log-next-entry-protected-length-by-definition)))))

(defthm fn-lb-log-fresh-append-entry-octets
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload) (fn-lb-log-layoutp log) (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-entry-octets target (nth 3 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))) (fn-lb-log-model-append row payload target log))
        (append (fn-lb-log-model-next-prefix row payload) (fn-blake3-stobj (fn-lb-log-model-next-prefix row payload)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lb-log-read-new-sealed-entry-interval)) :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lb-entry-octets fn-lblfr-range-entry-is-new-entry
 fn-lb-log-next-entry-entry-offset-by-definition fn-lb-log-next-entry-protected-length-by-definition
 (:type-prescription fn-lblfr-next-entry-present))))))

(defthm fn-lb-log-fresh-append-verified-entry
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload) (fn-lb-log-layoutp log) (not (fn-lb-log-model-row-entry row log)))
 (fn-arx-entry-ok (fn-lb-entry-octets target (nth 3 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))) (fn-lb-log-model-append row payload target log)) (fn-lb-entry-protected-len target (nth 3 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))) (fn-lb-log-model-append row payload target log))))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lb-log-fresh-append-entry-octets fn-lb-log-fresh-append-protected-length
 fn-lb-log-sealed-prefix-is-verified fn-lb-log-next-prefix-true-listp)))))

(defthm fn-lb-log-fresh-append-stored-range
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload) (fn-lb-log-layoutp log) (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-log-model-read-range target (nth 3 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))) (nth 4 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))) (fn-lb-log-model-append row payload target log))
        (fn-lb-log-model-next-range payload)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lb-log-read-new-payload-interval)) :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lb-log-next-entry-served-offset-by-definition fn-lb-log-next-entry-served-length-by-definition
 )))))

(local (defthm fn-lblfr-home-entry-is-new-entry
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload) (fn-lb-log-layoutp log) (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-log-model-home-entry (+ (nfix (nth 3 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log)))) (nfix (nth 4 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log)))))
    (caddr (fn-lb-log-model-segment target (fn-lb-log-model-append row payload target log)))) (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-home-entry-of-row-locator (log (fn-lb-log-model-append row payload target log))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append-preserves-layout fn-lb-log-append-fresh-row-entry
 fn-lb-log-append-fresh-row-segment fn-lblfr-row-handle-natural
 (:type-prescription fn-lblfr-next-entry-present)))))))

(defthm fn-lb-log-fresh-append-home-frame
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload) (fn-lb-log-layoutp log) (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-log-model-read-home-frame (list target (+ (nth 3 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))) (nth 4 (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))))) (fn-lb-log-model-append row payload target log))
        (fn-lb-log-model-home-frame row)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lblfr-home-entry-is-new-entry) (:instance fn-lb-log-read-new-home-interval))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-read-home-frame fn-lb-log-next-entry-entry-offset-by-definition
 fn-lb-log-next-entry-protected-length-by-definition fn-lb-log-next-entry-served-offset-by-definition
 fn-lb-log-next-entry-served-length-by-definition
 fn-lb-log-next-prefix-length (:type-prescription fn-lblfr-next-entry-present))))))
