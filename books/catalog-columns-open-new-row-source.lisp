; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-source-preservation")

(defthm fn-lb-log-rows-sourcep-of-append
 (equal (fn-lb-log-rows-sourcep (append a b) log)
        (and (fn-lb-log-rows-sourcep a log) (fn-lb-log-rows-sourcep b log)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero)
 '(len fn-lb-log-rows-sourcep binary-append)))))

(defthm fn-lb-log-open-tail-keeps-new-row-source
 (implies (and (natp h) (fn-cat-rowp row) (equal (fn-record-payload row) h)
 (fn-cbor-octet-listp payload) (fn-lb-log-layoutp log) (fn-lb-log-handles-below log h))
 (fn-lb-log-row-sourcep row
  (fn-lb-log-model-open-events tail keyring generation (+ 1 h) target
   (fn-lb-log-model-append row payload target log))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-handles-below-gives-fresh-key (n h))
 (:instance fn-lb-log-row-sourcep-of-fresh-append)
 (:instance fn-lb-log-handles-below-of-append (n h) (newn (+ 1 h)))
 (:instance fn-lb-log-rows-sourcep-preserved-by-open-events
 (ws tail) (h (+ 1 h)) (rows (list row)) (log (fn-lb-log-model-append row payload target log))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-rows-sourcep fn-cat-rowsp natp nfix)))))
