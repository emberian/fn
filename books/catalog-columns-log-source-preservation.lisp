; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-old-row-preservation")

(local (defthm fn-lblsp-next-range-not-bad
 (not (equal (fn-lb-log-model-next-range payload) :bad))
 :hints (("Goal" :do-not-induct t :cases ((equal payload :bad))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-next-range fn-la-tombstone-raw fn-lb-log-model-payload-wire-true-listp
 true-listp (:executable-counterpart fn-rcl-tombstonep)))))))

(local (defthm fn-lblsp-home-frame-not-bad
 (implies (fn-cat-rowp old) (not (equal (fn-lb-log-model-home-frame old) :bad)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-model-home-frame-is-octets (row old)))
 :cases ((equal (fn-lb-log-model-home-frame old) :bad))
 :in-theory (union-theories (theory 'ground-zero) '((:executable-counterpart fn-cbor-octet-listp)))))))

(local (defthm fn-lblsp-old-handle-natural
 (implies (fn-cat-rowp old) (natp (fn-record-payload old)))
 :hints (("Goal" :in-theory (enable fn-cat-rowp)))))

(defthm fn-lb-log-row-sourcep-of-fresh-append-old
 (implies (and (fn-cat-rowp old) (fn-lb-log-row-sourcep old log)
               (not (fn-lb-log-model-row-entry row log)))
 (fn-lb-log-row-sourcep old (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-row-entry-of-fresh-append-old)
       (:instance fn-lb-log-row-segment-of-fresh-append-old)
       (:instance fn-lb-log-append-preserves-existing-range
 (seg (fn-lb-log-model-row-segment old log))
 (off (nth 3 (fn-lb-log-model-row-entry old log)))
 (count (nth 4 (fn-lb-log-model-row-entry old log))))
       (:instance fn-lb-log-append-preserves-existing-home-frame
 (position (list (fn-lb-log-model-row-segment old log)
 (+ (nth 3 (fn-lb-log-model-row-entry old log)) (nth 4 (fn-lb-log-model-row-entry old log))))))
       (:instance fn-lb-log-append-preserves-verified-entry
 (seg (fn-lb-log-model-row-segment old log)) (off (nth 3 (fn-lb-log-model-row-entry old log)))))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lb-log-row-sourcep fn-lblsp-old-handle-natural fn-lblsp-next-range-not-bad fn-lblsp-home-frame-not-bad))
 '((tau-system))))))

(defthm fn-lb-log-rows-sourcep-of-fresh-append-old
 (implies (and (fn-cat-rowsp rows) (fn-lb-log-rows-sourcep rows log)
               (not (fn-lb-log-model-row-entry row log)))
 (fn-lb-log-rows-sourcep rows (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :induct (len rows)
 :in-theory (union-theories (theory 'ground-zero)
 '(len fn-cat-rowsp fn-lb-log-rows-sourcep fn-lb-log-row-sourcep-of-fresh-append-old)))))

(defthm fn-lb-log-rows-sourcep-of-fresh-append-cons
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload) (fn-lb-log-layoutp log)
 (not (fn-lb-log-model-row-entry row log)) (fn-cat-rowsp rows) (fn-lb-log-rows-sourcep rows log))
 (fn-lb-log-rows-sourcep (cons row rows) (fn-lb-log-model-append row payload target log)))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lb-log-rows-sourcep (cons row rows) (fn-lb-log-model-append row payload target log)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-row-sourcep-of-fresh-append fn-lb-log-rows-sourcep-of-fresh-append-old)))))
