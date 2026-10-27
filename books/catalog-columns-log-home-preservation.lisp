; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-served-establishment")
(include-book "log-verified-map-append")

(local (defthm fn-lblhp-segment-append-preserves-id
 (equal (car (fn-lb-log-model-append-to-segment row payload segment)) (car segment))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append-to-segment))))))

(local (defthm fn-lblhp-existing-segment-after-append
 (implies (fn-lb-log-model-segment seg log)
 (equal (fn-lb-log-model-segment seg (fn-lb-log-model-append row payload target log))
 (if (equal seg target) (fn-lb-log-model-append-to-segment row payload (fn-lb-log-model-segment seg log)) (fn-lb-log-model-segment seg log))))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append fn-lb-log-model-segment fn-lblhp-segment-append-preserves-id))))))

(local (defthm fn-lblhp-existing-home-entry-in-append
 (implies (fn-lb-log-model-home-entry position entries)
 (equal (fn-lb-log-model-home-entry position (append entries tail))
        (fn-lb-log-model-home-entry position entries)))
 :hints (("Goal" :induct (fn-lb-log-model-home-entry position entries)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-home-entry binary-append))))))

(local (defthm fn-lblhp-home-entry-in-appended-segment
 (implies (fn-lb-log-model-home-entry position (caddr segment))
 (equal (fn-lb-log-model-home-entry position (caddr (fn-lb-log-model-append-to-segment row payload segment)))
        (fn-lb-log-model-home-entry position (caddr segment))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-append-to-segment-directory-by-definition fn-lblhp-existing-home-entry-in-append))))))

(defthm fn-lb-log-existing-home-entry-survives-append
 (implies (fn-lb-log-model-home-entry position (caddr (fn-lb-log-model-segment seg log)))
 (equal (fn-lb-log-model-home-entry position
          (caddr (fn-lb-log-model-segment seg (fn-lb-log-model-append row payload target log))))
        (fn-lb-log-model-home-entry position (caddr (fn-lb-log-model-segment seg log)))))
 :hints (("Goal" :do-not-induct t :cases ((fn-lb-log-model-segment seg log) (equal seg target))
 :use ((:instance fn-lblhp-existing-segment-after-append)
 (:instance fn-lblhp-home-entry-in-appended-segment (segment (fn-lb-log-model-segment seg log))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-home-entry)))))

(local (defthm fn-lblhp-good-home-read-domain
 (implies (not (equal (fn-lb-log-model-read-home-frame position log) :bad))
 (let* ((entry (fn-lb-log-model-home-entry (cadr position) (caddr (fn-lb-log-model-segment (car position) log))))
        (end (+ (nfix (nth 1 entry)) (nfix (nth 2 entry)))))
 (and entry (natp (cadr position)) (<= (cadr position) end)
 (not (equal (fn-lb-log-model-read-range (car position) (cadr position) (- end (cadr position)) log) :bad)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-read-home-frame))))))

(defthm fn-lb-log-append-preserves-existing-home-frame
 (implies (not (equal (fn-lb-log-model-read-home-frame position log) :bad))
 (equal (fn-lb-log-model-read-home-frame position (fn-lb-log-model-append row payload target log))
        (fn-lb-log-model-read-home-frame position log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lblhp-good-home-read-domain)
 (:instance fn-lb-log-existing-home-entry-survives-append (seg (car position)) (position (cadr position))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-read-home-frame fn-lb-log-append-preserves-existing-range)))))
