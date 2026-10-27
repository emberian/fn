; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-fresh-directory")

(local (defthm fn-lblas-appended-segment-id
 (equal (car (fn-lb-log-model-append-to-segment row payload segment)) (car segment))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-append-to-segment car-cons)))) ))

(local (defthm fn-lblas-appended-segment-shape
 (equal (fn-lb-log-model-append-to-segment row payload (list (car segment) (cadr segment) (caddr segment)))
        (fn-lb-log-model-append-to-segment row payload segment))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-append-to-segment car-cons cdr-cons)))) ))

(defthm fn-lb-log-segment-of-append
 (equal (fn-lb-log-model-segment target (fn-lb-log-model-append row payload target log))
        (fn-lb-log-model-append-to-segment row payload
          (list target (cadr (fn-lb-log-model-segment target log))
                       (caddr (fn-lb-log-model-segment target log)))))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-append fn-lb-log-model-segment fn-lblas-appended-segment-id
     fn-lblas-appended-segment-shape)))))
