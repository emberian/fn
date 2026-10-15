; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-home-preservation")

(local (defthm fn-lblor-entry-in-append
 (implies (natp handle)
  (equal (fn-lb-log-model-row-entry-in sequence handle (append entries tail))
         (or (fn-lb-log-model-row-entry-in sequence handle entries)
             (fn-lb-log-model-row-entry-in sequence handle tail))))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
  :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-row-entry-in binary-append nth natp))))))

(local (defthm fn-lblor-entry-in-next-singleton
 (equal (fn-lb-log-model-row-entry-in sequence handle (list (fn-lb-log-model-next-entry row payload segment)))
        (and (equal sequence (fn-record-sequence row)) (equal handle (fn-record-payload row))
             (fn-lb-log-model-next-entry row payload segment)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-row-entry-in fn-lb-log-next-entry-handle-by-definition
     fn-lb-log-next-entry-sequence-by-definition car-cons cdr-cons (:executable-counterpart consp)))))))

(local (defthm fn-lblor-entry-in-appended-segment
 (implies (natp handle)
  (equal (fn-lb-log-model-row-entry-in sequence handle
           (caddr (fn-lb-log-model-append-to-segment row payload segment)))
         (or (fn-lb-log-model-row-entry-in sequence handle (caddr segment))
             (and (equal sequence (fn-record-sequence row)) (equal handle (fn-record-payload row))
                  (fn-lb-log-model-next-entry row payload segment)))))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-append-to-segment-directory-by-definition fn-lblor-entry-in-append fn-lblor-entry-in-next-singleton))))))

(local (defthm fn-lblor-appended-segment-id
 (equal (car (fn-lb-log-model-append-to-segment row payload segment)) (car segment))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lb-log-model-append-to-segment car-cons))))))

(local (defthm fn-lblor-entry-in-nil
 (equal (fn-lb-log-model-row-entry-in sequence handle nil) nil)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lb-log-model-row-entry-in (:executable-counterpart consp)))))))

(defthm fn-lb-log-row-entry-of-distinct-append
 (implies (and (natp (fn-record-payload old))
 (or (not (equal (fn-record-sequence old) (fn-record-sequence row)))
     (not (equal (fn-record-payload old) (fn-record-payload row)))))
 (equal (fn-lb-log-model-row-entry old (fn-lb-log-model-append row payload target log))
        (fn-lb-log-model-row-entry old log)))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append fn-lb-log-model-row-entry fn-lb-log-model-row-entry
 fn-lblor-entry-in-appended-segment fn-lblor-entry-in-next-singleton
 fn-lblor-entry-in-nil fn-lblor-appended-segment-id)) '(nth)))))

(defthm fn-lb-log-row-segment-of-distinct-append
 (implies (and (natp (fn-record-payload old))
 (or (not (equal (fn-record-sequence old) (fn-record-sequence row)))
     (not (equal (fn-record-payload old) (fn-record-payload row)))))
 (equal (fn-lb-log-model-row-segment old (fn-lb-log-model-append row payload target log))
        (fn-lb-log-model-row-segment old log)))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append fn-lb-log-model-row-entry fn-lb-log-model-row-segment
 fn-lblor-entry-in-appended-segment fn-lblor-entry-in-next-singleton
 fn-lblor-entry-in-nil fn-lblor-appended-segment-id)) '(nth)))))

(local (defthm fn-lblor-row-key-congruence
 (implies (and (equal (fn-record-sequence old) (fn-record-sequence row))
               (equal (fn-record-payload old) (fn-record-payload row)))
 (equal (fn-lb-log-model-row-entry old log) (fn-lb-log-model-row-entry row log)))
 :hints (("Goal" :induct (len log) :in-theory (union-theories (theory 'ground-zero)
 '(len fn-lb-log-model-row-entry))))))

(defthm fn-lb-log-row-entry-of-fresh-append-old
 (implies (and (natp (fn-record-payload old)) (fn-lb-log-model-row-entry old log)
               (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-log-model-row-entry old (fn-lb-log-model-append row payload target log))
        (fn-lb-log-model-row-entry old log)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lblor-row-key-congruence)
 (:instance fn-lb-log-row-entry-of-distinct-append))
 :in-theory (theory 'ground-zero))))

(defthm fn-lb-log-row-segment-of-fresh-append-old
 (implies (and (natp (fn-record-payload old)) (fn-lb-log-model-row-entry old log)
               (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-log-model-row-segment old (fn-lb-log-model-append row payload target log))
        (fn-lb-log-model-row-segment old log)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lblor-row-key-congruence)
 (:instance fn-lb-log-row-segment-of-distinct-append))
 :in-theory (theory 'ground-zero))))

(defthm fn-lb-log-payload-of-fresh-append-old
 (implies (and (natp (fn-record-payload old)) (fn-lb-log-model-row-entry old log)
               (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-log-payload old (fn-lb-log-model-append row payload target log))
        (fn-lb-log-payload old log)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-payload fn-lb-log-row-entry-of-fresh-append-old)))))
