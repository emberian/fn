; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-interned-sources")
(include-book "lb-log-open-properties")

(defthm fn-intern-row-at-is-held
 (implies (and (fn-record-p w) (natp generation) (natp h))
 (fn-held-p (fn-intern-row-at w keyring generation h)))
 :hints (("Goal" :in-theory (enable fn-intern-row-at fn-record-p fn-held-p
 fn-record-internals fn-held-internals fn-hf-p fn-hc-p fn-hf-startp fn-hc-verdictp))))

(local (defthm fn-lboht-arena-count-natural
 (natp (fn-arena-count fn-arena))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len natp))))))

(local (defthm fn-lboht-cat-row-natural-head
 (implies (fn-cat-rowp x) (natp (car x)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-rowp fn-held-shapep fn-record-uint64p fn-held-sequence fn-cbor-ag-car natp))))))

(local (defthm fn-lboht-cat-row-has-fifteen-fields
 (implies (fn-cat-rowp x) (equal (len x) 15))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-rowp fn-held-shapep))))))

(local (defthm fn-lboht-wire-control-is-no-catalog-row
 (implies (and (fn-wire-event-p x) (not (fn-record-p x)) (not (fn-stxa-p x)))
 (and (not (fn-cat-rowp x)) (not (fn-sca-composite-shapep x))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lboht-cat-row-natural-head) (:instance fn-lboht-cat-row-has-fifteen-fields))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-stxe-sequence fn-stxk-sequence fn-record-uint32p fn-cp-nth fn-th-at fn-store-event-nth fn-cbor-ag-car fn-cbor-ag-cdr natp fn-wire-event-p fn-sca-composite-shapep fn-store-retention-event-p fn-stxe-p fn-stxe-shapep
 fn-stxk-p fn-stxk-shapep fn-cpe-eventp fn-th-topic-eventp fn-th-local-admin-eventp))))))

(local (defthm fn-lboht-intern-row-at-count-is-catalog-row
 (implies (and (fn-record-p w) (natp generation))
 (fn-cat-rowp (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-held-p-of-intern-list)
       (:instance fn-held-p-implies-cat-rowp (x (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-intern-list-is-row-at-count))))))

(local (defthm fn-lboht-hstxa-make-is-not-catalog-row
 (not (fn-cat-rowp (fn-hstxa-make w h)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lboht-cat-row-natural-head (x (fn-hstxa-make w h))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-hstxa-make natp))))))

(local (defthm fn-lboht-composite-make-shape
 (equal (fn-sca-composite-shapep (fn-hstxa-make w h)) (fn-cat-rowp h))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-sca-composite-shapep fn-hstxa-make fn-hstxa-held fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lboht-composite-make-held
 (equal (fn-hstxa-held (fn-hstxa-make w h)) h)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-hstxa-make fn-hstxa-held fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lboht-record-is-consp
 (implies (fn-record-p w) (consp w))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-record-p fn-record-shapep))))))

(local (defthm fn-lboht-intern-event-held-rows
 (implies (and (natp generation)
 (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
 (equal (fn-lb-open-held-rows (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))
 (if (fn-lb-open-wire-article w)
  (list (fn-intern-row-at (fn-lb-open-wire-article w) keyring generation (fn-arena-count fn-arena))) nil)))
 :hints (("Goal" :do-not-induct t :cases ((fn-record-p w) (fn-stxa-p w))
 :use ((:instance fn-lboht-wire-control-is-no-catalog-row (x w)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-intern-event fn-lb-open-held-rows fn-lb-open-wire-article fn-cat-intern-list-is-row-at-count
 fn-lboht-intern-row-at-count-is-catalog-row fn-lboht-hstxa-make-is-not-catalog-row
 fn-lboht-composite-make-shape fn-lboht-composite-make-held fn-lboht-record-is-consp))))))

(local (defthm fn-lboht-held-rows-cons-is-singleton-append
 (equal (fn-lb-open-held-rows (cons r rs))
        (append (fn-lb-open-held-rows (list r)) (fn-lb-open-held-rows rs)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-held-rows binary-append))))))

(local (defthm fn-lboht-held-rows-cons-append-gated
 (implies (syntaxp (not (equal rs ''nil)))
 (equal (fn-lb-open-held-rows (cons r rs))
        (append (fn-lb-open-held-rows (list r)) (fn-lb-open-held-rows rs))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lboht-held-rows-cons-is-singleton-append))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lboht-empty-held-rows-by-definition
 (equal (fn-lb-open-held-rows nil) nil)
 :hints (("Goal" :in-theory '(fn-lb-open-held-rows)))))

(local (defthm fn-lboht-intern-event-held-rows-car
 (implies (and (natp generation)
 (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
 (equal (fn-lb-open-held-rows (list (car (fn-intern-event w keyring generation fn-arena))))
 (if (fn-lb-open-wire-article w)
  (list (fn-intern-row-at (fn-lb-open-wire-article w) keyring generation (fn-arena-count fn-arena))) nil)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lboht-intern-event-held-rows))
 :in-theory (union-theories (theory 'ground-zero) '(mv-nth))))))

(local (defthm fn-lboht-count-native-type
 (natp (fn-arena-count fn-arena)) :rule-classes :type-prescription
 :hints (("Goal" :use ((:instance fn-lboht-arena-count-natural)) :in-theory (theory 'ground-zero)))))

(local (defthm fn-lboht-held-listp-append
 (implies (and (fn-held-listp a) (fn-held-listp b)) (fn-held-listp (append a b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero)
 '(len fn-held-listp binary-append))))))

(defthm fn-lb-open-interned-rows-have-held-type
 (implies (and (natp generation)
 (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
 (fn-held-listp (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))))
 :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-intern-events fn-lboht-count-native-type fn-lboht-held-listp-append
 fn-lboht-empty-held-rows-by-definition fn-lboht-held-rows-cons-append-gated
 fn-lboht-intern-event-held-rows-car fn-intern-row-at-is-held fn-lb-open-wire-article-is-record
 fn-held-listp natp (:type-prescription fn-intern-event) (:type-prescription fn-intern-events)
 (:executable-counterpart fn-lb-open-held-rows))) '((tau-system))))))
