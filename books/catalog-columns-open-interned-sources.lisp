; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-new-row-source")
(include-book "lb-log-open-properties")

(local (defthm fn-lbosn-intern-row-at-payload
 (equal (fn-record-payload (fn-intern-row-at w keyring generation h)) h)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-intern-row-at fn-held-make fn-record-payload fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbosn-intern-event-arena-is-wire-seal
 (equal (mv-nth 1 (fn-intern-event w keyring generation fn-arena))
 (if (fn-lb-open-wire-article w)
     (fn-arena-seal-list (fn-record-payload (fn-lb-open-wire-article w)) fn-arena) fn-arena))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-intern-event-arena))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-wire-article))))))

(local (defthm fn-lbosn-intern-event-count
 (equal (fn-arena-count (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
 (+ (if (fn-lb-open-wire-article w) 1 0) (fn-arena-count fn-arena)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbosn-intern-event-arena-is-wire-seal))
 :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len fn-arena-seal-list-len))))))

(local (defthm fn-lbosn-arena-count-natural
 (natp (fn-arena-count fn-arena))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len natp))))))

(local (defthm fn-lbosn-new-entry-allocation
 (implies (and (fn-lb-log-handles-below log h) (natp h))
 (fn-lb-log-handles-below
  (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) payload target log) (+ 1 h)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-handles-below-of-append (n h) (newn (+ 1 h)) (row (fn-intern-row-at w keyring generation h))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbosn-intern-row-at-payload natp))))))

(local (defthm fn-lbosn-cat-row-natural-head
 (implies (fn-cat-rowp x) (natp (car x)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-rowp fn-held-shapep fn-record-uint64p fn-held-sequence fn-cbor-ag-car natp))))))

(local (defthm fn-lbosn-cat-row-has-fifteen-fields
 (implies (fn-cat-rowp x) (equal (len x) 15))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-rowp fn-held-shapep))))))

(local (defthm fn-lbosn-wire-control-is-no-catalog-row
 (implies (and (fn-wire-event-p x) (not (fn-record-p x)) (not (fn-stxa-p x)))
 (and (not (fn-cat-rowp x)) (not (fn-sca-composite-shapep x))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbosn-cat-row-natural-head) (:instance fn-lbosn-cat-row-has-fifteen-fields))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-stxe-sequence fn-stxk-sequence fn-record-uint32p fn-cp-nth fn-th-at fn-store-event-nth fn-cbor-ag-car fn-cbor-ag-cdr natp fn-wire-event-p fn-sca-composite-shapep fn-store-retention-event-p fn-stxe-p fn-stxe-shapep
 fn-stxk-p fn-stxk-shapep fn-cpe-eventp fn-th-topic-eventp fn-th-local-admin-eventp))))))

(local (defthm fn-lbosn-intern-row-at-count-is-catalog-row
 (implies (and (fn-record-p w) (natp generation))
 (fn-cat-rowp (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-held-p-of-intern-list)
       (:instance fn-held-p-implies-cat-rowp (x (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-intern-list-is-row-at-count))))))

(local (defthm fn-lbosn-hstxa-make-is-not-catalog-row
 (not (fn-cat-rowp (fn-hstxa-make w h)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbosn-cat-row-natural-head (x (fn-hstxa-make w h))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-hstxa-make natp))))))

(local (defthm fn-lbosn-composite-make-shape
 (equal (fn-sca-composite-shapep (fn-hstxa-make w h)) (fn-cat-rowp h))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-sca-composite-shapep fn-hstxa-make fn-hstxa-held fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbosn-composite-make-held
 (equal (fn-hstxa-held (fn-hstxa-make w h)) h)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-hstxa-make fn-hstxa-held fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbosn-record-is-consp
 (implies (fn-record-p w) (consp w))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-record-p fn-record-shapep))))))

(local (defthm fn-lbosn-intern-event-held-rows
 (implies (and (natp generation)
 (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
 (equal (fn-lb-open-held-rows (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))
 (if (fn-lb-open-wire-article w)
  (list (fn-intern-row-at (fn-lb-open-wire-article w) keyring generation (fn-arena-count fn-arena))) nil)))
 :hints (("Goal" :do-not-induct t :cases ((fn-record-p w) (fn-stxa-p w))
 :use ((:instance fn-lbosn-wire-control-is-no-catalog-row (x w)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-intern-event fn-lb-open-held-rows fn-lb-open-wire-article fn-cat-intern-list-is-row-at-count
 fn-lbosn-intern-row-at-count-is-catalog-row fn-lbosn-hstxa-make-is-not-catalog-row
 fn-lbosn-composite-make-shape fn-lbosn-composite-make-held fn-lbosn-record-is-consp))))))

(local (defthm fn-lbosn-held-rows-cons-is-singleton-append
 (equal (fn-lb-open-held-rows (cons r rs))
        (append (fn-lb-open-held-rows (list r)) (fn-lb-open-held-rows rs)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-held-rows binary-append))))))

(local (defthm fn-lbosn-record-payload-octets
 (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-record-p fn-record-payloadp))))))

(local (defthm fn-lbosn-payload-listp-of-append
 (implies (and (fn-arn-payload-listp a) (fn-arn-payload-listp b))
 (fn-arn-payload-listp (append a b)))
 :hints (("Goal" :induct (append a b)
 :in-theory (union-theories (theory 'ground-zero) '(fn-arn-payload-listp binary-append))))))

(local (defthm fn-lbosn-arena-p-of-seal
 (implies (and (fn-arena-p fn-arena) (fn-cbor-octet-listp payload))
 (fn-arena-p (fn-arena-seal-list payload fn-arena)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-arena-p-is-payload-listp fn-arena-seal-list-is-append fn-lbosn-payload-listp-of-append fn-arn-payload-listp))))))

(local (defthm fn-lbosn-one-intern-preserves-arena-p
 (implies (fn-arena-p fn-arena)
 (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbosn-record-payload-octets (w (fn-lb-open-wire-article w))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbosn-intern-event-arena-is-wire-seal fn-lb-open-wire-article-is-record fn-lbosn-arena-p-of-seal))))))

(local (defun-nx fn-lbosn-open-induct (ws keyring generation target log fn-arena)
 (declare (xargs :measure (acl2-count ws) :verify-guards nil))
 (if (consp ws)
  (let* ((a (fn-lb-open-wire-article (car ws)))
         (h (fn-arena-count fn-arena))
         (log2 (if a (fn-lb-log-model-append (fn-intern-row-at a keyring generation h) (fn-record-payload a) target log) log)))
   (fn-lbosn-open-induct (cdr ws) keyring generation target log2
    (mv-nth 1 (fn-intern-event (car ws) keyring generation fn-arena))))
  (list ws log fn-arena))))

(local (defthm fn-lbosn-held-rows-cons-append-gated
 (implies (syntaxp (not (equal rs ''nil)))
 (equal (fn-lb-open-held-rows (cons r rs))
        (append (fn-lb-open-held-rows (list r)) (fn-lb-open-held-rows rs))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbosn-held-rows-cons-is-singleton-append))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbosn-empty-held-rows-by-definition
 (equal (fn-lb-open-held-rows nil) nil)
 :hints (("Goal" :in-theory '(fn-lb-open-held-rows)))))

(local (defthm fn-lbosn-intern-event-held-rows-car
 (implies (and (natp generation)
 (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
 (equal (fn-lb-open-held-rows (list (car (fn-intern-event w keyring generation fn-arena))))
 (if (fn-lb-open-wire-article w)
  (list (fn-intern-row-at (fn-lb-open-wire-article w) keyring generation (fn-arena-count fn-arena))) nil)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbosn-intern-event-held-rows))
 :in-theory (union-theories (theory 'ground-zero) '(mv-nth))))))

(local (defthm fn-lbosn-arena-count-natural-type
 (natp (fn-arena-count fn-arena)) :rule-classes :type-prescription
 :hints (("Goal" :use ((:instance fn-lbosn-arena-count-natural))
 :in-theory (theory 'ground-zero)))))

(defthm fn-lb-log-model-open-sources-interned-rows
 (implies (and (fn-arena-p fn-arena) (natp generation) (fn-lb-log-layoutp log)
 (fn-lb-log-handles-below log (fn-arena-count fn-arena))
 (fn-lb-open-records-guardp ws keyring generation (fn-arena-count fn-arena))
 (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
 (fn-lb-log-rows-sourcep
   (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))
   (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log)))
 :hints (("Goal" :induct (fn-lbosn-open-induct ws keyring generation target log fn-arena)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbosn-open-induct fn-intern-events fn-lb-log-model-open-events fn-lb-open-records-guardp
 (:type-prescription fn-intern-event) (:type-prescription fn-intern-events) (:executable-counterpart fn-lb-open-held-rows) fn-lbosn-empty-held-rows-by-definition fn-lbosn-held-rows-cons-append-gated
 fn-lb-log-rows-sourcep-of-append fn-lb-log-rows-sourcep
 fn-lbosn-intern-event-held-rows-car fn-lbosn-intern-event-count fn-lbosn-intern-row-at-payload
 fn-lb-log-open-tail-keeps-new-row-source fn-lbosn-record-payload-octets
 fn-lbosn-one-intern-preserves-arena-p fn-lbosn-new-entry-allocation
 fn-lbosn-arena-count-natural fn-lbosn-arena-count-natural-type fn-lb-log-model-append-preserves-layout
 fn-lb-open-wire-article-is-record natp)) '((tau-system))))))
