; Open binding: decoded wire payloads, actual intern and availability loader.
; The two generated folds are allocation/projection helpers, not cost twins.
(in-package "ACL2")
(include-book "lb-log-open-model")
(include-book "lb-arena-log-binding")
(include-book "catalog-availability-owner-load")

(local (defthm fn-lbof-row-entry-in-append
 (implies (natp handle)
 (equal (fn-lb-log-model-row-entry-in sequence handle (append entries tail))
 (or (fn-lb-log-model-row-entry-in sequence handle entries) (fn-lb-log-model-row-entry-in sequence handle tail))))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-row-entry-in binary-append nth natp))))))

(local (defthm fn-lbof-last-appended-entry
 (equal (car (last (append entries (list entry)))) entry)
 :hints (("Goal" :induct (append entries (list entry)) :in-theory (union-theories (theory 'ground-zero) '(binary-append last))))))

(local (defthm fn-lbof-segment-append-row-entry
 (implies (natp handle)
 (equal (fn-lb-log-model-row-entry-in sequence handle (caddr (fn-lb-log-model-append-to-segment row payload segment)))
 (or (fn-lb-log-model-row-entry-in sequence handle (caddr segment))
     (and (equal sequence (fn-record-sequence row)) (equal handle (fn-record-payload row))
          (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment))))))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append-to-segment fn-lbof-row-entry-in-append fn-lbof-last-appended-entry fn-lb-log-model-row-entry-in nth))))))

(local (defthm fn-lbof-segment-new-entry-is-present
 (consp (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment)))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append-to-segment fn-lbof-last-appended-entry))))))

(local (defthm fn-lbof-segment-new-entry-payload
 (equal (nth 6 (car (last (caddr (fn-lb-log-model-append-to-segment row payload segment))))) payload)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-append-to-segment fn-lbof-last-appended-entry nth))))))

(local (defthm fn-lbof-log-payload-of-cons
 (equal (fn-lb-log-payload query (cons segment log))
 (let ((entry (fn-lb-log-model-row-entry-in (fn-record-sequence query) (fn-record-payload query) (caddr segment))))
 (if entry (nth 6 entry) (fn-lb-log-payload query log))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-payload fn-lb-log-model-row-entry))))))

(local (defthm fn-lbof-log-payload-of-atom
 (implies (atom log) (equal (fn-lb-log-payload query log) nil))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-payload fn-lb-log-model-row-entry nth))))))

(local (defthm fn-lbof-row-entry-in-nil
 (equal (fn-lb-log-model-row-entry-in sequence handle nil) nil)
 :hints (("Goal" :in-theory '(fn-lb-log-model-row-entry-in)))))

(local (defthm fn-lbof-log-payload-append-agrees
 (implies (and (natp (fn-record-payload query)) (equal (fn-lb-log-payload query log) expected)
 (implies (equal (fn-record-payload query) (fn-record-payload row)) (equal payload expected)))
 (equal (fn-lb-log-payload query (fn-lb-log-model-append row payload target log)) expected))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-append fn-lbof-log-payload-of-cons fn-lbof-log-payload-of-atom
 fn-lbof-segment-append-row-entry fn-lbof-segment-new-entry-is-present fn-lbof-segment-new-entry-payload fn-lbof-row-entry-in-nil))))))

(local (defthm fn-lbof-log-append-keeps-other-handle
 (implies (and (natp (fn-record-payload query)) (not (equal (fn-record-payload query) (fn-record-payload row))))
 (equal (fn-lb-log-payload query (fn-lb-log-model-append row payload target log)) (fn-lb-log-payload query log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbof-log-payload-append-agrees (expected (fn-lb-log-payload query log))))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbof-intern-row-at-payload
 (equal (fn-record-payload (fn-intern-row-at w keyring generation h)) h)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-intern-row-at fn-held-make fn-record-payload fn-cbor-ag-car fn-cbor-ag-cdr))))))

(defthm fn-lb-log-model-open-preserves-older-payload
 (implies (and (natp h) (natp (fn-record-payload query)) (< (fn-record-payload query) h))
 (equal (fn-lb-log-payload query (fn-lb-log-model-open-events ws keyring generation h target log))
        (fn-lb-log-payload query log)))
 :hints (("Goal" :induct (fn-lb-log-model-open-events ws keyring generation h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-open-events fn-lbof-log-append-keeps-other-handle fn-lbof-intern-row-at-payload natp)))))

(local (defthm fn-lbof-payload-bytes-survive-seal
 (implies (and (natp h) (< h (fn-arena-count fn-arena)))
 (equal (fn-nntp-payload-bytes h (fn-arena-seal-list payload fn-arena)) (fn-nntp-payload-bytes h fn-arena)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-arena-seal-list-keeps-nth-below (xs payload)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-payload-bytes fn-arena-payload-is-nth fn-arena-count-is-len fn-arena-seal-list-len))))))

(local (defthm fn-lbof-intern-event-arena-is-wire-seal
 (equal (mv-nth 1 (fn-intern-event w keyring generation fn-arena))
 (if (fn-lb-open-wire-article w)
     (fn-arena-seal-list (fn-record-payload (fn-lb-open-wire-article w)) fn-arena) fn-arena))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-intern-event-arena))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-wire-article))))))

(local (defthm fn-lbof-intern-event-count
 (equal (fn-arena-count (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
 (+ (if (fn-lb-open-wire-article w) 1 0) (fn-arena-count fn-arena)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbof-intern-event-arena-is-wire-seal))
 :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len fn-arena-seal-list-len))))))

(local (defthm fn-lbof-intern-event-keeps-old-payload
 (implies (and (natp h) (< h (fn-arena-count fn-arena)))
 (equal (fn-nntp-payload-bytes h (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
        (fn-nntp-payload-bytes h fn-arena)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbof-intern-event-arena-is-wire-seal fn-lbof-payload-bytes-survive-seal))))))

(local (defthm fn-lbof-arena-count-natural
 (natp (fn-arena-count fn-arena))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len natp))))))

(local (defthm fn-lbof-intern-events-count-monotone
 (<= (fn-arena-count fn-arena) (fn-arena-count (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
 :in-theory (union-theories (theory 'ground-zero) '(fn-intern-events fn-lbof-intern-event-count))))))

(local (defthm fn-lbof-intern-events-keeps-old-payload
 (implies (and (natp h) (< h (fn-arena-count fn-arena)))
 (equal (fn-nntp-payload-bytes h (mv-nth 1 (fn-intern-events ws keyring generation fn-arena)))
        (fn-nntp-payload-bytes h fn-arena)))
 :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-intern-events fn-lbof-intern-event-count fn-lbof-intern-event-keeps-old-payload natp))))))

(with-prover-time-limit 30
 (def-loop fn-lb-open-next-handle (ws h)
  :shape :step :over (ws h) :done (atom ws) :skip t :body :unused
  :let ((a (fn-lb-open-wire-article (car ws))))
  :next ((cdr ws) (if a (+ 1 h) h))
  :skip-next ((cdr ws) (if a (+ 1 h) h))
  :tail h :guard (natp h)))

(local (defthm fn-lbof-next-handle-is-natural
 (implies (natp h) (natp (fn-lb-open-next-handle ws h)))
 :hints (("Goal" :induct (fn-lb-open-next-handle ws h)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-next-handle natp))))))

(local (defthm fn-lbof-next-handle-is-monotone
 (implies (natp h) (<= h (fn-lb-open-next-handle ws h)))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-lb-open-next-handle ws h)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-next-handle natp))))))

(defthm fn-lb-intern-events-count-is-open-next-handle
 (implies (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad))
 (equal (fn-arena-count (mv-nth 1 (fn-intern-events ws keyring generation fn-arena)))
        (fn-lb-open-next-handle ws (fn-arena-count fn-arena))))
 :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-intern-events fn-lb-open-next-handle fn-lbof-intern-event-count)))))

(local (defthm fn-lbof-new-entry-allocation
 (implies (and (fn-lb-log-handles-below log h) (natp h))
 (fn-lb-log-handles-below
  (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) payload target log) (+ 1 h)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-handles-below-of-append (n h) (newn (+ 1 h)) (row (fn-intern-row-at w keyring generation h))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbof-intern-row-at-payload natp))))))

(defthm fn-lb-log-model-open-preserves-handle-allocation
 (implies (and (fn-lb-log-handles-below log h) (natp h))
 (fn-lb-log-handles-below (fn-lb-log-model-open-events ws keyring generation h target log)
                        (fn-lb-open-next-handle ws h)))
 :hints (("Goal" :induct (fn-lb-log-model-open-events ws keyring generation h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-open-events fn-lb-open-next-handle fn-lbof-new-entry-allocation natp)))))

(with-prover-time-limit 30
 (def-loop fn-lb-open-held-rows (events)
  :shape :map :over events :elt r
  :keep (or (fn-cat-rowp r) (fn-sca-composite-shapep r))
  :body (if (fn-cat-rowp r) r (fn-hstxa-held r))))

(local (defthm fn-lbof-cat-row-natural-head
 (implies (fn-cat-rowp x) (natp (car x)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-rowp fn-held-shapep fn-record-uint64p fn-held-sequence fn-cbor-ag-car natp))))))

(local (defthm fn-lbof-cat-row-has-fifteen-fields
 (implies (fn-cat-rowp x) (equal (len x) 15))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-rowp fn-held-shapep))))))

(local (defthm fn-lbof-wire-control-is-no-catalog-row
 (implies (and (fn-wire-event-p x) (not (fn-record-p x)) (not (fn-stxa-p x)))
 (and (not (fn-cat-rowp x)) (not (fn-sca-composite-shapep x))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbof-cat-row-natural-head) (:instance fn-lbof-cat-row-has-fifteen-fields))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-stxe-sequence fn-stxk-sequence fn-record-uint32p fn-cp-nth fn-th-at fn-store-event-nth fn-cbor-ag-car fn-cbor-ag-cdr natp fn-wire-event-p fn-sca-composite-shapep fn-store-retention-event-p fn-stxe-p fn-stxe-shapep
 fn-stxk-p fn-stxk-shapep fn-cpe-eventp fn-th-topic-eventp fn-th-local-admin-eventp))))))

(local (defthm fn-lbof-intern-row-at-count-is-catalog-row
 (implies (and (fn-record-p w) (natp generation))
 (fn-cat-rowp (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-held-p-of-intern-list)
       (:instance fn-held-p-implies-cat-rowp (x (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-intern-list-is-row-at-count))))))

(local (defthm fn-lbof-hstxa-make-is-not-catalog-row
 (not (fn-cat-rowp (fn-hstxa-make w h)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbof-cat-row-natural-head (x (fn-hstxa-make w h))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-hstxa-make natp))))))

(local (defthm fn-lbof-composite-make-shape
 (equal (fn-sca-composite-shapep (fn-hstxa-make w h)) (fn-cat-rowp h))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-sca-composite-shapep fn-hstxa-make fn-hstxa-held fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbof-composite-make-held
 (equal (fn-hstxa-held (fn-hstxa-make w h)) h)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-hstxa-make fn-hstxa-held fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbof-record-is-consp
 (implies (fn-record-p w) (consp w))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-record-p fn-record-shapep))))))

(local (defthm fn-lbof-intern-event-held-rows
 (implies (and (natp generation)
 (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
 (equal (fn-lb-open-held-rows (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))
 (if (fn-lb-open-wire-article w)
  (list (fn-intern-row-at (fn-lb-open-wire-article w) keyring generation (fn-arena-count fn-arena))) nil)))
 :hints (("Goal" :do-not-induct t :cases ((fn-record-p w) (fn-stxa-p w))
 :use ((:instance fn-lbof-wire-control-is-no-catalog-row (x w)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-intern-event fn-lb-open-held-rows fn-lb-open-wire-article fn-cat-intern-list-is-row-at-count
 fn-lbof-intern-row-at-count-is-catalog-row fn-lbof-hstxa-make-is-not-catalog-row
 fn-lbof-composite-make-shape fn-lbof-composite-make-held fn-lbof-record-is-consp))))))

(local (defthm fn-lbof-held-rows-cons-is-singleton-append
 (equal (fn-lb-open-held-rows (cons r rs))
        (append (fn-lb-open-held-rows (list r)) (fn-lb-open-held-rows rs)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-held-rows binary-append))))))

(local (defthm fn-lbof-binding-of-append-rows
 (equal (fn-lb-arena-is-log fn-arena (append a b) log)
 (and (fn-lb-arena-is-log fn-arena a log) (fn-lb-arena-is-log fn-arena b log)))
 :hints (("Goal" :induct (append a b)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log binary-append))))))

(local (defthm fn-lbof-record-payload-octets
 (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-record-p fn-record-payloadp))))))

(local (defthm fn-lbof-payload-listp-of-append
 (implies (and (fn-arn-payload-listp a) (fn-arn-payload-listp b))
 (fn-arn-payload-listp (append a b)))
 :hints (("Goal" :induct (append a b)
 :in-theory (union-theories (theory 'ground-zero) '(fn-arn-payload-listp binary-append))))))

(local (defthm fn-lbof-arena-p-of-seal
 (implies (and (fn-arena-p fn-arena) (fn-cbor-octet-listp payload))
 (fn-arena-p (fn-arena-seal-list payload fn-arena)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-arena-p-is-payload-listp fn-arena-seal-list-is-append fn-lbof-payload-listp-of-append fn-arn-payload-listp))))))

(local (defthm fn-lbof-one-intern-preserves-arena-p
 (implies (fn-arena-p fn-arena)
 (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbof-record-payload-octets (w (fn-lb-open-wire-article w))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbof-intern-event-arena-is-wire-seal fn-lb-open-wire-article-is-record fn-lbof-arena-p-of-seal))))))

(local (defthm fn-lbof-nth-append-at-length
 (equal (nth (len a) (append a (list x))) x)
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(nth len zp binary-append))))))

(local (defthm fn-lbof-new-seal-payload
 (implies (fn-arena-p fn-arena)
 (equal (fn-nntp-payload-bytes (fn-arena-count fn-arena) (fn-arena-seal-list payload fn-arena)) payload))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-arena-seal-list-is-append (xs payload))
       (:instance fn-lbof-nth-append-at-length (a fn-arena) (x payload)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-payload-bytes fn-arena-count-is-len fn-arena-seal-list-len fn-arena-payload-is-nth))))))

(local (defthm fn-lbof-append-binds-interned-record
 (implies (and (fn-lb-log-handles-below log h) (natp h))
 (equal (fn-lb-log-payload (fn-intern-row-at w keyring generation h)
  (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) (fn-record-payload w) target log))
  (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-handles-below-gives-fresh-key (row (fn-intern-row-at w keyring generation h)) (n h))
       (:instance fn-lb-log-append-binds-fresh-row (row (fn-intern-row-at w keyring generation h)) (payload (fn-record-payload w))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbof-intern-row-at-payload natp nfix))))))

(local (defthm fn-lbof-open-tail-keeps-new-log-payload
 (implies (and (fn-lb-log-handles-below log h) (natp h))
 (equal (fn-lb-log-payload (fn-intern-row-at w keyring generation h)
  (fn-lb-log-model-open-events tail keyring generation (+ 1 h) target
   (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) (fn-record-payload w) target log)))
 (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-model-open-preserves-older-payload (ws tail) (h (+ 1 h))
         (query (fn-intern-row-at w keyring generation h))
         (log (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) (fn-record-payload w) target log)))
       (:instance fn-lbof-append-binds-interned-record))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbof-intern-row-at-payload natp))))))

(local (defthm fn-lbof-open-tail-keeps-new-arena-payload
 (implies (and (fn-arena-p fn-arena) (fn-lb-open-wire-article w))
 (equal (fn-nntp-payload-bytes (fn-arena-count fn-arena)
  (mv-nth 1 (fn-intern-events tail keyring generation (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))
 (fn-record-payload (fn-lb-open-wire-article w))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbof-intern-events-keeps-old-payload (ws tail) (h (fn-arena-count fn-arena))
         (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
       (:instance fn-lbof-new-seal-payload (payload (fn-record-payload (fn-lb-open-wire-article w)))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbof-intern-event-count fn-lbof-intern-event-arena-is-wire-seal fn-arena-count-is-len fn-arena-seal-list-len fn-lbof-arena-count-natural natp))))))

(local (defun-nx fn-lbof-open-induct (ws keyring generation target log fn-arena)
 (declare (xargs :measure (acl2-count ws) :verify-guards nil))
 (if (consp ws)
  (let* ((a (fn-lb-open-wire-article (car ws)))
         (h (fn-arena-count fn-arena))
         (log2 (if a (fn-lb-log-model-append (fn-intern-row-at a keyring generation h) (fn-record-payload a) target log) log)))
   (fn-lbof-open-induct (cdr ws) keyring generation target log2
    (mv-nth 1 (fn-intern-event (car ws) keyring generation fn-arena))))
  (list ws log fn-arena))))

(local (defthm fn-lbof-held-rows-cons-append-gated
 (implies (syntaxp (not (equal rs ''nil)))
 (equal (fn-lb-open-held-rows (cons r rs))
        (append (fn-lb-open-held-rows (list r)) (fn-lb-open-held-rows rs))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbof-held-rows-cons-is-singleton-append))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbof-empty-held-rows-by-definition
 (equal (fn-lb-open-held-rows nil) nil)
 :hints (("Goal" :in-theory '(fn-lb-open-held-rows)))))

(local (defthm fn-lbof-binding-empty-by-definition
 (fn-lb-arena-is-log fn-arena nil log)
 :hints (("Goal" :in-theory '(fn-lb-arena-is-log)))))

(local (defthm fn-lbof-binding-cons-by-definition
 (equal (fn-lb-arena-is-log fn-arena (cons r rs) log)
 (and (equal (fn-nntp-payload-bytes (fn-record-payload r) fn-arena) (fn-lb-log-payload r log))
      (fn-lb-arena-is-log fn-arena rs log)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log))))))

(local (defthm fn-lbof-intern-event-held-rows-car
 (implies (and (natp generation)
 (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
 (equal (fn-lb-open-held-rows (list (car (fn-intern-event w keyring generation fn-arena))))
 (if (fn-lb-open-wire-article w)
  (list (fn-intern-row-at (fn-lb-open-wire-article w) keyring generation (fn-arena-count fn-arena))) nil)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbof-intern-event-held-rows))
 :in-theory (union-theories (theory 'ground-zero) '(mv-nth))))))

(defthm fn-lb-log-model-open-binds-interned-rows
 (implies (and (fn-arena-p fn-arena) (natp generation)
              (fn-lb-log-handles-below log (fn-arena-count fn-arena))
              (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
 (fn-lb-arena-is-log (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))
   (fn-lb-open-held-rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))
   (fn-lb-log-model-open-events ws keyring generation (fn-arena-count fn-arena) target log)))
 :hints (("Goal" :induct (fn-lbof-open-induct ws keyring generation target log fn-arena)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbof-open-induct fn-intern-events fn-lb-log-model-open-events
 fn-lbof-empty-held-rows-by-definition fn-lbof-held-rows-cons-append-gated fn-lbof-binding-of-append-rows
 fn-lbof-intern-event-held-rows-car fn-lbof-intern-event-count fn-lbof-intern-row-at-payload
 fn-lbof-open-tail-keeps-new-log-payload fn-lbof-open-tail-keeps-new-arena-payload
 fn-lbof-one-intern-preserves-arena-p fn-lbof-new-entry-allocation
 fn-lbof-arena-count-natural fn-lbof-binding-empty-by-definition fn-lbof-binding-cons-by-definition natp)))))

(local (defthm fn-lbol-row-entry-depends-on-key
 (implies (and (equal (fn-record-sequence a) (fn-record-sequence b)) (equal (fn-record-payload a) (fn-record-payload b)))
 (equal (fn-lb-log-model-row-entry a log) (fn-lb-log-model-row-entry b log)))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry a log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-row-entry))))))

(local (defthm fn-lbol-payload-depends-on-key
 (implies (and (equal (fn-record-sequence a) (fn-record-sequence b)) (equal (fn-record-payload a) (fn-record-payload b)))
 (equal (fn-lb-log-payload a log) (fn-lb-log-payload b log)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lbol-row-entry-depends-on-key)) :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-payload))))))

(local (defthm fn-lbol-binding-of-row-append
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
 (equal (fn-nntp-payload-bytes (fn-record-payload new) fn-arena) (fn-lb-log-payload new log)))
 (fn-lb-arena-is-log fn-arena (append rows (list new)) log))
 :hints (("Goal" :induct (fn-lb-arena-is-log fn-arena rows log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log binary-append))))))

(local (defthm fn-lbol-assigned-key-fields
 (and (equal (fn-record-sequence (fn-cat-assign h rows)) (fn-record-sequence h))
      (equal (fn-record-payload (fn-cat-assign h rows)) (fn-record-payload h)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-assign fn-held-with-numbers fn-held-make fn-record-sequence fn-record-payload fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbol-catalog-commit-ready-binding
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
 (equal (fn-nntp-payload-bytes (fn-record-payload h) fn-arena) (fn-lb-log-payload h log)))
 (fn-lb-arena-is-log fn-arena (fn-cat-commit h rows) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbol-binding-of-row-append (new (fn-cat-assign h rows)))
       (:instance fn-lbol-payload-depends-on-key (a (fn-cat-assign h rows)) (b h)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-commit fn-cat$a-commit fn-lbol-assigned-key-fields))))))

(local (defthm fn-lbol-withdrawn-row-key-fields
 (and (equal (fn-record-sequence (fn-held-with-withdrawn h withdrawn)) (fn-record-sequence h))
      (equal (fn-record-payload (fn-held-with-withdrawn h withdrawn)) (fn-record-payload h)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-held-with-withdrawn fn-held-make fn-record-sequence fn-record-payload fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbol-availability-key-fields
 (and (equal (fn-record-sequence (fn-cat-prepare-row-availability h fn-arena)) (fn-record-sequence h))
      (equal (fn-record-payload (fn-cat-prepare-row-availability h fn-arena)) (fn-record-payload h)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-held-with-facts-fields (facts (fn-held-facts-of (fn-nntp-payload-bytes (fn-record-payload h) fn-arena)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-prepare-row-availability))))))

(local (defthm fn-lbol-commit-same-key
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
              (fn-lb-arena-is-log fn-arena (list old) log)
              (equal (fn-record-sequence new) (fn-record-sequence old))
              (equal (fn-record-payload new) (fn-record-payload old)))
 (fn-lb-arena-is-log fn-arena (fn-cat-commit new rows) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbol-payload-depends-on-key (a new) (b old))
       (:instance fn-lbol-catalog-commit-ready-binding (h new)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log))))))

(local (defthm fn-lbol-with-facts-is-catalog-row
 (implies (and (fn-cat-rowp h) (fn-hf-p facts))
 (fn-cat-rowp (fn-held-with-facts h facts)))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-cat-rowp fn-held-with-facts) (fn-hf-p fn-cat-ctxp fn-held-facts-of))))))

(local (defthm fn-lbol-availability-keeps-catalog-row
 (implies (fn-cat-rowp h) (fn-cat-rowp (fn-cat-prepare-row-availability h fn-arena)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-prepare-row-availability fn-lbol-with-facts-is-catalog-row fn-hf-p-of-held-facts-of))))))

(local (defthm fn-lbof-load-one-preserves-binding
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
              (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows (list r)) log))
 (fn-lb-arena-is-log fn-arena (fn-sca-load-held-available-row r view-index fn-arena rows) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbol-commit-same-key (old r) (new (fn-cat-prepare-row-availability r fn-arena)))
(:instance fn-lbol-commit-same-key (old r) (new (fn-held-with-withdrawn (fn-cat-prepare-row-availability r fn-arena) (cons (fn-cat-count rows) 0))))
(:instance fn-lbol-commit-same-key (old (fn-hstxa-held r)) (new (fn-cat-prepare-row-availability (fn-hstxa-held r) fn-arena)))
(:instance fn-lbol-commit-same-key (old (fn-hstxa-held r)) (new (fn-held-with-withdrawn (fn-cat-prepare-row-availability (fn-hstxa-held r) fn-arena) (cons (fn-cat-count rows) 0)))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-sca-load-held-available-row fn-sca-load-held-row fn-lb-open-held-rows fn-sca-composite-shapep fn-lbol-availability-keeps-catalog-row
 fn-lbof-binding-cons-by-definition fn-lbof-binding-empty-by-definition
 fn-lbol-availability-key-fields fn-lbol-withdrawn-row-key-fields))))))

(defthm fn-lb-arena-is-log-of-availability-load-from
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
              (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows events) log))
 (fn-lb-arena-is-log fn-arena (fn-sca-load-held-available-from events view-index fn-arena rows) log))
 :hints (("Goal" :induct (fn-sca-load-held-available-from events view-index fn-arena rows)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-sca-load-held-available-from fn-lbof-held-rows-cons-append-gated fn-lbof-binding-of-append-rows
 fn-lbof-load-one-preserves-binding)))))

(defthm fn-lb-arena-is-log-of-availability-load
 (implies (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows events) log)
 (fn-lb-arena-is-log fn-arena (fn-sca-load-held-rows events view-index fn-arena rows) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-arena-is-log-of-availability-load-from (rows nil)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-sca-load-held-rows fn-cat-clear fn-cat$a-clear fn-lbof-binding-empty-by-definition)))))

(local (defthm fn-lbof-empty-log-allocation-by-definition
 (fn-lb-log-handles-below nil n)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-handles-below))))))

(local (defthm fn-lbof-load-refused-rows-by-definition
 (equal (fn-sca-load-held-rows :bad view-index fn-arena fn-cat) nil)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-sca-load-held-rows fn-sca-load-held-available-from fn-cat-clear fn-cat$a-clear))))))

(defthm fn-lb-arena-is-log-of-open-rebuild
 (let* ((arena0 (fn-arena-clear fn-arena))
        (events (mv-nth 0 (fn-intern-events ws nil 0 arena0)))
        (arena (mv-nth 1 (fn-intern-events ws nil 0 arena0)))
        (log (fn-lb-log-model-open-events ws nil 0 0 target nil)))
 (fn-lb-arena-is-log arena (fn-sca-load-held-rows events view-index arena fn-cat) log))
 :hints (("Goal" :do-not-induct t
 :cases ((equal (mv-nth 0 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena))) :bad))
 :use ((:instance fn-lb-log-model-open-binds-interned-rows (keyring nil) (generation 0)
         (log nil) (fn-arena (fn-arena-clear fn-arena)))
       (:instance fn-lb-arena-is-log-of-availability-load
         (events (mv-nth 0 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena))))
         (fn-arena (mv-nth 1 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena))))
         (rows fn-cat) (log (fn-lb-log-model-open-events ws nil 0 0 target nil))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-arena-clear-is-nil fn-arena-count-is-len fn-arena-p-is-payload-listp fn-arn-payload-listp
 fn-lbof-empty-log-allocation-by-definition fn-lbof-binding-empty-by-definition fn-lbof-load-refused-rows-by-definition)))))
