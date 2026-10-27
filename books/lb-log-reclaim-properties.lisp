; Arena/log binding across the actual reclaim rewrite, prediction, deferred
; seal and catalog candidate load. The candidate loader may use the OLD
; arena, as native reclaim does before its under-mutex swap.
(in-package "ACL2")
(include-book "lb-log-reclaim-model")
(include-book "lb-log-open-properties")

(with-prover-time-limit 60 (def-loop fn-lb-reclaim-next-handle (rows h)
  :shape :step :over (rows h) :done (atom rows) :skip t :body :unused
  :next ((cdr rows) (if (fn-record-p (car rows)) (+ 1 h) h))
  :skip-next ((cdr rows) (if (fn-record-p (car rows)) (+ 1 h) h))
  :tail h :guard (natp h)))

(local (defthm fn-lbr-record-is-consp
 (implies (fn-record-p w) (consp w))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-record-p fn-record-shapep))))))

(local (defthm fn-lbr-single-record-next-handle
 (implies (fn-record-p w) (equal (fn-lb-open-next-handle (list w) h) (+ 1 h)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-open-next-handle fn-lb-open-wire-article fn-lbr-record-is-consp))))))

(local (defthm fn-lbr-append-preserves-older-payload
 (implies (and (fn-record-p w) (natp h) (natp (fn-record-payload query)) (< (fn-record-payload query) h))
 (equal (fn-lb-log-payload query
  (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) (fn-record-payload w) target log))
 (fn-lb-log-payload query log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-model-open-preserves-older-payload (ws (list w))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-open-events fn-lb-open-wire-article fn-lbr-record-is-consp))))))

(defthm fn-lb-log-model-reclaim-preserves-older-payload
 (implies (and (natp h) (natp (fn-record-payload query)) (< (fn-record-payload query) h))
 (equal (fn-lb-log-payload query (fn-lb-log-model-reclaim-events rows id h target log))
        (fn-lb-log-payload query log)))
 :hints (("Goal" :induct (fn-lb-log-model-reclaim-events rows id h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-reclaim-events fn-lbr-append-preserves-older-payload natp)))))

(local (defthm fn-lbr-append-preserves-allocation
 (implies (and (fn-record-p w) (natp h) (fn-lb-log-handles-below log h))
 (fn-lb-log-handles-below
  (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) (fn-record-payload w) target log) (+ 1 h)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-model-open-preserves-handle-allocation (ws (list w))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-open-events fn-lb-open-wire-article fn-lbr-single-record-next-handle fn-lbr-record-is-consp))))))

(defthm fn-lb-log-model-reclaim-preserves-handle-allocation
 (implies (and (fn-lb-log-handles-below log h) (natp h))
 (fn-lb-log-handles-below (fn-lb-log-model-reclaim-events rows id h target log)
                        (fn-lb-reclaim-next-handle rows h)))
 :hints (("Goal" :induct (fn-lb-log-model-reclaim-events rows id h target log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-reclaim-events fn-lb-reclaim-next-handle fn-lbr-append-preserves-allocation natp)))))

(local (defthm fn-lbr-intern-row-at-payload
 (equal (fn-record-payload (fn-intern-row-at w keyring generation h)) h)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-intern-row-at fn-held-make fn-record-payload fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbr-payload-bytes-survive-seal
 (implies (and (natp h) (< h (fn-arena-count fn-arena)))
 (equal (fn-nntp-payload-bytes h (fn-arena-seal-list payload fn-arena)) (fn-nntp-payload-bytes h fn-arena)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-arena-seal-list-keeps-nth-below (xs payload)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-payload-bytes fn-arena-payload-is-nth fn-arena-count-is-len fn-arena-seal-list-len))))))

(local (defthm fn-lbr-arena-count-natural
 (natp (fn-arena-count fn-arena))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len natp))))))

(local (defthm fn-lbr-cat-row-natural-head
 (implies (fn-cat-rowp x) (natp (car x)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-rowp fn-held-shapep fn-record-uint64p fn-held-sequence fn-cbor-ag-car natp))))))

(local (defthm fn-lbr-cat-row-has-fifteen-fields
 (implies (fn-cat-rowp x) (equal (len x) 15))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-rowp fn-held-shapep))))))

(local (defthm fn-lbr-intern-row-at-count-is-catalog-row
 (implies (and (fn-record-p w) (natp generation))
 (fn-cat-rowp (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-held-p-of-intern-list)
       (:instance fn-held-p-implies-cat-rowp (x (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-intern-list-is-row-at-count))))))

(local (defthm fn-lbr-held-rows-cons-is-singleton-append
 (equal (fn-lb-open-held-rows (cons r rs))
        (append (fn-lb-open-held-rows (list r)) (fn-lb-open-held-rows rs)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-held-rows binary-append))))))

(local (defthm fn-lbr-binding-of-append-rows
 (equal (fn-lb-arena-is-log fn-arena (append a b) log)
 (and (fn-lb-arena-is-log fn-arena a log) (fn-lb-arena-is-log fn-arena b log)))
 :hints (("Goal" :induct (append a b)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log binary-append))))))

(local (defthm fn-lbr-record-payload-octets
 (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-record-p fn-record-payloadp))))))

(local (defthm fn-lbr-payload-listp-of-append
 (implies (and (fn-arn-payload-listp a) (fn-arn-payload-listp b))
 (fn-arn-payload-listp (append a b)))
 :hints (("Goal" :induct (append a b)
 :in-theory (union-theories (theory 'ground-zero) '(fn-arn-payload-listp binary-append))))))

(local (defthm fn-lbr-arena-p-of-seal
 (implies (and (fn-arena-p fn-arena) (fn-cbor-octet-listp payload))
 (fn-arena-p (fn-arena-seal-list payload fn-arena)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-arena-p-is-payload-listp fn-arena-seal-list-is-append fn-lbr-payload-listp-of-append fn-arn-payload-listp))))))

(local (defthm fn-lbr-nth-append-at-length
 (equal (nth (len a) (append a (list x))) x)
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(nth len zp binary-append))))))

(local (defthm fn-lbr-new-seal-payload
 (equal (fn-nntp-payload-bytes (fn-arena-count fn-arena) (fn-arena-seal-list payload fn-arena)) payload)
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-arena-seal-new-handle (xs payload)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-nntp-payload-bytes fn-arena-count-is-len fn-arena-seal-count))))))

(local (defthm fn-lbr-append-binds-interned-record
 (implies (and (fn-lb-log-handles-below log h) (natp h))
 (equal (fn-lb-log-payload (fn-intern-row-at w keyring generation h)
  (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) (fn-record-payload w) target log))
  (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-handles-below-gives-fresh-key (row (fn-intern-row-at w keyring generation h)) (n h))
       (:instance fn-lb-log-append-binds-fresh-row (row (fn-intern-row-at w keyring generation h)) (payload (fn-record-payload w))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr-intern-row-at-payload natp nfix))))))

(local (defthm fn-lbr-binding-empty-by-definition
 (fn-lb-arena-is-log fn-arena nil log)
 :hints (("Goal" :in-theory '(fn-lb-arena-is-log)))))

(local (defthm fn-lbr-binding-cons-by-definition
 (equal (fn-lb-arena-is-log fn-arena (cons r rs) log)
 (and (equal (fn-nntp-payload-bytes (fn-record-payload r) fn-arena) (fn-lb-log-payload r log))
      (fn-lb-arena-is-log fn-arena rs log)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log))))))

(local (defun-nx fn-lbr-seal-induct (rows fn-arena)
 (declare (xargs :measure (acl2-count rows) :verify-guards nil))
 (if (consp rows)
  (fn-lbr-seal-induct (cdr rows)
   (if (fn-record-p (car rows)) (fn-arena-seal-list (fn-record-payload (car rows)) fn-arena) fn-arena))
  fn-arena)))

(local (defthm fn-lbr-seed-generation-is-natural
 (natp (fn-ssr-at 2 (fn-ssr-seed id)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-ssr-seed-establishes-statep (identity id)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-ssr-statep))))))

(local (defthm fn-lbr-seal-count
 (equal (fn-arena-count (fn-arena-seal-list payload fn-arena)) (+ 1 (fn-arena-count fn-arena)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-arena-count-is-len fn-arena-seal-list-len))))))

(local (defthm fn-lbr-orcs-count
 (equal (fn-arena-count (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))
        (fn-lb-reclaim-next-handle rows (fn-arena-count fn-arena)))
 :hints (("Goal" :induct (fn-lbr-seal-induct rows fn-arena)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr-seal-induct fn-orcs-seal fn-orcs-payloads fn-lb-reclaim-next-handle fn-lbr-record-payload-octets fn-lbr-seal-count))))))

(local (defthm fn-lbr-orcs-keeps-old-payload
 (implies (and (natp h) (< h (fn-arena-count fn-arena)))
 (equal (fn-nntp-payload-bytes h (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))
        (fn-nntp-payload-bytes h fn-arena)))
 :hints (("Goal" :induct (fn-lbr-seal-induct rows fn-arena)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr-seal-induct fn-orcs-seal fn-orcs-payloads fn-lbr-record-payload-octets fn-lbr-payload-bytes-survive-seal fn-lbr-seal-count natp))))))

(local (defthm fn-lbr-orcs-arena-p
 (implies (fn-arena-p fn-arena)
 (fn-arena-p (fn-orcs-seal (fn-orcs-payloads rows) fn-arena)))
 :hints (("Goal" :induct (fn-lbr-seal-induct rows fn-arena)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr-seal-induct fn-orcs-seal fn-orcs-payloads fn-lbr-record-payload-octets fn-lbr-arena-p-of-seal))))))

(local (defthm fn-lbr-handles-below-monotone
 (implies (and (fn-scol-handles-below rows n) (<= (nfix n) (nfix newn)))
 (fn-scol-handles-below rows newn))
 :hints (("Goal" :induct (fn-scol-handles-below rows n)
 :in-theory (union-theories (theory 'ground-zero) '(fn-scol-handles-below))))))

(local (defthm fn-lbr-one-append-frames-kept-binding
 (implies (and (fn-record-p w) (fn-lb-arena-is-log fn-arena kept log)
              (fn-scol-handles-below kept (fn-arena-count fn-arena)))
 (fn-lb-arena-is-log (fn-arena-seal-list (fn-record-payload w) fn-arena) kept
  (fn-lb-log-model-append (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))
   (fn-record-payload w) target log)))
 :hints (("Goal" :induct (fn-lb-arena-is-log fn-arena kept log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-arena-is-log fn-scol-handles-below fn-lbr-payload-bytes-survive-seal
   fn-lbr-append-preserves-older-payload fn-lbr-arena-count-natural nfix))))))

(local (defthm fn-lbr-reclaim-frames-kept-binding
 (implies (and (fn-lb-arena-is-log fn-arena kept log)
              (fn-scol-handles-below kept (fn-arena-count fn-arena)))
 (fn-lb-arena-is-log
  (fn-orcs-seal (fn-orcs-payloads rows) fn-arena) kept
  (fn-lb-log-model-reclaim-events rows id (fn-arena-count fn-arena) target log)))
 :hints (("Goal" :induct (fn-lb-arena-is-log fn-arena kept log)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-arena-is-log fn-scol-handles-below fn-lbr-orcs-keeps-old-payload
 fn-lb-log-model-reclaim-preserves-older-payload fn-lbr-arena-count-natural nfix))))))

(local (defthm fn-lbr-reclaim-tail-keeps-new-log-payload
 (implies (and (fn-lb-log-handles-below log h) (natp h))
 (equal (fn-lb-log-payload (fn-intern-row-at w keyring generation h)
  (fn-lb-log-model-reclaim-events tail id (+ 1 h) target
   (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) (fn-record-payload w) target log)))
 (fn-record-payload w)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-model-reclaim-preserves-older-payload (rows tail) (h (+ 1 h))
         (query (fn-intern-row-at w keyring generation h))
         (log (fn-lb-log-model-append (fn-intern-row-at w keyring generation h) (fn-record-payload w) target log)))
       (:instance fn-lbr-append-binds-interned-record))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr-intern-row-at-payload natp))))))

(local (defthm fn-lbr-reclaim-tail-keeps-new-arena-payload
 (equal (fn-nntp-payload-bytes (fn-arena-count fn-arena)
  (fn-orcs-seal (fn-orcs-payloads tail) (fn-arena-seal-list payload fn-arena)))
 payload)
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr-orcs-keeps-old-payload (rows tail) (h (fn-arena-count fn-arena))
         (fn-arena (fn-arena-seal-list payload fn-arena)))
       (:instance fn-lbr-new-seal-payload))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr-seal-count fn-lbr-arena-count-natural natp))))))

(local (defthm fn-lbr-held-rows-cons-append-gated
 (implies (syntaxp (not (equal rs ''nil)))
 (equal (fn-lb-open-held-rows (cons r rs))
        (append (fn-lb-open-held-rows (list r)) (fn-lb-open-held-rows rs))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr-held-rows-cons-is-singleton-append))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbr-handles-below-append
 (equal (fn-scol-handles-below (append a b) n)
 (and (fn-scol-handles-below a n) (fn-scol-handles-below b n)))
 :hints (("Goal" :induct (append a b)
 :in-theory (union-theories (theory 'ground-zero) '(fn-scol-handles-below binary-append))))))

(local (defthm fn-lbr-wire-record-has-eleven-fields
 (implies (fn-record-p w) (equal (len w) 11))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-record-p fn-record-shapep))))))

(local (defthm fn-lbr-wire-record-is-not-held
 (implies (fn-record-p w) (not (fn-cat-rowp w)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr-cat-row-has-fifteen-fields (x w)) (:instance fn-lbr-wire-record-has-eleven-fields))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbr-wire-record-is-not-composite
 (implies (fn-record-p w) (not (fn-sca-composite-shapep w)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-record-p fn-record-shapep fn-record-uint64p fn-record-sequence fn-cbor-ag-car fn-cbor-ag-cdr fn-sca-composite-shapep natp))))))

(local (defthm fn-lbr-wire-record-has-no-kept-row
 (implies (fn-record-p w) (equal (fn-lb-open-held-rows (list w)) nil))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-open-held-rows fn-lbr-wire-record-is-not-held fn-lbr-wire-record-is-not-composite))))))

(local (defthm fn-lbr-new-predicted-held-row
 (implies (and (fn-record-p w) (natp generation))
 (equal (fn-lb-open-held-rows (list (fn-intern-row-at w keyring generation (fn-arena-count fn-arena))))
        (list (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-open-held-rows fn-lbr-intern-row-at-count-is-catalog-row))))))

(local (defun-nx fn-lbr-reclaim-induct (rows id target log fn-arena)
 (declare (xargs :measure (acl2-count rows) :verify-guards nil))
 (if (consp rows)
  (let* ((w (car rows)) (seed (fn-ssr-seed id))
    (row (if (fn-record-p w) (fn-intern-row-at w (fn-ssr-at 1 seed) (fn-ssr-at 2 seed) (fn-arena-count fn-arena)) w)))
   (fn-lbr-reclaim-induct (cdr rows) (fn-replay-identity-loop (list row) id) target
    (if (fn-record-p w) (fn-lb-log-model-append row (fn-record-payload w) target log) log)
    (if (fn-record-p w) (fn-arena-seal-list (fn-record-payload w) fn-arena) fn-arena)))
  (list rows log fn-arena))))

(local (defthm fn-lbr-kept-handles-after-seal
 (implies (fn-scol-handles-below kept (fn-arena-count fn-arena))
 (fn-scol-handles-below kept (fn-arena-count (fn-arena-seal-list payload fn-arena))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr-handles-below-monotone
  (rows kept) (n (fn-arena-count fn-arena)) (newn (+ 1 (fn-arena-count fn-arena)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbr-seal-count fn-lbr-arena-count-natural nfix natp))))))

(local (defthm fn-lbr-empty-kept-rows
 (implies (atom rows) (equal (fn-lb-open-held-rows rows) nil))
 :hints (("Goal" :in-theory '(fn-lb-open-held-rows)))))

(local (defthm fn-lbr-input-binding-tail
 (implies (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows rows) log)
 (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows (cdr rows)) log))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-held-rows fn-lb-arena-is-log))))))

(local (defthm fn-lbr-input-handles-tail
 (implies (fn-scol-handles-below (fn-lb-open-held-rows rows) h)
 (fn-scol-handles-below (fn-lb-open-held-rows (cdr rows)) h))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-held-rows fn-scol-handles-below))))))

(local (defthm fn-lbr-input-binding-head
 (implies (and (consp rows) (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows rows) log))
 (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows (list (car rows))) log))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-held-rows fn-lb-arena-is-log))))))

(local (defthm fn-lbr-input-handles-head
 (implies (and (consp rows) (fn-scol-handles-below (fn-lb-open-held-rows rows) h))
 (fn-scol-handles-below (fn-lb-open-held-rows (list (car rows))) h))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-open-held-rows fn-scol-handles-below))))))

(local (defthm fn-lbr-handles-below-increment
 (implies (and (natp h) (fn-scol-handles-below kept h))
 (fn-scol-handles-below kept (+ 1 h)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr-handles-below-monotone (rows kept) (n h) (newn (+ 1 h))))
 :in-theory (union-theories (theory 'ground-zero) '(natp nfix))))))

(defthm fn-lb-log-model-reclaim-binds-predicted-rows
 (implies
  (and (fn-lb-log-handles-below log (fn-arena-count fn-arena)) (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows rows) log) (fn-scol-handles-below (fn-lb-open-held-rows rows) (fn-arena-count fn-arena)))
 (fn-lb-arena-is-log
  (fn-orcs-seal (fn-orcs-payloads rows) fn-arena)
  (fn-lb-open-held-rows (fn-orcs-predict-rows-at rows id (fn-arena-count fn-arena)))
  (fn-lb-log-model-reclaim-events rows id (fn-arena-count fn-arena) target log)))
 :hints (("Goal" :induct (fn-lbr-reclaim-induct rows id target log fn-arena) :do-not '(generalize eliminate-destructors)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbr-reclaim-induct fn-orcs-seal fn-orcs-payloads fn-orcs-predict-rows-at
 fn-lb-log-model-reclaim-events fn-lbr-held-rows-cons-append-gated
 fn-lbr-binding-of-append-rows
 fn-lbr-handles-below-append fn-lbr-wire-record-has-no-kept-row
 fn-lbr-new-predicted-held-row fn-lbr-seed-generation-is-natural
 fn-lbr-one-append-frames-kept-binding fn-lbr-kept-handles-after-seal fn-lbr-reclaim-frames-kept-binding
 fn-lbr-reclaim-tail-keeps-new-log-payload fn-lbr-reclaim-tail-keeps-new-arena-payload
 fn-lbr-intern-row-at-payload fn-lbr-record-payload-octets
 fn-lbr-arena-p-of-seal fn-lbr-append-preserves-allocation fn-lbr-seal-count
 fn-lbr-arena-count-natural fn-lbr-binding-empty-by-definition fn-lbr-binding-cons-by-definition
 fn-lbr-empty-kept-rows fn-lbr-input-binding-tail fn-lbr-input-binding-head fn-lbr-input-handles-tail fn-lbr-input-handles-head fn-lbr-handles-below-increment natp)))))

(local (defthm fn-lbrl-row-entry-depends-on-key
 (implies (and (equal (fn-record-sequence a) (fn-record-sequence b)) (equal (fn-record-payload a) (fn-record-payload b)))
 (equal (fn-lb-log-model-row-entry a log) (fn-lb-log-model-row-entry b log)))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry a log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-row-entry))))))

(local (defthm fn-lbrl-payload-depends-on-key
 (implies (and (equal (fn-record-sequence a) (fn-record-sequence b)) (equal (fn-record-payload a) (fn-record-payload b)))
 (equal (fn-lb-log-payload a log) (fn-lb-log-payload b log)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lbrl-row-entry-depends-on-key)) :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-payload))))))

(local (defthm fn-lbrl-binding-of-row-append
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
 (equal (fn-nntp-payload-bytes (fn-record-payload new) fn-arena) (fn-lb-log-payload new log)))
 (fn-lb-arena-is-log fn-arena (append rows (list new)) log))
 :hints (("Goal" :induct (fn-lb-arena-is-log fn-arena rows log)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log binary-append))))))

(local (defthm fn-lbrl-assigned-key-fields
 (and (equal (fn-record-sequence (fn-cat-assign h rows)) (fn-record-sequence h))
      (equal (fn-record-payload (fn-cat-assign h rows)) (fn-record-payload h)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-assign fn-held-with-numbers fn-held-make fn-record-sequence fn-record-payload fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbrl-catalog-commit-ready-binding
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
 (equal (fn-nntp-payload-bytes (fn-record-payload h) fn-arena) (fn-lb-log-payload h log)))
 (fn-lb-arena-is-log fn-arena (fn-cat-commit h rows) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbrl-binding-of-row-append (new (fn-cat-assign h rows)))
       (:instance fn-lbrl-payload-depends-on-key (a (fn-cat-assign h rows)) (b h)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-commit fn-cat$a-commit fn-lbrl-assigned-key-fields))))))

(local (defthm fn-lbrl-withdrawn-row-key-fields
 (and (equal (fn-record-sequence (fn-held-with-withdrawn h withdrawn)) (fn-record-sequence h))
      (equal (fn-record-payload (fn-held-with-withdrawn h withdrawn)) (fn-record-payload h)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-held-with-withdrawn fn-held-make fn-record-sequence fn-record-payload fn-cbor-ag-car fn-cbor-ag-cdr))))))

(local (defthm fn-lbrl-availability-key-fields
 (and (equal (fn-record-sequence (fn-cat-prepare-row-availability h fn-arena)) (fn-record-sequence h))
      (equal (fn-record-payload (fn-cat-prepare-row-availability h fn-arena)) (fn-record-payload h)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-held-with-facts-fields (facts (fn-held-facts-of (fn-nntp-payload-bytes (fn-record-payload h) fn-arena)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-prepare-row-availability))))))

(local (defthm fn-lbrl-commit-same-key
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
              (fn-lb-arena-is-log fn-arena (list old) log)
              (equal (fn-record-sequence new) (fn-record-sequence old))
              (equal (fn-record-payload new) (fn-record-payload old)))
 (fn-lb-arena-is-log fn-arena (fn-cat-commit new rows) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbrl-payload-depends-on-key (a new) (b old))
       (:instance fn-lbrl-catalog-commit-ready-binding (h new)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-arena-is-log))))))

(local (defthm fn-lbrl-with-facts-is-catalog-row
 (implies (and (fn-cat-rowp h) (fn-hf-p facts))
 (fn-cat-rowp (fn-held-with-facts h facts)))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-cat-rowp fn-held-with-facts) (fn-hf-p fn-cat-ctxp fn-held-facts-of))))))

(local (defthm fn-lbrl-availability-keeps-catalog-row
 (implies (fn-cat-rowp h) (fn-cat-rowp (fn-cat-prepare-row-availability h fn-arena)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-prepare-row-availability fn-lbrl-with-facts-is-catalog-row fn-hf-p-of-held-facts-of))))))

(local (defthm fn-lbr-load-one-preserves-binding
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
              (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows (list r)) log))
 (fn-lb-arena-is-log fn-arena (fn-sca-load-held-available-row r view-index loader-arena rows) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbrl-commit-same-key (old r) (new (fn-cat-prepare-row-availability r loader-arena)))
(:instance fn-lbrl-commit-same-key (old r) (new (fn-held-with-withdrawn (fn-cat-prepare-row-availability r loader-arena) (cons (fn-cat-count rows) 0))))
(:instance fn-lbrl-commit-same-key (old (fn-hstxa-held r)) (new (fn-cat-prepare-row-availability (fn-hstxa-held r) loader-arena)))
(:instance fn-lbrl-commit-same-key (old (fn-hstxa-held r)) (new (fn-held-with-withdrawn (fn-cat-prepare-row-availability (fn-hstxa-held r) loader-arena) (cons (fn-cat-count rows) 0)))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-sca-load-held-available-row fn-sca-load-held-row fn-lb-open-held-rows fn-sca-composite-shapep fn-lbrl-availability-keeps-catalog-row
 fn-lbr-binding-cons-by-definition fn-lbr-binding-empty-by-definition
 fn-lbrl-availability-key-fields fn-lbrl-withdrawn-row-key-fields))))))

(defthm fn-lb-arena-is-log-of-independent-availability-load-from
 (implies (and (fn-lb-arena-is-log fn-arena rows log)
              (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows events) log))
 (fn-lb-arena-is-log fn-arena (fn-sca-load-held-available-from events view-index loader-arena rows) log))
 :hints (("Goal" :induct (fn-sca-load-held-available-from events view-index loader-arena rows)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-sca-load-held-available-from fn-lbr-held-rows-cons-append-gated fn-lbr-binding-of-append-rows
 fn-lbr-load-one-preserves-binding)))))

(defthm fn-lb-arena-is-log-of-independent-availability-load
 (implies (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows events) log)
 (fn-lb-arena-is-log fn-arena (fn-sca-load-held-rows events view-index loader-arena rows) log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-arena-is-log-of-independent-availability-load-from (rows nil)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-sca-load-held-rows fn-cat-clear fn-cat$a-clear fn-lbr-binding-empty-by-definition)))))

; No-bad is redundant: refusal loads no rows; keep the actual non-refusal proof local.
(local (defthm fn-lbr-non-refusal-reclaim-binding
 (implies
  (and (fn-lb-log-handles-below log (fn-arena-count fn-arena)) (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows rows) log) (fn-scol-handles-below (fn-lb-open-held-rows rows) (fn-arena-count fn-arena)) (not (fn-orcs-has-bad rows)))
 (let* ((base (fn-arena-count fn-arena))
        (prediction (fn-orcs-predict rows id base))
        (post-arena (fn-orcs-seal (cadr prediction) fn-arena))
        (post-log (fn-lb-log-model-reclaim-events rows id base target log)))
  (fn-lb-arena-is-log post-arena
   (fn-sca-load-held-rows (car prediction) view-index fn-arena fn-cat)
   post-log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-model-reclaim-binds-predicted-rows)
       (:instance fn-lb-arena-is-log-of-independent-availability-load
        (events (fn-orcs-predict-rows-at rows id (fn-arena-count fn-arena)))
        (fn-arena (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))
        (loader-arena fn-arena) (rows fn-cat)
        (log (fn-lb-log-model-reclaim-events rows id (fn-arena-count fn-arena) target log))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-orcs-predict))))))

(defthm fn-lb-arena-is-log-of-reclaim
 (implies (and (fn-lb-log-handles-below log (fn-arena-count fn-arena)) (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows rows) log) (fn-scol-handles-below (fn-lb-open-held-rows rows) (fn-arena-count fn-arena)))
 (let* ((base (fn-arena-count fn-arena))
        (prediction (fn-orcs-predict rows id base))
        (post-arena (fn-orcs-seal (cadr prediction) fn-arena))
        (post-log (fn-lb-log-model-reclaim-events rows id base target log)))
  (fn-lb-arena-is-log post-arena
   (fn-sca-load-held-rows (car prediction) view-index fn-arena fn-cat)
   post-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :cases ((fn-orcs-has-bad rows))
 :use ((:instance fn-lbr-non-refusal-reclaim-binding))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-orcs-predict fn-sca-load-held-rows fn-sca-load-held-available-from
 fn-cat-clear fn-cat$a-clear fn-lb-arena-is-log)))))

(local (defthm fn-lbr-rewrite-makes-a-wire-record
 (implies (fn-rclp-rewrites-p octets ctx)
 (fn-record-p (fn-rclp-tombstoned (fn-record-result-record (fn-record-decode-exact octets)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-rclp-rewrites-p))))))

(local (defthm fn-lbr-rewrite-kept-row-projection
 (equal (fn-lb-open-held-rows (list (fn-orc-rewrite-row row ctx fn-arena)))
        (if (fn-rclp-rewrites-p (fn-orc-row-octets row fn-arena) ctx)
         nil (fn-lb-open-held-rows (list row))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr-rewrite-makes-a-wire-record (octets (fn-orc-row-octets row fn-arena))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-orc-rewrite-row fn-lbr-wire-record-has-no-kept-row))))))

(defthm fn-lb-reclaim-rewrite-preserves-kept-binding
 (implies (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows rows) log)
 (fn-lb-arena-is-log fn-arena
  (fn-lb-open-held-rows (fn-orc-rewrite-rows rows ctx fn-arena)) log))
 :hints (("Goal" :induct (fn-orc-rewrite-rows rows ctx fn-arena)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-orc-rewrite-rows fn-lbr-rewrite-kept-row-projection fn-lbr-held-rows-cons-append-gated
 fn-lbr-binding-of-append-rows fn-lbr-binding-empty-by-definition fn-lbr-empty-kept-rows)))))

(defthm fn-lb-reclaim-rewrite-preserves-kept-handles
 (implies (fn-scol-handles-below (fn-lb-open-held-rows rows) n)
 (fn-scol-handles-below
  (fn-lb-open-held-rows (fn-orc-rewrite-rows rows ctx fn-arena)) n))
 :hints (("Goal" :induct (fn-orc-rewrite-rows rows ctx fn-arena)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-orc-rewrite-rows fn-lbr-rewrite-kept-row-projection fn-lbr-held-rows-cons-append-gated
 fn-lbr-handles-below-append fn-scol-handles-below fn-lbr-empty-kept-rows)))))

(local (defthm fn-lbr-rewrite-does-not-create-bad
 (implies (not (equal row :bad))
 (not (equal (fn-orc-rewrite-row row ctx fn-arena) :bad)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr-rewrite-makes-a-wire-record (octets (fn-orc-row-octets row fn-arena)))
       (:instance fn-lbr-record-is-consp
        (w (fn-rclp-tombstoned (fn-record-result-record (fn-record-decode-exact (fn-orc-row-octets row fn-arena)))))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-orc-rewrite-row))))))

(local (defthm fn-lbr-rewrite-preserves-no-bad
 (implies (not (fn-orcs-has-bad rows))
 (not (fn-orcs-has-bad (fn-orc-rewrite-rows rows ctx fn-arena))))
 :hints (("Goal" :induct (fn-orc-rewrite-rows rows ctx fn-arena)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-orc-rewrite-rows fn-orcs-has-bad fn-lbr-rewrite-does-not-create-bad))))))

(defthm fn-lb-arena-is-log-of-reclaim-after-rewrite
 (implies
  (and (fn-lb-log-handles-below log (fn-arena-count fn-arena)) (fn-lb-arena-is-log fn-arena (fn-lb-open-held-rows rows) log) (fn-scol-handles-below (fn-lb-open-held-rows rows) (fn-arena-count fn-arena)) (not (fn-orcs-has-bad rows)))
 (let* ((mixed (fn-orc-rewrite-rows rows ctx fn-arena))
        (base (fn-arena-count fn-arena))
        (prediction (fn-orcs-predict mixed id base))
        (post-arena (fn-orcs-seal (cadr prediction) fn-arena))
        (post-log (fn-lb-log-model-reclaim-events mixed id base target log)))
  (fn-lb-arena-is-log post-arena
   (fn-sca-load-held-rows (car prediction) view-index fn-arena fn-cat)
   post-log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-arena-is-log-of-reclaim (rows (fn-orc-rewrite-rows rows ctx fn-arena)))
       (:instance fn-lb-reclaim-rewrite-preserves-kept-binding)
       (:instance fn-lb-reclaim-rewrite-preserves-kept-handles (n (fn-arena-count fn-arena)))
       (:instance fn-lbr-rewrite-preserves-no-bad))
 :in-theory (theory 'ground-zero))))
