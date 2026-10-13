; Guard discharge for the LB foundation.
; Guard signatures, recognizers, findings and residual goals: build/lb/GUARDS.md.
; Proof cuts and arithmetic are local; LC invariant lemmas are exported.
(in-package "ACL2")
(include-book "lb-log-model")
(include-book "catalog-columns")
(include-book "log-verified-map")
(include-book "log-locator-resolves")

(local
  (defthm
    fn-lbg-character-octets
    (implies (character-listp chars) (fn-cbor-octet-listp (fn-record-string-octets-aux chars)))
    :hints
    (("Goal"
       :induct
       (fn-record-string-octets-aux chars)
       :in-theory
       (enable fn-record-string-octets-aux fn-cbor-octet-listp fn-cbor-octetp)))))

(local
  (defthm
    fn-lbg-string-octets
    (fn-cbor-octet-listp (fn-record-string-octets text))
    :hints
    (("Goal" :in-theory (enable fn-record-string-octets)))))

(local
  (defthm
    fn-lbg-beta-reduction-unfolds
    (and
      (equal (apply$ (list 'lambda vars body) args) (ev$ body (pairlis$ vars args)))
      (equal (apply$ (list 'lambda vars dcl body) args) (ev$ body (pairlis$ vars args))))
    :hints
    (("Goal" :in-theory (enable apply$ apply$-lambda)))))

(local
  (defthm
    fn-lbg-ev-variable-unfolds
    (implies (symbolp x) (equal (ev$ x a) (cdr (assoc-equal x a))))
    :hints
    (("Goal" :expand (ev$ x a) :in-theory (enable tamep)))))

(local
  (defthm
    fn-lbg-ev-quote-unfolds
    (equal (ev$ (list 'quote obj) a) obj)
    :hints
    (("Goal" :expand (ev$ (list 'quote obj) a)))))

(local
  (defthm
    fn-lbg-ev-function-unfolds
    (implies
      (and
        (not (eq fn 'quote))
        (not (eq fn 'if))
        (not (eq fn 'apply$))
        (not (eq fn 'ev$))
        (tamep (cons fn args)))
      (equal (ev$ (cons fn args) a) (apply$ fn (ev$-list args a))))
    :hints
    (("Goal" :expand (ev$ (cons fn args) a) :in-theory (disable tamep apply$ ev$ ev$-list)))))

(local
  (defthm
    fn-lbg-ev-if-unfolds
    (implies
      (suitably-tamep-listp 3 nil args)
      (equal
        (ev$ (cons 'if args) a)
        (if (ev$ (car args) a) (ev$ (cadr args) a) (ev$ (caddr args) a))))
    :hints
    (("Goal"
       :expand
       (ev$ (cons 'if args) a)
       :in-theory
       (e/d (badge) (ev$ ev$-list suitably-tamep-listp apply$))))))

(local
  (defthm
    fn-lbg-log-entry-shape
    (implies
      (loop$
        for
        s
        in
        (true-list-fix log)
        always
        (and (true-listp s) (true-list-listp (true-list-fix (caddr s)))))
      (and
        (alistp (remove-equal nil (true-list-fix log)))
        (true-listp (fn-lb-log-model-segment seg log))
        (true-list-listp (true-list-fix (caddr (fn-lb-log-model-segment seg log))))))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-model-segment seg log)
       :in-theory
       (enable fn-lb-log-model-segment always$ apply$ apply$-prim ev$-list badge)))))

(local
  (defthm
    fn-lbg-log-read-shape
    (implies
      (loop$
        for
        s
        in
        (true-list-fix log)
        always
        (and (true-listp s) (true-listp (cadr s)) (true-list-listp (true-list-fix (caddr s)))))
      (and
        (loop$
          for
          s
          in
          (true-list-fix log)
          always
          (and (true-listp s) (true-list-listp (true-list-fix (caddr s)))))
        (true-listp (cadr (fn-lb-log-model-segment seg log)))))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-model-segment seg log)
       :in-theory
       (enable fn-lb-log-model-segment always$ apply$ apply$-prim ev$-list badge)))))

(local
  (defthm
    fn-lbg-entry-list
    (implies
      (true-list-listp (true-list-fix entries))
      (true-listp (fn-lb-log-model-entry e entries)))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-model-entry e entries)
       :in-theory
       (enable fn-lb-log-model-entry true-list-listp)))))

(local
  (defthm
    fn-lbg-handle-entry-list
    (implies
      (true-list-listp (true-list-fix entries))
      (true-listp (fn-lb-log-model-handle-entry h entries)))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-model-handle-entry h entries)
       :in-theory
       (enable fn-lb-log-model-handle-entry true-list-listp)))))

(local
  (defthm
    fn-lbg-home-entry-list
    (implies
      (true-list-listp (true-list-fix entries))
      (true-listp (fn-lb-log-model-home-entry p entries)))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-model-home-entry p entries)
       :in-theory
       (enable fn-lb-log-model-home-entry true-list-listp)))))

(local
  (defthm
    fn-lbg-payload-entry-list
    (implies
      (loop$
        for
        s
        in
        (true-list-fix log)
        always
        (and (true-listp s) (true-list-listp (true-list-fix (caddr s)))))
      (true-listp (fn-lb-log-model-payload-entry h log)))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-model-payload-entry h log)
       :in-theory
       (enable fn-lb-log-model-payload-entry always$ apply$ apply$-prim ev$-list badge)))))

(local
  (defthm
    fn-lbg-held-numbers-alist
    (implies (fn-held-numbersp numbers) (alistp numbers))
    :hints
    (("Goal" :induct (fn-held-numbersp numbers) :in-theory (enable fn-held-numbersp)))))

(local
  (defthm
    fn-lbg-number-group-keys-list
    (true-listp (fn-lbc-number-group-keys numbers))
    :hints
    (("Goal"
       :induct
       (fn-lbc-number-group-keys numbers)
       :in-theory
       (enable fn-lbc-number-group-keys)))))

(local
  (defthm
    fn-lbg-catalog-car-numbers
    (implies
      (and (fn-cat$ap rows) (consp rows))
      (fn-held-numbersp (fn-held-numbers (car rows))))
    :hints
    (("Goal" :in-theory (enable fn-cat$ap fn-cat-rowsp)))))

(local
  (defthm
    fn-lbg-model-log-read-shape
    (implies
      (fn-lb-log-model-segsp log)
      (loop$
        for
        s
        in
        (true-list-fix log)
        always
        (and (true-listp s) (true-listp (cadr s)) (true-list-listp (true-list-fix (caddr s))))))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-model-segsp log)
       :in-theory
       (enable
         fn-lb-log-model-segsp
         fn-lb-log-model-entriesp
         fn-lb-log-model-entryp
         always$
         apply$
         apply$-prim
         ev$-list
         badge)))))

(local
  (defthm
    fn-lbg-remove-nil-alist
    (implies (alistp x) (equal (remove-equal nil x) x))
    :hints
    (("Goal" :induct (remove-equal nil x) :in-theory (enable alistp remove-equal)))))

(local
  (defthm
    fn-lbg-rowsp-car-numbers
    (implies
      (and (fn-cat-rowsp rows) (consp rows))
      (fn-held-numbersp (fn-held-numbers (car rows))))
    :hints
    (("Goal" :in-theory (enable fn-cat-rowsp)))))

(local
  (defthm
    fn-lbg-catalog-cdr
    (implies (fn-cat$ap rows) (fn-cat$ap (cdr rows)))
    :hints
    (("Goal" :in-theory (enable fn-cat$ap fn-cat-rowsp)))))

(local
  (defthm
    fn-lbg-list-entries-caars
    (implies (true-list-listp (true-list-fix x)) (alistp (remove-equal nil (true-list-fix x))))
    :hints
    (("Goal"
       :induct
       (remove-equal nil x)
       :in-theory
       (enable true-list-listp alistp remove-equal)))))

(local
  (defthm
    fn-lbg-rowwords-loc-fields
    (implies
      (and (adt-seq-p *fn-lbc-rowwords-schema* rows) (natp i) (< i (len rows)))
      (and (unsigned-byte-p 64 (nth 1 (nth i rows))) (unsigned-byte-p 64 (nth 2 (nth i rows)))))
    :hints
    (("Goal"
       :use
       ((:instance adt-tp-rec-p-nth (s *fn-lbc-rowwords-schema*) (a rows)))
       :in-theory
       (enable adt-rec-p adt-val-okp)))))

(local
  (defthm
    fn-lbg-locator-words
    (implies
      (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
      (fn-locp (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
    :hints
    (("Goal" :in-theory (enable fn-lbc-loc0 fn-lbc-loc1 fn-lbc-count fn-locp)))))

(local
  (defthm
    fn-lbg-union-list
    (implies (true-listp y) (true-listp (union-equal x y)))
    :hints
    (("Goal" :induct (union-equal x y) :in-theory (enable union-equal)))))

(local
  (defthm
    fn-lbg-row-group-keys-list
    (true-listp (fn-lbc-row-group-keys rows))
    :hints
    (("Goal" :induct (fn-lbc-row-group-keys rows) :in-theory (enable fn-lbc-row-group-keys)))))

(local
  (defthm
    fn-lbg-served-row-list-by-definition
    (true-listp (fn-lbc-served-row i fn-lbc))
    :hints
    (("Goal" :in-theory (enable fn-lbc-served-row)))
    :rule-classes
    :type-prescription))

(local
  (defthm
    fn-lbg-home-api-list
    (implies
      (loop$
        for
        s
        in
        (true-list-fix log)
        always
        (and (true-listp s) (true-list-listp (true-list-fix (caddr s)))))
      (true-listp (fn-lbc-home-entry i fn-lbc log)))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-log-entry-shape
          (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))))
       :in-theory
       (e/d
         (fn-lbc-home-entry)
         (always$ fn-lbc-loc0 fn-lbc-loc1 fn-lb-log-model-segment fn-lbg-log-entry-shape))))))

(local
  (defthm
    fn-lbg-served-regions-by-definition
    (and
      (true-listp (nth 6 (fn-lbc-served-row i fn-lbc)))
      (true-listp (nth 7 (fn-lbc-served-row i fn-lbc))))
    :hints
    (("Goal" :in-theory '(fn-lbc-served-row nth true-listp car-cons cdr-cons zp)))))

(local
  (defthm
    fn-lbg-offset-natural
    (natp (fn-loc-offset a b))
    :hints
    (("Goal" :in-theory (e/d (fn-loc-offset) (floor mod))))
    :rule-classes
    :type-prescription))

(local
  (defthm
    fn-lbg-length-natural
    (natp (fn-loc-len a b))
    :hints
    (("Goal" :in-theory (e/d (fn-loc-len) (floor mod))))
    :rule-classes
    :type-prescription))

(local
  (defthm
    fn-lbg-named-entries
    (equal
      (fn-lb-log-entries-guardp log)
      (loop$
        for
        s
        in
        (true-list-fix log)
        always
        (and (true-listp s) (true-list-listp (true-list-fix (caddr s))))))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-entries-guardp log)
       :in-theory
       (enable fn-lb-log-entries-guardp always$ apply$ apply$-prim ev$-list badge)))))

(local
  (defthm
    fn-lbg-named-read
    (equal
      (fn-lb-log-read-guardp log)
      (loop$
        for
        s
        in
        (true-list-fix log)
        always
        (and (true-listp s) (true-listp (cadr s)) (true-list-listp (true-list-fix (caddr s))))))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-read-guardp log)
       :in-theory
       (enable fn-lb-log-read-guardp always$ apply$ apply$-prim ev$-list badge)))))

(local
  (defthm
    fn-lbg-named-append
    (equal
      (fn-lb-log-append-guardp log)
      (loop$
        for
        s
        in
        (true-list-fix log)
        always
        (and (true-listp s) (true-listp (cadr s)) (true-listp (caddr s)))))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-append-guardp log)
       :in-theory
       (enable fn-lb-log-append-guardp always$ apply$ apply$-prim ev$-list badge)))))

(verify-guards fn-lb-value-treep :hints (("Goal" :in-theory (enable fn-lbc-escape-cellsp))))

(verify-guards
  fn-lb-log-entries-guardp
  :hints
  (("Goal" :in-theory (enable fn-lbc-escape-cellsp))))

(verify-guards fn-lb-log-read-guardp :hints (("Goal" :in-theory (enable fn-lbc-escape-cellsp))))

(verify-guards
  fn-lb-log-append-guardp
  :hints
  (("Goal" :in-theory (enable fn-lbc-escape-cellsp))))

(verify-guards fn-lbc-escape-cellsp :hints (("Goal" :in-theory (enable fn-lbc-escape-cellsp))))

(verify-guards
  fn-lbc-number-escape-cellsp
  :hints
  (("Goal" :in-theory (enable fn-lbc-escape-cellsp))))

(verify-guards
  fn-nntp-stuffed-section
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-log-model-wire
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-la-payload-wire :guard-debug t)

(verify-guards
  fn-lb-log-model-homes
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-log-model-nat-octets
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lb-log-model-text-octets :guard-debug t)

(verify-guards fn-lb-log-model-entryp :guard-debug t)

(verify-guards
  fn-lb-log-model-entriesp
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-log-model-segsp
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lb-log-model-segment :guard-debug t)

(verify-guards
  fn-lb-log-model-entry
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-log-model-read-range
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-log-model-home-entry
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-log-model-read-home-frame
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-log-read-shape (log segs) (seg (car position)))
       (:instance fn-lbg-log-entry-shape (log segs) (seg (car position))))
     :in-theory
     (disable always$ fn-lb-log-model-segment fn-lbg-log-read-shape fn-lbg-log-entry-shape))))

(verify-guards fn-lb-log-model-handle-entry :guard-debug t)

(verify-guards
  fn-lb-log-model-payload-entry
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-log-model-payload-segment
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-log-payload
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-entry-protected-len
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-entry-octets
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-log-read-shape)
       (:instance fn-lbg-log-entry-shape)
       (:instance fn-lbg-list-entries-caars (x (caddr (fn-lb-log-model-segment seg log)))))
     :in-theory
     (disable
       always$
       fn-lb-log-model-segment
       fn-lb-log-model-entry
       fn-lbg-log-read-shape
       fn-lbg-log-entry-shape
       fn-lbg-list-entries-caars))))

(verify-guards
  fn-lb-log-model-pre
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-log-model-recycle
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-arena-is-log
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-loc0
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-loc1
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards update-fn-lbc-loc0 :guard-debug t)

(verify-guards update-fn-lbc-loc1 :guard-debug t)

(verify-guards
  fn-lbc-word
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-directory-field :guard-debug t)

(verify-guards
  fn-lbc-membership-field
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-nov-field
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-msgid-pool-octet :guard-debug t)

(verify-guards
  fn-lbc-msgid-pool-range
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-msgid-pool-append
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-overview-pool-octet
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-overview-pool-range
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-overview-pool-append
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-clear-columns :guard-debug t)

(verify-guards
  fn-lbc-escape
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-value
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-directory-value
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-msgid
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-flag :guard-debug t)

(verify-guards
  fn-lbc-withdrawn
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-membership-group
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-membership-run :guard-debug t)

(verify-guards
  fn-lbc-groups
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-numbers
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-nov-text :guard-debug t)

(verify-guards fn-lbc-nov-at :guard-debug t)

(verify-guards
  fn-lbc-original-nov
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-render-nov
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-served-row
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-log-model-value-octets
  :hints
  (("Goal" :in-theory (enable fn-lb-value-treep))))

(verify-guards
  fn-lb-log-model-home-frame
  :hints
  (("Goal" :in-theory (enable fn-lb-value-treep))))

(local
  (defthm
    fn-lbg-value-octets-list
    (true-listp (fn-lb-log-model-value-octets value))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-model-value-octets value)
       :in-theory
       (enable fn-lb-log-model-value-octets)))
    :rule-classes
    :type-prescription))

(local
  (defthm
    fn-lbg-home-frame-list
    (implies (fn-cat-rowp row) (true-listp (fn-lb-log-model-home-frame row)))
    :hints
    (("Goal" :in-theory (enable fn-lb-log-model-home-frame)))))

(verify-guards
  fn-lbc-home-entry
  :hints
  (("Goal"
     :use
     ((:instance
        fn-lbg-log-entry-shape
        (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))))
     :in-theory
     (disable
       always$
       fn-lbc-p
       fn-lbc-loc0
       fn-lbc-loc1
       fn-lbc-count
       fn-lb-log-model-segment
       fn-lbg-log-entry-shape))))

(verify-guards
  fn-lbc-restore-control
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-sparse-u64
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-text-smallp :guard-debug t)

(verify-guards fn-lbc-nov-smallp :guard-debug t)

(verify-guards
  fn-lbc-numbers-smallp
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-append-nov-texts
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-nov-spans :guard-debug t)

(verify-guards
  fn-lbc-append-nov
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-append-memberships
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-msgid-hash-octets
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-msgid-hash
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-visiblep
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-newnews-candidatep
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-number-get
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-number-put-first
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-number-put-row-seen :guard-debug t)

(verify-guards
  fn-lbc-number-put-row
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-summary-word
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-live-summary :guard-debug t)

(verify-guards
  fn-lbc-summary-put
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lbc-number-group-keys :guard-debug t)

(verify-guards
  fn-lbc-row-group-keys
  :hints
  (("Goal" :in-theory (disable fn-cat$ap fn-cat-rowsp))))

(verify-guards fn-lbc-rebuild-summaries :guard-debug t)

(verify-guards fn-lbc-slot-word :guard-debug t)

(verify-guards
  fn-lbc-reserve-slots
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-slot-insert
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-index-slots
  :hints
  (("Goal" :in-theory (disable floor mod fn-lbc-p fn-lbc-slot-count fn-lbc-word))))

(verify-guards
  fn-lbc-summaries-corr
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-summary-cells-corr
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lbc-number-cells-corr
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards
  fn-lb-verified-entries-invp
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lb-vmap-index-covers :guard-debug t)

(verify-guards
  fn-lb-vmap-mark
  :hints
  (("Goal" :in-theory (disable always$ fn-lbc-p fn-lb-log-model-segment fn-lb-log-model-entry))))

(verify-guards fn-lb-vmap-recycle-keys :guard-debug t)

(verify-guards fn-lb-vmap-retain-keys :guard-debug t)

(verify-guards
  fn-lb-vmap-recycle
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lc-home-position :guard-debug t)

(verify-guards fn-lc-count :guard-debug t)

(verify-guards fn-lc-segsp :guard-debug t)

(verify-guards
  fn-lc-read-range
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-model-log-read-shape (log segs))
       (:instance fn-lbg-log-read-shape (log segs) (seg (fn-loc-segment loc0 loc1)))
       (:instance fn-lbg-log-entry-shape (log segs) (seg (fn-loc-segment loc0 loc1))))
     :in-theory
     (e/d
       (fn-lc-segsp)
       (always$
         fn-lb-log-model-segsp
         fn-lb-log-model-segment
         fn-lbg-log-read-shape
         fn-lbg-log-entry-shape
         fn-lbg-model-log-read-shape
         fn-lbg-home-api-list)))))

(verify-guards
  fn-lc-read-home-frame
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-model-log-read-shape (log segs)))
     :in-theory
     (disable always$ fn-lc-segsp fn-lb-log-model-segsp))))

(verify-guards
  fn-lc-expected-range
  :guard-debug
  t
  :hints
  (("Goal" :in-theory (enable always$ apply$ apply$-prim ev$-list badge))))

(verify-guards fn-lc-pin-entries-p :guard-debug t)

(verify-guards fn-lbc-home-guardp :hints (("Goal" :in-theory (enable fn-lbc-home-entry))))

(verify-guards
  fn-lbc-at
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-served-regions-by-definition) (:instance fn-lbg-home-api-list))
     :in-theory
     (disable
       always$
       fn-lbc-p
       fn-lbc-count
       fn-lbc-home-entry
       fn-lbc-served-row
       fn-lbc-restore-control
       fn-lbg-served-regions-by-definition
       fn-lbg-home-api-list))))

(verify-guards
  fn-lbc-stored-range
  :hints
  (("Goal"
     :use
     ((:instance
        fn-lbg-log-read-shape
        (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))))
       (:instance
         fn-lbg-log-entry-shape
         (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))))
     :in-theory
     (disable
       always$
       fn-lbc-p
       fn-lbc-count
       fn-lbc-loc0
       fn-lbc-loc1
       fn-loc-offset
       fn-loc-len
       fn-lbc-value
       fn-lbc-directory-value
       fn-lb-log-model-segment
       fn-lbg-log-read-shape
       fn-lbg-log-entry-shape))))

(verify-guards fn-lbc-row-log-guardp)

(verify-guards fn-lbc-rows-log-guardp)

(verify-guards fn-lbc-row-homes-guardp)

(local
  (defthm
    fn-lbg-escape-select
    (implies
      (and
        (natp start)
        (natp i)
        (<= start i)
        (< i (fn-lbc-count fn-lbc))
        (fn-lbc-escape-cellsp start fn-lbc))
      (alistp (fn-lbc-escape-store-get i fn-lbc)))
    :hints
    (("Goal"
       :induct
       (fn-lbc-escape-cellsp start fn-lbc)
       :in-theory
       (e/d (fn-lbc-escape-cellsp) (fn-lbc-p fn-lbc-count fn-lbc-escape-store-get))))))

(local
  (defthm
    fn-lbg-number-escape-select
    (implies
      (and
        (natp start)
        (natp i)
        (<= start i)
        (< i (fn-lbc-count fn-lbc))
        (fn-lbc-number-escape-cellsp start fn-lbc))
      (alistp (cdr (assoc-eq :numbers (fn-lbc-escape-store-get i fn-lbc)))))
    :hints
    (("Goal"
       :induct
       (fn-lbc-number-escape-cellsp start fn-lbc)
       :in-theory
       (e/d (fn-lbc-number-escape-cellsp) (fn-lbc-p fn-lbc-count fn-lbc-escape-store-get))))))

(verify-guards fn-lc-pin-tokens)

(verify-guards fn-lc-pins-p)

(verify-guards fn-lc-pin-references)

(verify-guards fn-lc-pin-ownedp)

(local (include-book "arithmetic-5/top" :dir :system))

(local
  (defthm
    fn-lbg-membership-run-alist
    (alistp (fn-lbc-membership-run start count t fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-membership-run start count t fn-lbc)
       :in-theory
       (e/d (fn-lbc-membership-run) (fn-lbc-p fn-lbc-membership-group fn-lbc-membership-field))))))

(local
  (defthm
    fn-lbg-numbers-alist
    (implies
      (and
        (fn-lbc-escape-cellsp 0 fn-lbc)
        (fn-lbc-number-escape-cellsp 0 fn-lbc)
        (natp i)
        (< i (fn-lbc-count fn-lbc)))
      (alistp (fn-lbc-numbers i fn-lbc)))
    :hints
    (("Goal"
       :use
       ((:instance fn-lbg-escape-select (start 0))
         (:instance fn-lbg-number-escape-select (start 0)))
       :in-theory
       (e/d
         (fn-lbc-numbers fn-lbc-escape)
         (fn-lbc-escape-store-get
           fn-lbc-escape-cellsp
           fn-lbc-number-escape-cellsp
           fn-lbc-count
           fn-lbc-p
           fn-lbc-directory-value
           fn-lbc-membership-run))))))

(local
  (defthm
    fn-lbg-slot-field
    (implies
      (and (adt-seq-p *fn-lbc-msgid-slots-schema* rows) (natp i) (< i (len rows)))
      (unsigned-byte-p 64 (car (nth i rows))))
    :hints
    (("Goal"
       :use
       ((:instance adt-tp-rec-p-nth (s *fn-lbc-msgid-slots-schema*) (a rows)))
       :in-theory
       (enable adt-rec-p adt-val-okp)))))

(verify-guards
  fn-lbc-first-reaching
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-escape-select (start 0) (i (+ lo (floor (- hi lo) 2)))))
     :in-theory
     (disable
       fn-lbc-escape-cellsp
       fn-lbc-escape-store-get
       fn-lbc-count
       fn-lbc-p
       fn-lbc-value
       floor
       mod
       |(floor x 2)|))))

(local
  (defthm
    fn-lbg-slot-natural
    (implies (fn-lbc-p fn-lbc) (natp (fn-lbc-slot-word slot fn-lbc)))
    :hints
    (("Goal"
       :use
       ((:instance fn-lbg-slot-field (rows (nth *fn-lbc-slot-store* fn-lbc)) (i slot)))
       :in-theory
       (enable fn-lbc-slot-word)))
    :rule-classes
    :type-prescription))

(local
  (defthm
    fn-lbg-slot-cons
    (implies
      (and (adt-seq-p *fn-lbc-msgid-slots-schema* rows) (natp i) (< i (len rows)))
      (consp (nth i rows)))
    :hints
    (("Goal"
       :use
       ((:instance adt-tp-rec-p-nth (s *fn-lbc-msgid-slots-schema*) (a rows)))
       :in-theory
       (enable adt-rec-p adt-val-okp)))))

(verify-guards
  fn-lbc-stamp-escape-cellsp
  :hints
  (("Goal" :in-theory (enable fn-lbc-escape-cellsp))))

(local
  (defthm
    fn-lbg-hnov-small
    (implies (fn-hnov-p nov) (fn-lbc-nov-smallp nov))
    :hints
    (("Goal" :in-theory (enable fn-hnov-p fn-lbc-nov-smallp fn-lbc-text-smallp)))))

(local
  (defthm
    fn-lbg-msgid-pool-append-escape-column-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-msgid-pool-append bytes fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-msgid-pool-append bytes fn-lbc)
       :in-theory
       (e/d (fn-lbc-msgid-pool-append) (fn-lbc-msgid-octets-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-overview-pool-append-escape-column-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-overview-pool-append bytes fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-overview-pool-append bytes fn-lbc)
       :in-theory
       (e/d (fn-lbc-overview-pool-append) (fn-lbc-overview-octets-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-nov-texts-escape-column-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-append-nov-texts texts fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-append-nov-texts texts fn-lbc)
       :in-theory
       (e/d (fn-lbc-append-nov-texts) (fn-lbc-overview-pool-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-memberships-escape-column-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-append-memberships items numbersp fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-append-memberships items numbersp fn-lbc)
       :in-theory
       (e/d
         (fn-lbc-append-memberships)
         (fn-lbc-overview-pool-append fn-lbc-memberships-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-nov-escape-column-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-append-nov nov fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal"
       :in-theory
       (e/d (fn-lbc-append-nov) (fn-lbc-append-nov-texts fn-lbc-nov-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-withdrawn-spine
    (implies (fn-held-withdrawnp w) (or (consp w) (null w)))
    :hints
    (("Goal" :in-theory (enable fn-held-withdrawnp)))))

(local
  (defthm
    fn-lbg-u64-output
    (unsigned-byte-p 64 (fn-lbc-u64 x))
    :hints
    (("Goal" :in-theory (enable fn-lbc-u64)))))

(local
  (defthm
    fn-lbg-row-sequence
    (implies (fn-cat-rowp row) (natp (fn-record-sequence row)))
    :hints
    (("Goal" :in-theory (enable fn-cat-rowp fn-record-uint64p)))))

(verify-guards
  fn-lb-log-model-append-to-segment
  :hints
  (("Goal"
     :in-theory
     (disable
       fn-lb-log-model-homes
       fn-lb-value-treep
       fn-lb-log-model-home-frame
       fn-rcl-tombstonep
       fn-cat-rowp))))

(local
  (defthm
    fn-lbg-escape-put-preserved
    (implies
      (and (natp key) (alistp cell) (fn-lbc-escape-cellsp i fn-lbc))
      (fn-lbc-escape-cellsp i (fn-lbc-escape-store-put key cell fn-lbc)))
    :hints
    (("Goal"
       :induct
       (fn-lbc-escape-cellsp i fn-lbc)
       :in-theory
       (e/d
         (fn-lbc-escape-cellsp fn-lbc-escape-store-put fn-lbc-escape-store-get fn-lbc-count)
         (fn-lbc-p))))))

(local
  (defthm
    fn-lbg-escape-clear-preserved
    (fn-lbc-escape-cellsp 0 (fn-lbc-clear-columns fn-lbc))
    :hints
    (("Goal"
       :in-theory
       (e/d (fn-lbc-clear-columns fn-lbc-escape-cellsp fn-lbc-count) (fn-lbc-p))))))

(local
  (defthm
    fn-lbg-escape-frame-update
    (implies
      (and (natp field) (< 0 field) (not (equal field *fn-lbc-escape-store-get*)))
      (equal
        (fn-lbc-escape-cellsp i (update-nth field value fn-lbc))
        (fn-lbc-escape-cellsp i fn-lbc)))
    :hints
    (("Goal"
       :induct
       (fn-lbc-escape-cellsp i fn-lbc)
       :in-theory
       (e/d (fn-lbc-escape-cellsp fn-lbc-count fn-lbc-escape-store-get) (fn-lbc-p))))))

(verify-guards
  fn-lbc-msgid-probe
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-escape-select (start 0) (i (- (fn-lbc-slot-word slot fn-lbc) 1))))
     :in-theory
     (disable
       fn-lbc-slot-word
       fn-lbc-escape-cellsp
       fn-lbc-count
       fn-lbc-p
       fn-lbc-escape-store-get
       fn-lbc-msgid
       fn-lbc-word
       floor
       mod))))

(verify-guards
  fn-lbc-msgid-seqs
  :hints
  (("Goal"
     :in-theory
     (disable fn-lbc-msgid-probe fn-lbc-escape-cellsp fn-lbc-count fn-lbc-p floor mod))))

(local
  (defthm
    fn-lbg-stamp-escape-select
    (implies
      (and
        (natp start)
        (natp i)
        (<= start i)
        (< i (fn-lbc-count fn-lbc))
        (fn-lbc-stamp-escape-cellsp start fn-lbc))
      (let
        ((escape (assoc-eq :stamp (fn-lbc-escape-store-get i fn-lbc))))
        (or (not escape) (acl2-numberp (cdr escape)))))
    :hints
    (("Goal"
       :induct
       (fn-lbc-stamp-escape-cellsp start fn-lbc)
       :in-theory
       (e/d (fn-lbc-stamp-escape-cellsp) (fn-lbc-p fn-lbc-count fn-lbc-escape-store-get))))))

(local
  (defthm
    fn-lbg-rowwords-stamp-field
    (implies
      (and (adt-seq-p *fn-lbc-rowwords-schema* rows) (natp i) (< i (len rows)))
      (unsigned-byte-p 64 (nth 4 (nth i rows))))
    :hints
    (("Goal"
       :use
       ((:instance adt-tp-rec-p-nth (s *fn-lbc-rowwords-schema*) (a rows)))
       :in-theory
       (enable adt-rec-p adt-val-okp)))))

(local
  (defthm
    fn-lbg-midpoint-bounds
    (implies
      (and (natp lo) (natp hi) (< lo hi))
      (and
        (natp (+ lo (floor (- hi lo) 2)))
        (<= lo (+ lo (floor (- hi lo) 2)))
        (< (+ lo (floor (- hi lo) 2)) hi)))
    :hints
    (("Goal" :in-theory (disable floor mod |(floor x 2)|)))
    :rule-classes
    nil))

(local
  (defthm
    fn-lbg-dense-stamp-number
    (implies
      (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)))
      (acl2-numberp (fn-lbc-word :stamp i fn-lbc)))
    :hints
    (("Goal"
       :use
       ((:instance fn-lbg-rowwords-stamp-field (rows (car fn-lbc))))
       :in-theory
       (enable fn-lbc-word fn-lbc-count)))
    :rule-classes
    :type-prescription))

(local
  (defthm
    fn-lbg-stamp-value-number
    (implies
      (and
        (fn-lbc-p fn-lbc)
        (fn-lbc-escape-cellsp 0 fn-lbc)
        (fn-lbc-stamp-escape-cellsp 0 fn-lbc)
        (natp i)
        (< i (fn-lbc-count fn-lbc)))
      (acl2-numberp (fn-lbc-value i :stamp fn-lbc)))
    :hints
    (("Goal"
       :use
       ((:instance fn-lbg-escape-select (start 0))
         (:instance fn-lbg-stamp-escape-select (start 0)))
       :in-theory
       (e/d
         (fn-lbc-value fn-lbc-escape)
         (fn-lbc-word
           fn-lbc-count
           fn-lbc-p
           fn-lbc-escape-store-get
           fn-lbc-stamp-escape-cellsp
           fn-lbc-escape-cellsp))))
    :rule-classes
    :type-prescription))

(local
  (defthm
    fn-lbg-named-reader-caar
    (implies (fn-lb-log-read-guardp log) (alistp (remove-equal nil (true-list-fix log))))
    :hints
    (("Goal"
       :use
       ((:instance fn-lbg-log-read-shape) (:instance fn-lbg-log-entry-shape))
       :in-theory
       (disable fn-lb-log-read-guardp fn-lb-log-entries-guardp always$)))))

(local
  (defthm
    fn-lbg-first-reaching-bounds
    (implies
      (and (natp lo) (natp hi) (<= lo hi))
      (and
        (natp (fn-lbc-first-reaching threshold lo hi fn-lbc))
        (<= lo (fn-lbc-first-reaching threshold lo hi fn-lbc))
        (<= (fn-lbc-first-reaching threshold lo hi fn-lbc) hi)))
    :hints
    (("Goal"
       :induct
       (fn-lbc-first-reaching threshold lo hi fn-lbc)
       :expand
       ((fn-lbc-first-reaching threshold lo hi fn-lbc))
       :in-theory
       (e/d
         ((:induction fn-lbc-first-reaching))
         ((:definition fn-lbc-first-reaching)
           fn-lbc-value
           fn-lbc-count
           fn-lbc-p
           floor
           mod
           |(floor x 2)|)))
      ("Subgoal *1/3" :use fn-lbg-midpoint-bounds)
      ("Subgoal *1/2" :use fn-lbg-midpoint-bounds))
    :rule-classes
    nil))

(verify-guards
  fn-lb-log-model-append
  :hints
  (("Goal"
     :in-theory
     (e/d
       (fn-lb-log-append-guardp)
       (fn-lbg-named-append
         fn-lb-value-treep
         fn-lb-log-model-homes
         fn-cat-rowp
         fn-rcl-tombstonep
         fn-lb-log-model-append-to-segment)))))

(local
  (defthm
    fn-lbg-sparse-alist
    (alistp (fn-lbc-sparse-u64 fields values))
    :hints
    (("Goal" :induct (fn-lbc-sparse-u64 fields values) :in-theory (enable fn-lbc-sparse-u64)))))

(local
  (defthm
    fn-lbg-mod-u64
    (implies (integerp x) (unsigned-byte-p 64 (mod x 18446744073709551616)))
    :hints
    (("Goal"
       :use
       ((:instance mod-bounds-1 (y 18446744073709551616)))
       :in-theory
       '(unsigned-byte-p integer-range-p (:type-prescription integerp-mod-1) (:executable-counterpart <) (:executable-counterpart expt) (:executable-counterpart binary-*) (:executable-counterpart binary-+) (:executable-counterpart not))))))

(local
  (defthm
    fn-lbg-msgid-hash-word
    (implies
      (unsigned-byte-p 64 hash)
      (unsigned-byte-p 64 (fn-lbc-msgid-hash-octets bytes hash)))
    :hints
    (("Goal"
       :induct
       (fn-lbc-msgid-hash-octets bytes hash)
       :in-theory
       '(fn-lbc-msgid-hash-octets fn-lbg-mod-u64 nfix natp unsigned-byte-p integer-range-p (:type-prescription integerp-mod-1) (:executable-counterpart <) (:executable-counterpart not) (:executable-counterpart expt))))))

(local
  (defthm
    fn-lbg-msgid-hash-u64
    (unsigned-byte-p 64 (fn-lbc-msgid-hash msgid))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-msgid-hash) (fn-lbc-msgid-hash-octets unsigned-byte-p))))))

(verify-guards
  fn-lbc-row-corr
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-named-reader-caar)
       (:instance fn-lbg-log-entry-shape)
       (:instance
         fn-lbg-log-read-shape
         (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))))
     :in-theory
     (disable
       fn-nntp-stuffed-section
       fn-lb-log-model-wire
       fn-la-payload-wire
       fn-la-tombstone-raw
       fn-lb-log-model-homes
       fn-lb-log-model-nat-octets
       fn-lb-log-model-text-octets
       fn-lb-value-treep
       fn-lb-log-model-value-octets
       fn-lb-log-model-home-frame
       fn-lb-log-model-entryp
       fn-lb-log-model-entriesp
       fn-lb-log-model-segsp
       fn-lb-log-entries-guardp
       fn-lb-log-read-guardp
       fn-lb-log-append-guardp
       fn-lb-log-model-segment
       fn-lb-log-model-entry
       fn-lb-log-model-read-range
       fn-lb-log-model-home-entry
       fn-lb-log-model-read-home-frame
       fn-lb-log-model-handle-entry
       fn-lb-log-model-payload-entry
       fn-lb-log-model-payload-segment
       fn-lb-log-payload
       fn-lb-entry-protected-len
       fn-lb-entry-octets
       fn-lb-log-model-pre
       fn-lb-log-model-append-to-segment
       fn-lb-log-model-append
       fn-lb-log-model-recycle
       fn-lb-arena-is-log
       fn-lbc-count
       fn-lbc-escape-cellsp
       fn-lbc-number-escape-cellsp
       fn-lbc-stamp-escape-cellsp
       fn-lbc-loc0
       fn-lbc-loc1
       update-fn-lbc-loc0
       update-fn-lbc-loc1
       fn-lbc-word
       fn-lbc-directory-field
       fn-lbc-membership-field
       fn-lbc-nov-field
       fn-lbc-msgid-pool-count
       fn-lbc-msgid-pool-octet
       fn-lbc-msgid-pool-range
       fn-lbc-msgid-pool-append
       fn-lbc-overview-pool-count
       fn-lbc-overview-pool-octet
       fn-lbc-overview-pool-range
       fn-lbc-overview-pool-append
       fn-lbc-clear-columns
       fn-lbc-escape
       fn-lbc-value
       fn-lbc-directory-value
       fn-lbc-msgid
       fn-lbc-flag
       fn-lbc-withdrawn
       fn-lbc-membership-group
       fn-lbc-membership-run
       fn-lbc-groups
       fn-lbc-numbers
       fn-lbc-nov-text
       fn-lbc-nov-at
       fn-lbc-original-nov
       fn-lbc-render-nov
       fn-cat-served-projection
       fn-lbc-served-row
       fn-lbc-home-entry
       fn-lbc-restore-control
       fn-lbc-home-guardp
       fn-lbc-at
       fn-lbc-u64
       fn-lbc-sparse-u64
       fn-lbc-text-smallp
       fn-lbc-nov-smallp
       fn-lbc-numbers-smallp
       fn-lbc-nov-record-count
       fn-lbc-membership-record-count
       fn-lbc-append-nov-texts
       fn-lbc-nov-spans
       fn-lbc-append-nov
       fn-lbc-append-memberships
       fn-lbc-msgid-hash-octets
       fn-lbc-msgid-hash
       fn-lbc-row-log-guardp
       fn-lbc-rows-log-guardp
       fn-lbc-row-homes-guardp
       fn-lbc-append-row
       fn-lbc-visiblep
       lb-prefix-max
       lb-first-at-least
       lb-keep-from
       fn-lbc-first-reaching
       fn-lbc-newnews-candidatep
       fn-lbc-newnews-tail
       fn-lbc-newnews-range
       fn-lbc-stored-range
       fn-lbc-number-get
       fn-lbc-number-put-first
       fn-lbc-number-put-row-seen
       fn-lbc-number-put-row
       fn-lbc-summary-word
       fn-lbc-live-summary
       fn-lbc-summary-put
       fn-lbc-number-group-keys
       fn-lbc-row-group-keys
       fn-lbc-rebuild-summaries
       fn-lbc-rebuild-rows
       fn-lbc-slot-count
       fn-lbc-slot-word
       fn-lbc-reserve-slots
       fn-lbc-slot-insert
       fn-lbc-index-slots
       fn-lbc-msgid-probe
       fn-lbc-msgid-seqs
       fn-lbc-open-rebuild
       fn-lbc-row-corr
       fn-lbc-rows-corr
       fn-lbc-summaries-corr
       fn-lbc-summary-cells-corr
       fn-lbc-number-cells-corr
       fn-lb-verified-bit
       fn-lb-verified-entries-invp
       fn-lb-vmap-index-covers
       fn-lb-vmap-mark
       fn-lb-vmap-recycle-keys
       fn-lb-vmap-retain-keys
       fn-lb-vmap-recycle
       fn-lc-home-position
       fn-lc-count
       fn-lc-segsp
       fn-lc-read-range
       fn-lc-read-home-frame
       fn-lc-expected-home-frame
       fn-lc-expected-range
       fn-lc-bound-row
       fn-lc-locator-resolves
       fn-lc-resolve-from
       fn-lc-locators-resolve
       fn-lc-pin-tokens
       fn-lc-pin-entries-p
       fn-lc-pins-p
       fn-lc-pin-references
       fn-lc-pin-ownedp
       fn-lbc-p
       floor
       mod
       always$
       fn-nntp-section-of-bytes
       fn-hnov-of
       fn-hf-nov
       fn-cat-served-projection
       fn-nntp-split-article
       fn-nntp-split-head
       fn-loc-segment
       fn-loc-offset
       fn-loc-len))))

(verify-guards
  fn-lbc-newnews-tail
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-escape-select (start 0) (i (- hi 1)))
       (:instance fn-lbg-numbers-alist (i (- hi 1)))
       (:instance fn-lbg-stamp-value-number (i (- hi 1))))
     :in-theory
     (disable
       fn-lbc-escape-cellsp
       fn-lbc-number-escape-cellsp
       fn-lbc-stamp-escape-cellsp
       fn-lbc-escape-store-get
       fn-lbc-count
       fn-lbc-p
       fn-lbc-numbers
       fn-lbc-visiblep
       fn-lbc-value
       fn-lbc-msgid
       fn-lbc-flag
       fn-lbc-word
       floor
       mod))))

(verify-guards
  fn-lbc-newnews-range
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-first-reaching-bounds (lo 0) (hi v)))
     :in-theory
     (disable
       fn-lbc-first-reaching
       fn-lbc-count
       fn-lbc-p
       fn-lbc-escape-cellsp
       fn-lbc-number-escape-cellsp
       fn-lbc-stamp-escape-cellsp))))

(local
  (defthm
    fn-lbg-row-homes-cdr
    (implies (fn-lbc-row-homes-guardp rows) (fn-lbc-row-homes-guardp (cdr rows)))
    :hints
    (("Goal" :in-theory (enable fn-lbc-row-homes-guardp)))))

(verify-guards
  fn-lbc-rows-corr
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-escape-select (start 0)))
     :in-theory
     (e/d
       (fn-lbc-row-homes-guardp)
       (fn-lb-log-model-homes
         fn-lb-value-treep
         fn-lbc-p
         fn-lbc-count
         fn-lbc-escape-cellsp
         fn-lbc-escape-store-get
         fn-lbc-row-corr
         fn-lb-log-read-guardp
         fn-lbg-named-read
         always$)))))

(local
  (defthm
    fn-lbg-rows-log-cdr
    (implies (fn-lbc-rows-log-guardp rows log) (fn-lbc-rows-log-guardp (cdr rows) log))
    :hints
    (("Goal" :in-theory (enable fn-lbc-rows-log-guardp)))))

(local
  (defthm
    fn-lbg-row-log-widths
    (implies
      (fn-lbc-row-log-guardp row log)
      (and
        (unsigned-byte-p 64 (fn-lb-log-model-payload-segment (fn-record-payload row) log))
        (unsigned-byte-p 32 (nth 3 (fn-lb-log-model-payload-entry (fn-record-payload row) log)))
        (unsigned-byte-p 32 (nth 4 (fn-lb-log-model-payload-entry (fn-record-payload row) log)))))
    :hints
    (("Goal" :in-theory (enable fn-lbc-row-log-guardp)))
    :rule-classes
    nil))

; Resume 3: update projections, establishment and LC guard grant.

(local
  (defthm
    fn-lbg-escape-extensional
    (implies
      (and
        (equal (fn-lbc-count x) (fn-lbc-count y))
        (equal (nth *fn-lbc-escape-store-get* x) (nth *fn-lbc-escape-store-get* y)))
      (equal (fn-lbc-escape-cellsp i x) (fn-lbc-escape-cellsp i y)))
    :hints
    (("Goal"
       :induct
       (fn-lbc-escape-cellsp i x)
       :in-theory
       (e/d
         ((:induction fn-lbc-escape-cellsp) fn-lbc-escape-store-get)
         ((:definition fn-lbc-escape-cellsp) fn-lbc-count fn-lbc-p))
       :expand
       ((fn-lbc-escape-cellsp i x) (fn-lbc-escape-cellsp i y))))
    :rule-classes
    nil))

(local
  (defthm
    fn-lbg-msgid-pool-append-count-frame
    (equal (fn-lbc-count (fn-lbc-msgid-pool-append bytes fn-lbc)) (fn-lbc-count fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-msgid-pool-append bytes fn-lbc)
       :in-theory
       (e/d (fn-lbc-msgid-pool-append fn-lbc-count) (fn-lbc-msgid-octets-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-msgid-pool-append-escape-get-frame
    (equal
      (fn-lbc-escape-store-get key (fn-lbc-msgid-pool-append bytes fn-lbc))
      (fn-lbc-escape-store-get key fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-escape-store-get) (fn-lbc-msgid-pool-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-msgid-pool-append-escape-frame
    (equal
      (fn-lbc-escape-cellsp i (fn-lbc-msgid-pool-append bytes fn-lbc))
      (fn-lbc-escape-cellsp i fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (x (fn-lbc-msgid-pool-append bytes fn-lbc))
          (y fn-lbc)))
       :in-theory
       (disable
         fn-lbc-escape-cellsp
         fn-lbc-count
         fn-lbc-escape-store-get
         fn-lbc-msgid-pool-append
         fn-lbc-p)))))

(local
  (defthm
    fn-lbg-overview-pool-append-count-frame
    (equal (fn-lbc-count (fn-lbc-overview-pool-append bytes fn-lbc)) (fn-lbc-count fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-overview-pool-append bytes fn-lbc)
       :in-theory
       (e/d (fn-lbc-overview-pool-append fn-lbc-count) (fn-lbc-overview-octets-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-overview-pool-append-escape-get-frame
    (equal
      (fn-lbc-escape-store-get key (fn-lbc-overview-pool-append bytes fn-lbc))
      (fn-lbc-escape-store-get key fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-escape-store-get) (fn-lbc-overview-pool-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-overview-pool-append-escape-frame
    (equal
      (fn-lbc-escape-cellsp i (fn-lbc-overview-pool-append bytes fn-lbc))
      (fn-lbc-escape-cellsp i fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (x (fn-lbc-overview-pool-append bytes fn-lbc))
          (y fn-lbc)))
       :in-theory
       (disable
         fn-lbc-escape-cellsp
         fn-lbc-count
         fn-lbc-escape-store-get
         fn-lbc-overview-pool-append
         fn-lbc-p)))))

(local
  (defthm
    fn-lbg-append-nov-texts-count-frame
    (equal (fn-lbc-count (fn-lbc-append-nov-texts texts fn-lbc)) (fn-lbc-count fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-append-nov-texts texts fn-lbc)
       :in-theory
       (e/d (fn-lbc-append-nov-texts fn-lbc-count) (fn-lbc-overview-pool-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-nov-texts-escape-get-frame
    (equal
      (fn-lbc-escape-store-get key (fn-lbc-append-nov-texts texts fn-lbc))
      (fn-lbc-escape-store-get key fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-escape-store-get) (fn-lbc-append-nov-texts fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-nov-texts-escape-frame
    (equal
      (fn-lbc-escape-cellsp i (fn-lbc-append-nov-texts texts fn-lbc))
      (fn-lbc-escape-cellsp i fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (x (fn-lbc-append-nov-texts texts fn-lbc))
          (y fn-lbc)))
       :in-theory
       (disable
         fn-lbc-escape-cellsp
         fn-lbc-count
         fn-lbc-escape-store-get
         fn-lbc-append-nov-texts
         fn-lbc-p)))))

(local
  (defthm
    fn-lbg-append-memberships-escape-get-frame
    (equal
      (fn-lbc-escape-store-get key (fn-lbc-append-memberships items numbersp fn-lbc))
      (fn-lbc-escape-store-get key fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-escape-store-get) (fn-lbc-append-memberships fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-nov-escape-get-frame
    (equal
      (fn-lbc-escape-store-get key (fn-lbc-append-nov nov fn-lbc))
      (fn-lbc-escape-store-get key fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-escape-store-get) (fn-lbc-append-nov fn-lbc-p))))))

(local
  (defthm
    fn-lbg-flags-word
    (unsigned-byte-p 64 (+ (if a 1 0) (if b 2 0) (if c 4 0) (if d 8 0) (if e 16 0) (if f 32 0)))
    :hints
    (("Goal" :in-theory (enable unsigned-byte-p integer-range-p)))))

(local
  (defthm
    fn-lbg-framed-boolean
    (booleanp (fn-nntp-framed-of-bytes payload))
    :hints
    (("Goal"
       :in-theory
       (e/d (fn-nntp-framed-of-bytes fn-nntp-split-okp) (fn-nntp-split-article))))))

(local
  (defthm
    fn-lbg-rowwords-record
    (implies
      (and (fn-locp loc0 loc1) (unsigned-byte-p 64 flags))
      (adt-rec-p
        *fn-lbc-rowwords-schema*
        (list
          (fn-lbc-u64 x0)
          loc0
          loc1
          (fn-lbc-u64 x3)
          (fn-lbc-u64 x4)
          (fn-lbc-u64 x5)
          (fn-lbc-u64 x6)
          (fn-lbc-u64 x7)
          (fn-lbc-u64 x8)
          (fn-lbc-msgid-hash msgid)
          (fn-lbc-u64 x10)
          (fn-lbc-u64 x11)
          (fn-lbc-u64 x12)
          (fn-lbc-u64 x13)
          (fn-lbc-u64 x14)
          flags)))
    :hints
    (("Goal"
       :in-theory
       (e/d (adt-rec-p adt-val-okp fn-locp) (fn-lbc-u64 fn-lbc-msgid-hash unsigned-byte-p))))))

(local
  (defthm
    fn-lbg-directory-record
    (implies
      (and (booleanp b3) (booleanp b14) (booleanp b15) (booleanp b16) (booleanp b18))
      (adt-rec-p
        *fn-lbc-directory-schema*
        (list
          (fn-lbc-u64 x0)
          (fn-lbc-u64 x1)
          (fn-lbc-u64 x2)
          b3
          (fn-lbc-u64 x4)
          (fn-lbc-u64 x5)
          (if q6 1 0)
          (fn-lbc-u64 x7)
          (if q8 1 0)
          (fn-lbc-u64 x9)
          (fn-lbc-u64 x10)
          (fn-lbc-u64 x11)
          (fn-lbc-u64 x12)
          (fn-lbc-u64 x13)
          b14
          b15
          b16
          (fn-lbc-u64 x17)
          b18)))
    :hints
    (("Goal" :in-theory (e/d (adt-rec-p adt-val-okp) (fn-lbc-u64 unsigned-byte-p))))))

(local
  (defthm
    fn-lbg-locator-make-types
    (implies
      (and (unsigned-byte-p 64 seg) (unsigned-byte-p 32 off) (unsigned-byte-p 32 len))
      (fn-locp (mv-nth 0 (fn-loc-make seg off len)) (mv-nth 1 (fn-loc-make seg off len))))
    :hints
    (("Goal"
       :use
       fn-loc-accessors-of-make
       :in-theory
       (disable fn-loc-make fn-locp fn-loc-segment fn-loc-offset fn-loc-len unsigned-byte-p)))))

(local
  (defthm
    fn-lbg-update-loc0-count
    (implies
      (and (fn-lbc-p fn-lbc) (natp k) (< k (fn-lbc-count fn-lbc)) (unsigned-byte-p 64 word))
      (equal (fn-lbc-count (update-fn-lbc-loc0 k word fn-lbc)) (fn-lbc-count fn-lbc)))
    :hints
    (("Goal" :in-theory (e/d (update-fn-lbc-loc0 fn-lbc-count) (fn-lbc-p))))))

(local
  (defthm
    fn-lbg-update-loc0-escape-column
    (equal
      (nth *fn-lbc-escape-store-get* (update-fn-lbc-loc0 k word fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (update-fn-lbc-loc0) (fn-lbc-p))))))

(local
  (defthm
    fn-lbc-escape-cellsp-of-update-loc0
    (implies
      (and (fn-lbc-p fn-lbc) (natp k) (< k (fn-lbc-count fn-lbc)) (unsigned-byte-p 64 word))
      (equal
        (fn-lbc-escape-cellsp i (update-fn-lbc-loc0 k word fn-lbc))
        (fn-lbc-escape-cellsp i fn-lbc)))
    :hints
    (("Goal"
       :use
       ((:instance fn-lbg-escape-extensional (x (update-fn-lbc-loc0 k word fn-lbc)) (y fn-lbc)))
       :in-theory
       (disable
         update-fn-lbc-loc0
         fn-lbc-count
         fn-lbc-p
         fn-lbc-escape-cellsp
         fn-lbc-escape-store-get)))))

(local
  (defthm
    fn-lbg-update-loc1-count
    (implies
      (and (fn-lbc-p fn-lbc) (natp k) (< k (fn-lbc-count fn-lbc)) (unsigned-byte-p 64 word))
      (equal (fn-lbc-count (update-fn-lbc-loc1 k word fn-lbc)) (fn-lbc-count fn-lbc)))
    :hints
    (("Goal" :in-theory (e/d (update-fn-lbc-loc1 fn-lbc-count) (fn-lbc-p))))))

(local
  (defthm
    fn-lbg-update-loc1-escape-column
    (equal
      (nth *fn-lbc-escape-store-get* (update-fn-lbc-loc1 k word fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (update-fn-lbc-loc1) (fn-lbc-p))))))

(local
  (defthm
    fn-lbc-escape-cellsp-of-update-loc1
    (implies
      (and (fn-lbc-p fn-lbc) (natp k) (< k (fn-lbc-count fn-lbc)) (unsigned-byte-p 64 word))
      (equal
        (fn-lbc-escape-cellsp i (update-fn-lbc-loc1 k word fn-lbc))
        (fn-lbc-escape-cellsp i fn-lbc)))
    :hints
    (("Goal"
       :use
       ((:instance fn-lbg-escape-extensional (x (update-fn-lbc-loc1 k word fn-lbc)) (y fn-lbc)))
       :in-theory
       (disable
         update-fn-lbc-loc1
         fn-lbc-count
         fn-lbc-p
         fn-lbc-escape-cellsp
         fn-lbc-escape-store-get)))))

(local
  (defthm
    fn-lbg-value-tree-string
    (implies (stringp x) (fn-lb-value-treep x))
    :hints
    (("Goal" :in-theory (enable fn-lb-value-treep)))))

(local
  (defthm
    fn-lbg-metadata-value-tree
    (implies (fn-record-metadata-bytes-p text) (fn-lb-value-treep text))
    :hints
    (("Goal"
       :in-theory
       (enable fn-record-metadata-bytes-p fn-record-octet-stringp fn-lb-value-treep)))))

(local
  (defthm
    fn-lbg-msgid-pool-append-row-column
    (equal (car (fn-lbc-msgid-pool-append bytes fn-lbc)) (car fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-msgid-pool-append bytes fn-lbc)
       :in-theory
       (e/d (fn-lbc-msgid-pool-append) (fn-lbc-msgid-octets-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-overview-pool-append-row-column
    (equal (car (fn-lbc-overview-pool-append bytes fn-lbc)) (car fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-overview-pool-append bytes fn-lbc)
       :in-theory
       (e/d (fn-lbc-overview-pool-append) (fn-lbc-overview-octets-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-nov-texts-row-column
    (equal (car (fn-lbc-append-nov-texts texts fn-lbc)) (car fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-append-nov-texts texts fn-lbc)
       :in-theory
       (e/d (fn-lbc-append-nov-texts) (fn-lbc-overview-pool-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-memberships-row-column
    (equal (car (fn-lbc-append-memberships items numbersp fn-lbc)) (car fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-append-memberships items numbersp fn-lbc)
       :in-theory
       (e/d
         (fn-lbc-append-memberships)
         (fn-lbc-overview-pool-append fn-lbc-memberships-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-memberships-count-frame
    (equal
      (fn-lbc-count (fn-lbc-append-memberships items numbersp fn-lbc))
      (fn-lbc-count fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-count) (fn-lbc-append-memberships fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-nov-row-column
    (equal (car (fn-lbc-append-nov nov fn-lbc)) (car fn-lbc))
    :hints
    (("Goal"
       :in-theory
       (e/d (fn-lbc-append-nov) (fn-lbc-append-nov-texts fn-lbc-nov-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-nov-count-frame
    (equal (fn-lbc-count (fn-lbc-append-nov nov fn-lbc)) (fn-lbc-count fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-count) (fn-lbc-append-nov fn-lbc-p))))))

(local
  (defthm
    fn-lbg-row-withdrawal-spine
    (implies
      (fn-cat-rowp row)
      (or (consp (fn-held-withdrawn row)) (equal (fn-held-withdrawn row) nil)))
    :hints
    (("Goal"
       :use
       ((:instance fn-cat-rowp-fields (h row))
         (:instance fn-lbg-withdrawn-spine (w (fn-held-withdrawn row))))
       :in-theory
       (disable fn-cat-rowp fn-held-withdrawnp)))))

(local
  (defthm
    fn-lbg-held-bad-atom-countermodel
    (implies
      (bad-atom x)
      (and
        (fn-held-p
          (fn-held-make
            0
            0
            0
            "a"
            0
            nil
            "a"
            "a"
            "a"
            0
            0
            (fn-hf-make 0 nil 0 (list x))
            (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0)
            nil
            nil))
        (not
          (fn-lb-value-treep
            (fn-lb-log-model-homes
              (fn-held-make
                0
                0
                0
                "a"
                0
                nil
                "a"
                "a"
                "a"
                0
                0
                (fn-hf-make 0 nil 0 (list x))
                (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0)
                nil
                nil))))))
    :hints
    (("Goal"
       :in-theory
       (enable
         bad-atom
         fn-held-p
         fn-hf-p
         fn-hc-p
         fn-hc-verdictp
         fn-held-internals
         fn-record-internals
         fn-lb-log-model-homes
         fn-lb-value-treep)))
    :rule-classes
    nil))

(local
  (defthm
    fn-lbg-generic-row-record
    (implies
      (and
        (unsigned-byte-p 64 v0)
        (unsigned-byte-p 64 v1)
        (unsigned-byte-p 64 v2)
        (unsigned-byte-p 64 v3)
        (unsigned-byte-p 64 v4)
        (unsigned-byte-p 64 v5)
        (unsigned-byte-p 64 v6)
        (unsigned-byte-p 64 v7)
        (unsigned-byte-p 64 v8)
        (unsigned-byte-p 64 v9)
        (unsigned-byte-p 64 v10)
        (unsigned-byte-p 64 v11)
        (unsigned-byte-p 64 v12)
        (unsigned-byte-p 64 v13)
        (unsigned-byte-p 64 v14)
        (unsigned-byte-p 64 v15))
      (adt-rec-p
        *fn-lbc-rowwords-schema*
        (list v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)))
    :hints
    (("Goal" :in-theory (enable adt-rec-p adt-val-okp)))))

(local
  (defthm
    fn-lbg-escape-single-end
    (implies
      (and
        (natp n)
        (equal (fn-lbc-count fn-lbc) (+ 1 n))
        (alistp (fn-lbc-escape-store-get n fn-lbc)))
      (fn-lbc-escape-cellsp n fn-lbc))
    :hints
    (("Goal"
       :expand
       ((fn-lbc-escape-cellsp n fn-lbc) (fn-lbc-escape-cellsp (+ 1 n) fn-lbc))
       :in-theory
       (disable fn-lbc-count fn-lbc-escape-store-get fn-lbc-escape-cellsp fn-lbc-p)))))

(local
  (defthm
    fn-lbg-extension-count
    (equal
      (fn-lbc-count
        (fn-lbc-escape-store-put
          (fn-lbc-count fn-lbc)
          cell
          (update-nth *fn-lbc-row-store* (append (car fn-lbc) (list words)) fn-lbc)))
      (+ 1 (fn-lbc-count fn-lbc)))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-count fn-lbc-escape-store-put) (fn-lbc-p))))))

(local
  (defthm
    fn-lbg-extension-cell
    (equal
      (fn-lbc-escape-store-get
        (fn-lbc-count fn-lbc)
        (fn-lbc-escape-store-put
          (fn-lbc-count fn-lbc)
          cell
          (update-nth *fn-lbc-row-store* (append (car fn-lbc) (list words)) fn-lbc)))
      cell)
    :hints
    (("Goal"
       :in-theory
       (e/d (fn-lbc-escape-store-get fn-lbc-escape-store-put) (fn-lbc-count fn-lbc-p))))))

(local
  (defthm
    fn-lbg-extension-old-cell
    (implies
      (not (equal key (fn-lbc-count fn-lbc)))
      (equal
        (fn-lbc-escape-store-get
          key
          (fn-lbc-escape-store-put
            (fn-lbc-count fn-lbc)
            cell
            (update-nth *fn-lbc-row-store* (append (car fn-lbc) (list words)) fn-lbc)))
        (fn-lbc-escape-store-get key fn-lbc)))
    :hints
    (("Goal"
       :in-theory
       (e/d (fn-lbc-escape-store-get fn-lbc-escape-store-put) (fn-lbc-count fn-lbc-p))))))

(local
  (defthm
    fn-lbg-escape-extension-end
    (implies
      (alistp cell)
      (fn-lbc-escape-cellsp
        (fn-lbc-count fn-lbc)
        (fn-lbc-escape-store-put
          (fn-lbc-count fn-lbc)
          cell
          (update-nth *fn-lbc-row-store* (append (car fn-lbc) (list words)) fn-lbc))))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-single-end
          (n (fn-lbc-count fn-lbc))
          (fn-lbc
            (fn-lbc-escape-store-put
              (fn-lbc-count fn-lbc)
              cell
              (update-nth *fn-lbc-row-store* (append (car fn-lbc) (list words)) fn-lbc)))))
       :in-theory
       (disable
         fn-lbc-count
         fn-lbc-escape-store-put
         fn-lbc-escape-store-get
         fn-lbc-escape-cellsp
         fn-lbc-p)))))

(verify-guards fn-lb-home-fields-guardp)

(verify-guards fn-lb-entries-homes-guardp)

(verify-guards fn-lb-log-homes-guardp)

(verify-guards fn-lbc-lc-guardp)

(local
  (defthm
    fn-lbg-homes-entries-lists
    (implies (fn-lb-entries-homes-guardp entries) (true-list-listp (true-list-fix entries)))
    :hints
    (("Goal"
       :induct
       (fn-lb-entries-homes-guardp entries)
       :in-theory
       (e/d (fn-lb-entries-homes-guardp true-list-listp) (fn-lb-home-fields-guardp))))))

(local
  (defthm
    fn-lbg-homes-log-entries
    (implies (fn-lb-log-homes-guardp log) (fn-lb-log-entries-guardp log))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-homes-guardp log)
       :in-theory
       (e/d
         (fn-lb-log-homes-guardp fn-lb-log-entries-guardp)
         (fn-lbg-named-entries fn-lb-entries-homes-guardp always$))))))

(local
  (defthm
    fn-lbg-homes-segment
    (implies
      (fn-lb-log-homes-guardp log)
      (fn-lb-entries-homes-guardp (caddr (fn-lb-log-model-segment seg log))))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-model-segment seg log)
       :in-theory
       (e/d
         (fn-lb-log-model-segment fn-lb-log-homes-guardp)
         (fn-lb-entries-homes-guardp fn-lb-home-fields-guardp))))))

(local
  (defthm
    fn-lbg-homes-selected-entry
    (implies
      (fn-lb-entries-homes-guardp entries)
      (fn-lb-home-fields-guardp (nth 7 (fn-lb-log-model-home-entry position entries))))
    :hints
    (("Goal"
       :induct
       (fn-lb-log-model-home-entry position entries)
       :in-theory
       (e/d (fn-lb-log-model-home-entry fn-lb-entries-homes-guardp) (fn-lb-home-fields-guardp))))))

(defthm
  fn-lbc-lc-guardp-of-update-loc0
  (implies
    (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)) (unsigned-byte-p 64 word))
    (equal
      (fn-lbc-lc-guardp log (update-fn-lbc-loc0 i word fn-lbc))
      (fn-lbc-lc-guardp log fn-lbc)))
  :hints
  (("Goal"
     :in-theory
     (e/d
       (fn-lbc-lc-guardp)
       (update-fn-lbc-loc0 fn-lb-log-homes-guardp fn-lbc-escape-cellsp fn-lbc-count fn-lbc-p)))))

(defthm
  fn-lbc-lc-guardp-of-update-loc1
  (implies
    (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc)) (unsigned-byte-p 64 word))
    (equal
      (fn-lbc-lc-guardp log (update-fn-lbc-loc1 i word fn-lbc))
      (fn-lbc-lc-guardp log fn-lbc)))
  :hints
  (("Goal"
     :in-theory
     (e/d
       (fn-lbc-lc-guardp)
       (update-fn-lbc-loc1 fn-lb-log-homes-guardp fn-lbc-escape-cellsp fn-lbc-count fn-lbc-p)))))

(local
  (defthm
    fn-lbg-number-put-first-row-frame
    (equal (car (fn-lbc-number-put-first group number i fn-lbc)) (car fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-number-put-first) (fn-dmap-put fn-lbc-p))))))

(local
  (defthm
    fn-lbg-number-put-first-escape-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-number-put-first group number i fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-number-put-first) (fn-dmap-put fn-lbc-p))))))

(local
  (defthm
    fn-lbg-number-put-row-seen-row-frame
    (equal (car (fn-lbc-number-put-row-seen numbers seen i fn-lbc)) (car fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-number-put-row-seen numbers seen i fn-lbc)
       :in-theory
       (e/d (fn-lbc-number-put-row-seen) (fn-lbc-number-put-first fn-lbc-p))))))

(local
  (defthm
    fn-lbg-number-put-row-seen-escape-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-number-put-row-seen numbers seen i fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-number-put-row-seen numbers seen i fn-lbc)
       :in-theory
       (e/d (fn-lbc-number-put-row-seen) (fn-lbc-number-put-first fn-lbc-p))))))

(local
  (defthm
    fn-lbg-number-put-row-row-frame
    (equal (car (fn-lbc-number-put-row numbers i fn-lbc)) (car fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-number-put-row) (fn-lbc-number-put-row-seen fn-lbc-p))))))

(local
  (defthm
    fn-lbg-number-put-row-escape-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-number-put-row numbers i fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-number-put-row) (fn-lbc-number-put-row-seen fn-lbc-p))))))

(local
  (defthm
    fn-lbg-reserve-slots-row-frame
    (equal (car (fn-lbc-reserve-slots n fn-lbc)) (car fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-reserve-slots n fn-lbc)
       :in-theory
       (e/d (fn-lbc-reserve-slots) (fn-lbc-msgid-slots-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-reserve-slots-escape-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-reserve-slots n fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-reserve-slots n fn-lbc)
       :in-theory
       (e/d (fn-lbc-reserve-slots) (fn-lbc-msgid-slots-append fn-lbc-p))))))

(local
  (defthm
    fn-lbg-slot-insert-row-frame
    (equal (car (fn-lbc-slot-insert i slot fuel fn-lbc)) (car fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-slot-insert i slot fuel fn-lbc)
       :in-theory
       (e/d (fn-lbc-slot-insert) (fn-lbc-msgid-slots-set-word fn-lbc-slot-word fn-lbc-p))))))

(local
  (defthm
    fn-lbg-slot-insert-escape-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-slot-insert i slot fuel fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-slot-insert i slot fuel fn-lbc)
       :in-theory
       (e/d (fn-lbc-slot-insert) (fn-lbc-msgid-slots-set-word fn-lbc-slot-word fn-lbc-p))))))

(local
  (defthm
    fn-lbg-index-slots-row-frame
    (equal (car (fn-lbc-index-slots i n fn-lbc)) (car fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-index-slots i n fn-lbc)
       :in-theory
       (e/d (fn-lbc-index-slots) (fn-lbc-slot-insert fn-lbc-p))))))

(local
  (defthm
    fn-lbg-index-slots-escape-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-index-slots i n fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-index-slots i n fn-lbc)
       :in-theory
       (e/d (fn-lbc-index-slots) (fn-lbc-slot-insert fn-lbc-p))))))

(local
  (defthm
    fn-lbg-escape-outside-count
    (implies
      (or (not (natp start)) (<= (fn-lbc-count fn-lbc) start))
      (fn-lbc-escape-cellsp start fn-lbc))
    :hints
    (("Goal"
       :expand
       ((fn-lbc-escape-cellsp start fn-lbc))
       :in-theory
       (disable fn-lbc-escape-cellsp fn-lbc-count fn-lbc-p)))))

(local
  (defthm
    fn-lbg-escape-extension-prefix
    (implies
      (and
        (natp start)
        (<= start (fn-lbc-count fn-lbc))
        (fn-lbc-escape-cellsp start fn-lbc)
        (alistp cell))
      (fn-lbc-escape-cellsp
        start
        (fn-lbc-escape-store-put
          (fn-lbc-count fn-lbc)
          cell
          (update-nth *fn-lbc-row-store* (append (car fn-lbc) (list words)) fn-lbc))))
    :hints
    (("Goal"
       :induct
       (fn-lbc-escape-cellsp start fn-lbc)
       :expand
       ((fn-lbc-escape-cellsp start fn-lbc)
         (fn-lbc-escape-cellsp
           start
           (fn-lbc-escape-store-put
             (fn-lbc-count fn-lbc)
             cell
             (update-nth *fn-lbc-row-store* (append (car fn-lbc) (list words)) fn-lbc))))
       :in-theory
       (e/d
         ((:induction fn-lbc-escape-cellsp))
         ((:definition fn-lbc-escape-cellsp)
           update-nth
           fn-lbc-count
           fn-lbc-escape-store-get
           fn-lbc-escape-store-put
           fn-lbc-p))))))

(local
  (defthm
    fn-lbg-summary-put-row-frame
    (equal (car (fn-lbc-summary-put group value next fn-lbc)) (car fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-summary-put) (fn-dmap-put fn-lbc-p))))))

(local
  (defthm
    fn-lbg-append-memberships-escape-frame
    (equal
      (fn-lbc-escape-cellsp i (fn-lbc-append-memberships items numbersp fn-lbc))
      (fn-lbc-escape-cellsp i fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (x (fn-lbc-append-memberships items numbersp fn-lbc))
          (y fn-lbc)))
       :in-theory
       (disable
         fn-lbc-escape-cellsp
         fn-lbc-count
         fn-lbc-escape-store-get
         fn-lbc-append-memberships
         fn-lbc-p)))))

(local
  (defthm
    fn-lbg-append-nov-escape-frame
    (equal
      (fn-lbc-escape-cellsp i (fn-lbc-append-nov nov fn-lbc))
      (fn-lbc-escape-cellsp i fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance fn-lbg-escape-extensional (x (fn-lbc-append-nov nov fn-lbc)) (y fn-lbc)))
       :in-theory
       (disable
         fn-lbc-escape-cellsp
         fn-lbc-count
         fn-lbc-escape-store-get
         fn-lbc-append-nov
         fn-lbc-p)))))

(verify-guards
  fn-lbc-append-row
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-row-withdrawal-spine)
       (:instance
         fn-lbg-locator-make-types
         (seg (fn-lb-log-model-payload-segment (fn-record-payload row) log))
         (off (nth 3 (fn-lb-log-model-payload-entry (fn-record-payload row) log)))
         (len (nth 4 (fn-lb-log-model-payload-entry (fn-record-payload row) log))))
       (:instance fn-lbg-row-log-widths)
       (:instance fn-cat-rowp-fields (h row))
       (:instance fn-lbg-escape-select (start 0) (i (- (fn-lbc-count fn-lbc) 1)))
       (:instance
         fn-lbg-hnov-small
         (nov (fn-hnov-of (nth 6 (fn-lb-log-model-payload-entry (fn-record-payload row) log))))))
     :in-theory
     (disable
       fn-held-withdrawnp
       fn-rcl-tombstonep
       fn-arx-entry-ok
       fn-hnov-p
       fn-hnov-ok
       fn-hnov-tomb
       fn-hf-nov
       fn-record-string-octets
       fn-nntp-framed-of-bytes
       fn-nntp-split-article
       fn-nntp-split-head
       fn-lbc-escape-store-get
       unsigned-byte-p
       fn-nntp-stuffed-section
       fn-lb-log-model-wire
       fn-la-payload-wire
       fn-la-tombstone-raw
       fn-lb-log-model-homes
       fn-lb-log-model-nat-octets
       fn-lb-log-model-text-octets
       fn-lb-value-treep
       fn-lb-log-model-value-octets
       fn-lb-log-model-home-frame
       fn-lb-log-model-entryp
       fn-lb-log-model-entriesp
       fn-lb-log-model-segsp
       fn-lb-log-entries-guardp
       fn-lb-log-read-guardp
       fn-lb-log-append-guardp
       fn-lb-log-model-segment
       fn-lb-log-model-entry
       fn-lb-log-model-read-range
       fn-lb-log-model-home-entry
       fn-lb-log-model-read-home-frame
       fn-lb-log-model-handle-entry
       fn-lb-log-model-payload-entry
       fn-lb-log-model-payload-segment
       fn-lb-log-payload
       fn-lb-entry-protected-len
       fn-lb-entry-octets
       fn-lb-log-model-pre
       fn-lb-log-model-append-to-segment
       fn-lb-log-model-append
       fn-lb-log-model-recycle
       fn-lb-arena-is-log
       fn-lbc-count
       fn-lbc-escape-cellsp
       fn-lbc-number-escape-cellsp
       fn-lbc-stamp-escape-cellsp
       fn-lbc-loc0
       fn-lbc-loc1
       update-fn-lbc-loc0
       update-fn-lbc-loc1
       fn-lbc-word
       fn-lbc-directory-field
       fn-lbc-membership-field
       fn-lbc-nov-field
       fn-lbc-msgid-pool-count
       fn-lbc-msgid-pool-octet
       fn-lbc-msgid-pool-range
       fn-lbc-msgid-pool-append
       fn-lbc-overview-pool-count
       fn-lbc-overview-pool-octet
       fn-lbc-overview-pool-range
       fn-lbc-overview-pool-append
       fn-lbc-clear-columns
       fn-lbc-escape
       fn-lbc-value
       fn-lbc-directory-value
       fn-lbc-msgid
       fn-lbc-flag
       fn-lbc-withdrawn
       fn-lbc-membership-group
       fn-lbc-membership-run
       fn-lbc-groups
       fn-lbc-numbers
       fn-lbc-nov-text
       fn-lbc-nov-at
       fn-lbc-original-nov
       fn-lbc-render-nov
       fn-cat-served-projection
       fn-lbc-served-row
       fn-lbc-home-entry
       fn-lbc-restore-control
       fn-lbc-home-guardp
       fn-lbc-at
       fn-lbc-u64
       fn-lbc-sparse-u64
       fn-lbc-text-smallp
       fn-lbc-nov-smallp
       fn-lbc-numbers-smallp
       fn-lbc-nov-record-count
       fn-lbc-membership-record-count
       fn-lbc-append-nov-texts
       fn-lbc-nov-spans
       fn-lbc-append-nov
       fn-lbc-append-memberships
       fn-lbc-msgid-hash-octets
       fn-lbc-msgid-hash
       fn-lbc-row-log-guardp
       fn-lbc-rows-log-guardp
       fn-lbc-row-homes-guardp
       fn-lbc-append-row
       fn-lbc-visiblep
       lb-prefix-max
       lb-first-at-least
       lb-keep-from
       fn-lbc-first-reaching
       fn-lbc-newnews-candidatep
       fn-lbc-newnews-tail
       fn-lbc-newnews-range
       fn-lbc-stored-range
       fn-lbc-number-get
       fn-lbc-number-put-first
       fn-lbc-number-put-row-seen
       fn-lbc-number-put-row
       fn-lbc-summary-word
       fn-lbc-live-summary
       fn-lbc-summary-put
       fn-lbc-number-group-keys
       fn-lbc-row-group-keys
       fn-lbc-rebuild-summaries
       fn-lbc-rebuild-rows
       fn-lbc-slot-count
       fn-lbc-slot-word
       fn-lbc-reserve-slots
       fn-lbc-slot-insert
       fn-lbc-index-slots
       fn-lbc-msgid-probe
       fn-lbc-msgid-seqs
       fn-lbc-open-rebuild
       fn-lbc-row-corr
       fn-lbc-rows-corr
       fn-lbc-summaries-corr
       fn-lbc-summary-cells-corr
       fn-lbc-number-cells-corr
       fn-lbc-p
       floor
       mod
       always$
       fn-hnov-of
       fn-nntp-stuffed-section
       fn-nntp-section-of-bytes
       fn-loc-make))))

(local
  (defthm
    fn-lbg-homes-all-locators
    (implies (fn-lb-log-homes-guardp log) (fn-lbc-home-guardp i fn-lbc log))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-homes-segment
          (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))))
         (:instance
           fn-lbg-homes-selected-entry
           (entries
             (caddr
               (fn-lb-log-model-segment
                 (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))
                 log)))
           (position
             (+
               (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))
               (fn-loc-len (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))))))
       :in-theory
       (e/d
         (fn-lbc-home-guardp fn-lbc-home-entry fn-lb-home-fields-guardp)
         (fn-lbg-homes-selected-entry
           fn-lbg-homes-segment
           fn-lb-log-homes-guardp
           fn-lb-log-model-segment
           fn-lb-log-model-home-entry
           fn-lbc-loc0
           fn-lbc-loc1
           fn-loc-segment
           fn-loc-offset
           fn-loc-len))))))

(verify-guards
  fn-lc-bound-row
  :hints
  (("Goal"
     :use
     ((:instance fn-lbg-escape-select (start 0)))
     :in-theory
     (e/d
       (fn-lbc-lc-guardp fn-lc-count)
       (fn-lbc-at
         fn-lbc-escape-cellsp
         fn-lbc-p
         fn-lbc-count
         fn-lbc-home-guardp
         fn-lb-log-homes-guardp
         fn-lbc-escape-store-get
         always$
         fn-lbg-named-entries)))))

(local
  (defthm
    fn-lbg-escape-extension-flexible
    (implies
      (and
        (equal n (fn-lbc-count fn-lbc))
        (equal rows (car fn-lbc))
        (natp start)
        (<= start n)
        (fn-lbc-escape-cellsp start fn-lbc)
        (alistp cell))
      (fn-lbc-escape-cellsp
        start
        (fn-lbc-escape-store-put
          n
          cell
          (update-nth *fn-lbc-row-store* (append rows (list words)) fn-lbc))))
    :hints
    (("Goal"
       :use
       fn-lbg-escape-extension-prefix
       :in-theory
       (disable
         fn-lbc-count
         fn-lbc-escape-cellsp
         fn-lbc-escape-store-put
         fn-lbc-escape-store-get
         fn-lbc-p
         update-nth)))))

(local
  (defthm
    fn-lbg-summary-put-escape-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-summary-put group value next fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal" :in-theory (e/d (fn-lbc-summary-put) (fn-dmap-put fn-lbc-p))))))

(local
  (defthm
    fn-lbg-escape-put-other-field
    (implies
      (and (natp field) (< 0 field) (not (equal field *fn-lbc-escape-store-get*)))
      (equal
        (fn-lbc-escape-cellsp
          i
          (fn-lbc-escape-store-put key cell (update-nth field value fn-lbc)))
        (fn-lbc-escape-cellsp i (fn-lbc-escape-store-put key cell fn-lbc))))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (x (fn-lbc-escape-store-put key cell (update-nth field value fn-lbc)))
          (y (fn-lbc-escape-store-put key cell fn-lbc))))
       :in-theory
       (e/d
         (fn-lbc-count fn-lbc-escape-store-put)
         (fn-lbc-p fn-lbc-escape-cellsp fn-lbc-escape-store-get))))))

(local
  (defthm
    fn-lbg-count-by-car
    (equal (fn-lbc-count fn-lbc) (len (car fn-lbc)))
    :hints
    (("Goal" :cases ((consp fn-lbc)) :in-theory (enable fn-lbc-count)))))

(local
  (defthm
    fn-lbg-number-put-first-recognizer-frame
    (equal
      (fn-lbc-escape-cellsp j (fn-lbc-number-put-first group number i fn-lbc))
      (fn-lbc-escape-cellsp j fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (i j)
          (x (fn-lbc-number-put-first group number i fn-lbc))
          (y fn-lbc)))
       :in-theory
       (e/d
         (fn-lbc-count)
         (fn-lbc-number-put-first fn-lbc-escape-cellsp fn-lbc-escape-store-get fn-lbc-p))))))

(local
  (defthm
    fn-lbg-number-put-row-seen-recognizer-frame
    (equal
      (fn-lbc-escape-cellsp j (fn-lbc-number-put-row-seen numbers seen i fn-lbc))
      (fn-lbc-escape-cellsp j fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (i j)
          (x (fn-lbc-number-put-row-seen numbers seen i fn-lbc))
          (y fn-lbc)))
       :in-theory
       (e/d
         (fn-lbc-count)
         (fn-lbc-number-put-row-seen fn-lbc-escape-cellsp fn-lbc-escape-store-get fn-lbc-p))))))

(local
  (defthm
    fn-lbg-number-put-row-recognizer-frame
    (equal
      (fn-lbc-escape-cellsp j (fn-lbc-number-put-row numbers i fn-lbc))
      (fn-lbc-escape-cellsp j fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (i j)
          (x (fn-lbc-number-put-row numbers i fn-lbc))
          (y fn-lbc)))
       :in-theory
       (e/d
         (fn-lbc-count)
         (fn-lbc-number-put-row fn-lbc-escape-cellsp fn-lbc-escape-store-get fn-lbc-p))))))

(local
  (defthm
    fn-lbg-reserve-slots-recognizer-frame
    (equal
      (fn-lbc-escape-cellsp j (fn-lbc-reserve-slots n fn-lbc))
      (fn-lbc-escape-cellsp j fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (i j)
          (x (fn-lbc-reserve-slots n fn-lbc))
          (y fn-lbc)))
       :in-theory
       (e/d
         (fn-lbc-count)
         (fn-lbc-reserve-slots fn-lbc-escape-cellsp fn-lbc-escape-store-get fn-lbc-p))))))

(local
  (defthm
    fn-lbg-slot-insert-recognizer-frame
    (equal
      (fn-lbc-escape-cellsp j (fn-lbc-slot-insert i slot fuel fn-lbc))
      (fn-lbc-escape-cellsp j fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (i j)
          (x (fn-lbc-slot-insert i slot fuel fn-lbc))
          (y fn-lbc)))
       :in-theory
       (e/d
         (fn-lbc-count)
         (fn-lbc-slot-insert fn-lbc-escape-cellsp fn-lbc-escape-store-get fn-lbc-p))))))

(local
  (defthm
    fn-lbg-index-slots-recognizer-frame
    (equal
      (fn-lbc-escape-cellsp j (fn-lbc-index-slots i n fn-lbc))
      (fn-lbc-escape-cellsp j fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (i j)
          (x (fn-lbc-index-slots i n fn-lbc))
          (y fn-lbc)))
       :in-theory
       (e/d
         (fn-lbc-count)
         (fn-lbc-index-slots fn-lbc-escape-cellsp fn-lbc-escape-store-get fn-lbc-p))))))

(local
  (defthm
    fn-lbg-summary-put-recognizer-frame
    (equal
      (fn-lbc-escape-cellsp j (fn-lbc-summary-put group value next fn-lbc))
      (fn-lbc-escape-cellsp j fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (i j)
          (x (fn-lbc-summary-put group value next fn-lbc))
          (y fn-lbc)))
       :in-theory
       (e/d
         (fn-lbc-count)
         (fn-lbc-summary-put fn-lbc-escape-cellsp fn-lbc-escape-store-get fn-lbc-p))))))

(local
  (defthm
    fn-lbg-rebuild-summaries-row-frame
    (equal (car (fn-lbc-rebuild-summaries groups rows fn-lbc)) (car fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-rebuild-summaries groups rows fn-lbc)
       :in-theory
       (e/d (fn-lbc-rebuild-summaries) (fn-lbc-summary-put fn-lbc-p))))))

(local
  (defthm
    fn-lbg-rebuild-summaries-escape-frame
    (equal
      (nth *fn-lbc-escape-store-get* (fn-lbc-rebuild-summaries groups rows fn-lbc))
      (nth *fn-lbc-escape-store-get* fn-lbc))
    :hints
    (("Goal"
       :induct
       (fn-lbc-rebuild-summaries groups rows fn-lbc)
       :in-theory
       (e/d (fn-lbc-rebuild-summaries) (fn-lbc-summary-put fn-lbc-p))))))

(local
  (defthm
    fn-lbg-rebuild-summaries-recognizer-frame
    (equal
      (fn-lbc-escape-cellsp j (fn-lbc-rebuild-summaries groups rows fn-lbc))
      (fn-lbc-escape-cellsp j fn-lbc))
    :hints
    (("Goal"
       :use
       ((:instance
          fn-lbg-escape-extensional
          (i j)
          (x (fn-lbc-rebuild-summaries groups rows fn-lbc))
          (y fn-lbc)))
       :in-theory
       (e/d
         (fn-lbc-count)
         (fn-lbc-rebuild-summaries fn-lbc-escape-cellsp fn-lbc-escape-store-get fn-lbc-p))))))

(local
  (defthm
    fn-lbg-alist-append
    (implies (and (alistp a) (alistp b)) (alistp (append a b)))
    :hints
    (("Goal" :induct (append a b) :in-theory (enable alistp append)))))

(local
  (defthm
    fn-lbg-row-nth-by-car
    (equal (nth *fn-lbc-row-store* fn-lbc) (car fn-lbc))
    :hints
    (("Goal" :in-theory (enable nth)))))

(local
  (defthm
    fn-lbc-escape-cellsp-of-append-row
    (implies
      (fn-lbc-escape-cellsp 0 fn-lbc)
      (fn-lbc-escape-cellsp 0 (fn-lbc-append-row row log fn-lbc)))
    :hints
    (("Goal"
       :in-theory
       '(fn-lbc-append-row update-fn-lbc-row-store update-fn-lbc-directory-store fn-lbc-row-store fn-lbc-directory-store fn-lbc-rowwords-append-is-append fn-lbc-directory-append-is-append fn-lbg-escape-put-other-field fn-lbg-escape-frame-update fn-lbg-escape-extension-flexible fn-lbg-alist-append fn-lbg-sparse-alist alistp fn-lbg-row-nth-by-car fn-lbg-count-by-car fn-lbg-msgid-pool-append-count-frame fn-lbg-msgid-pool-append-row-column fn-lbg-msgid-pool-append-escape-frame fn-lbg-overview-pool-append-count-frame fn-lbg-overview-pool-append-row-column fn-lbg-overview-pool-append-escape-frame fn-lbg-append-nov-texts-count-frame fn-lbg-append-nov-texts-row-column fn-lbg-append-nov-texts-escape-frame fn-lbg-append-memberships-count-frame fn-lbg-append-memberships-row-column fn-lbg-append-memberships-escape-frame fn-lbg-append-nov-count-frame fn-lbg-append-nov-row-column fn-lbg-append-nov-escape-frame (:executable-counterpart equal) (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart <) (:executable-counterpart natp) (:executable-counterpart not) (:type-prescription len) (:type-prescription fn-lbc-count) (:type-prescription alistp) car-cons cdr-cons)))))

(local
  (defthm
    fn-lbc-escape-cellsp-of-rebuild-rows
    (implies
      (fn-lbc-escape-cellsp 0 fn-lbc)
      (fn-lbc-escape-cellsp 0 (fn-lbc-rebuild-rows rows log fn-lbc)))
    :hints
    (("Goal"
       :induct
       (fn-lbc-rebuild-rows rows log fn-lbc)
       :in-theory
       (e/d
         (fn-lbc-rebuild-rows)
         (fn-lbc-append-row fn-lbc-number-put-row fn-lbc-count fn-lbc-escape-cellsp fn-lbc-p))))))

(defthm
  fn-lbc-lc-guardp-of-open-rebuild
  (implies
    (fn-lb-log-homes-guardp log)
    (fn-lbc-lc-guardp log (fn-lbc-open-rebuild rows log fn-lbc)))
  :hints
  (("Goal"
     :in-theory
     (e/d
       (fn-lbc-open-rebuild fn-lbc-lc-guardp)
       (fn-lbc-clear-columns
         fn-lbc-rebuild-rows
         fn-lbc-rebuild-summaries
         fn-lbc-index-slots
         fn-lbc-reserve-slots
         fn-lbc-count
         fn-lbc-escape-cellsp
         fn-lbc-p
         fn-lb-log-homes-guardp)))))

(verify-guards
  fn-lbc-rebuild-rows
  :hints
  (("Goal"
     :in-theory
     (e/d
       (fn-lbc-rows-log-guardp)
       (fn-lbc-append-row
         fn-lbc-row-log-guardp
         fn-lb-log-read-guardp
         fn-lbc-p
         fn-lbc-count
         fn-lbc-escape-cellsp
         fn-lbg-named-read
         always$)))))

(verify-guards
  fn-lbc-open-rebuild
  :hints
  (("Goal"
     :in-theory
     (disable
       fn-lbc-clear-columns
       fn-lbc-rebuild-rows
       fn-lbc-p
       fn-lbc-count
       fn-lbc-escape-cellsp
       fn-lbc-rebuild-summaries
       fn-lbc-reserve-slots
       fn-lbc-index-slots
       fn-lb-log-homes-guardp
       fn-lbc-rows-log-guardp
       fn-lb-log-read-guardp
       fn-lbg-named-read
       always$))))

; Resume 4: value-tree closure of saved homes across reconstruction.

(local
 (defthm fn-lbg-tree-car (implies (fn-lb-value-treep x) (fn-lb-value-treep (car x))) :hints (("Goal" :in-theory (enable fn-lb-value-treep))))
)

(local
 (defthm fn-lbg-tree-cdr (implies (fn-lb-value-treep x) (fn-lb-value-treep (cdr x))) :hints (("Goal" :in-theory (enable fn-lb-value-treep))))
)

(local
 (defthm fn-lbg-tree-nth (implies (fn-lb-value-treep x) (fn-lb-value-treep (nth n x))) :hints (("Goal" :induct (nth n x) :in-theory (enable nth fn-lb-value-treep))))
)

(local
 (defthm fn-lbg-tree-truefix (implies (fn-lb-value-treep x) (fn-lb-value-treep (true-list-fix x))) :hints (("Goal" :induct (true-list-fix x) :in-theory (enable true-list-fix fn-lb-value-treep))))
)

(local
 (defthm fn-lbg-tree-take (implies (fn-lb-value-treep x) (fn-lb-value-treep (take n x))) :hints (("Goal" :induct (take n x) :in-theory (enable take fn-lb-value-treep))))
)

(local
 (defthm fn-lbg-tree-nthcdr (implies (fn-lb-value-treep x) (fn-lb-value-treep (nthcdr n x))) :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr fn-lb-value-treep))))
)

(local
 (defthm fn-lbg-prefix3-shape (implies (and (true-listp x) (equal (len x) 3)) (equal x (list (car x) (cadr x) (caddr x)))) :rule-classes nil :hints (("Goal" :in-theory (enable len true-listp))))
)

(local
 (defthm fn-lbg-restored-control-home-tree
  (implies (fn-lb-home-fields-guardp homes)
   (let ((control (true-list-fix (fn-lbc-restore-control (nth 4 homes) nov))))
    (fn-lb-value-treep (list (len control) (take (min 3 (len control)) control) (nthcdr 4 control)))))
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-lbg-prefix3-shape (x (cadr (nth 4 homes)))))
   :in-theory (e/d (fn-lb-home-fields-guardp fn-lbc-restore-control fn-lb-value-treep)
    ()))))
)

(local
 (defthm fn-lbg-home-field-trees
  (implies (fn-lb-home-fields-guardp homes) (fn-lb-value-treep homes))
  :hints (("Goal" :in-theory (enable fn-lb-home-fields-guardp))))
)

(local
 (defthm fn-lbg-at-home-tree
  (implies (fn-lb-home-fields-guardp (nth 7 (fn-lbc-home-entry i fn-lbc log)))
           (fn-lb-value-treep (fn-lb-log-model-homes (fn-lbc-at i fn-lbc log))))
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-lbg-restored-control-home-tree
    (homes (nth 7 (fn-lbc-home-entry i fn-lbc log)))
    (nov (nth 3 (nth 6 (fn-lbc-served-row i fn-lbc))))))
   :in-theory (e/d (fn-lbc-at fn-lb-log-model-homes fn-lb-value-treep)
    (fn-lbc-served-row fn-lbc-home-entry fn-lbc-restore-control fn-held-make fn-hf-make fn-lb-home-fields-guardp fn-lbg-restored-control-home-tree)))))
)

(local
 (defthm fn-lbg-lc-at-tree
  (implies (fn-lbc-lc-guardp log fn-lbc)
           (fn-lb-value-treep (fn-lb-log-model-homes (fn-lbc-at i fn-lbc log))))
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-lbg-homes-segment
    (seg (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))))
    (:instance fn-lbg-homes-selected-entry
     (entries (caddr (fn-lb-log-model-segment (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)) log)))
     (position (+ (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)) (fn-loc-len (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))))))
   :in-theory (e/d (fn-lbc-lc-guardp fn-lbc-home-entry)
    (fn-lbg-homes-segment fn-lbg-homes-selected-entry fn-lb-log-homes-guardp fn-lb-entries-homes-guardp fn-lb-home-fields-guardp fn-lb-value-treep fn-lb-log-model-homes fn-lbc-at fn-lbc-escape-cellsp fn-lbc-loc0 fn-lbc-loc1 fn-lb-log-model-segment fn-lb-log-model-home-entry fn-loc-segment fn-loc-offset fn-loc-len)))))
)

(local
 (defthm fn-lbg-model-home-fields-domain
  (implies (fn-lb-value-treep (fn-lb-log-model-homes row))
           (fn-lb-home-fields-guardp (fn-lb-log-model-homes row)))
  :hints (("Goal" :do-not-induct t
   :in-theory (enable fn-lb-home-fields-guardp fn-lb-log-model-homes))))
)

(verify-guards fn-lc-expected-home-frame
 :hints (("Goal" :in-theory (disable fn-held-p fn-lb-log-model-homes fn-lb-value-treep fn-lb-log-model-home-frame))))

(verify-guards fn-lc-locator-resolves
 :hints (("Goal" :in-theory
  (e/d (fn-lc-bound-row fn-lc-count fn-lc-segsp)
       (fn-lbc-at fn-lb-log-model-homes fn-lb-value-treep fn-held-p fn-lbc-p fn-lbc-lc-guardp fn-lbc-count fn-lc-read-range fn-lc-read-home-frame fn-lb-log-payload fn-lc-expected-range fn-lc-expected-home-frame fn-lc-home-position fn-lbc-loc0 fn-lbc-loc1 fn-locp fn-lb-log-model-segsp fn-lb-log-homes-guardp fn-lbc-escape-cellsp always$ fn-lbg-named-entries fn-lbg-named-read)))))

(verify-guards fn-lc-resolve-from
 :hints (("Goal" :in-theory (e/d (fn-lc-count) (fn-lc-locator-resolves fn-lbc-lc-guardp fn-lc-segsp fn-lbc-p fn-lbc-count)))))

(verify-guards fn-lc-locators-resolve
 :hints (("Goal" :in-theory (e/d (fn-lc-count) (fn-lc-resolve-from fn-lbc-lc-guardp fn-lc-segsp fn-lbc-p fn-lbc-count)))))
