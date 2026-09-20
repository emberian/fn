; fn: the incremental statement index, and the durable equivocation record.
;
; specs/substrate-transport.md sections 2.1 and 2.3, keystone S3-3 (packet S3).
;
; fn-stx-lace is linear in the store and must never run on a served path
; (D3, no whole-state revalidation).  The executable node carries this index
; instead: three alists, each extended by at most one cons per accepted
; article, in the pattern of peering's history index.  The licence for using
; it in place of the projection is fn-stx-index-agrees-with-lace; the licence
; for carrying it across a transition is
; fn-stx-index-invariant-preserved-by-accept.
;
; The (:equivocation creator incarnation sequence id-held id-new) values of
; section 2.3 are the index's third list.  They are a DISCOVERY AID with a
; proved agreement, never an independent authority: if a record and the lace
; disagreed the lace would win, because the lace is the articles -- and
; fn-stx-recorded-equivocation-agrees-with-lace is what stops them
; disagreeing.

(in-package "ACL2")
(include-book "stx-lace")

(local (in-theory (enable (:d fn-lace-same-slotp) (:d fn-lace-slot-conflictp)
                          (:d fn-lace-equivocatorp))))

(local (defthm fn-stx-index-stmt-is-consp
         (implies (fn-stmt-p s) (consp s))
         :hints (("Goal" :in-theory (enable fn-stmt-p)))))

; -----------------------------------------------------------------------------
; Slot keys

(defun fn-stx-slot-key (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (list (fn-stmt-creator s) (fn-stmt-incarnation s) (fn-stmt-sequence s)))

(defthm fn-stx-slot-key-equal-is-same-slotp
  (iff (equal (fn-stx-slot-key a) (fn-stx-slot-key b))
       (fn-lace-same-slotp a b)))

(in-theory (disable (:d fn-stx-slot-key)))

; -----------------------------------------------------------------------------
; The lace-side twins of the three queries (proof level only)

(defun fn-stx-lace-slot-first (lace k)
  (declare (xargs :guard (fn-lace-p lace)))
  (if (consp lace)
      (if (equal (fn-stx-slot-key (car lace)) k)
          (car lace)
        (fn-stx-lace-slot-first (cdr lace) k))
    nil))

(defthm fn-stx-lace-slot-first-is-member
  (implies (fn-stx-lace-slot-first lace k)
           (member-equal (fn-stx-lace-slot-first lace k) lace)))

(defthm fn-stx-lace-slot-first-key
  (implies (fn-stx-lace-slot-first lace k)
           (equal (fn-stx-slot-key (fn-stx-lace-slot-first lace k)) k)))

(defthm fn-stx-lace-slot-first-of-member
  (implies (and (fn-lace-p lace)
                (member-equal x lace)
                (equal (fn-stx-slot-key x) k))
           (fn-stx-lace-slot-first lace k)))

; The witness behind fn-lace-slot-conflictp: the first statement of the lace
; that sits in s's slot and is not s.
(defun fn-stx-slot-partner (lace s)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-stmt-p s))))
  (if (consp lace)
      (if (and (not (equal (car lace) s))
               (fn-lace-same-slotp (car lace) s))
          (car lace)
        (fn-stx-slot-partner (cdr lace) s))
    nil))

(local (defthm fn-stx-slot-partner-is-member
         (implies (fn-lace-slot-conflictp s lace)
                  (member-equal (fn-stx-slot-partner lace s) lace))
         :hints (("Goal" :induct (fn-stx-slot-partner lace s)
                  :in-theory (e/d ((:d fn-lace-slot-conflictp))
                                  ((:d fn-lace-same-slotp)))))))

(local (defthm fn-stx-slot-partner-differs
         (implies (fn-lace-slot-conflictp s lace)
                  (not (equal (fn-stx-slot-partner lace s) s)))
         :hints (("Goal" :induct (fn-stx-slot-partner lace s)
                  :in-theory (e/d ((:d fn-lace-slot-conflictp))
                                  ((:d fn-lace-same-slotp)))))))

(local (defthm fn-stx-slot-partner-same-slot
         (implies (fn-lace-slot-conflictp s lace)
                  (fn-lace-same-slotp (fn-stx-slot-partner lace s) s))
         :hints (("Goal" :induct (fn-stx-slot-partner lace s)
                  :in-theory (e/d ((:d fn-lace-slot-conflictp))
                                  ((:d fn-lace-same-slotp)))))))

(defthm fn-stx-slot-partner-elim
  (implies (fn-lace-slot-conflictp s lace)
           (and (member-equal (fn-stx-slot-partner lace s) lace)
                (not (equal (fn-stx-slot-partner lace s) s))
                (fn-lace-same-slotp (fn-stx-slot-partner lace s) s)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-stx-slot-partner (:d fn-lace-slot-conflictp)
                               (:d fn-lace-same-slotp)))))

(defthm fn-stx-slot-conflictp-implies-slot-first
  (implies (and (fn-lace-p lace) (fn-lace-slot-conflictp s lace))
           (fn-stx-lace-slot-first lace (fn-stx-slot-key s)))
  :hints (("Goal"
           :use ((:instance fn-stx-slot-partner-elim)
                 (:instance fn-stx-lace-slot-first-of-member
                            (x (fn-stx-slot-partner lace s))
                            (k (fn-stx-slot-key s))))
           :in-theory (disable fn-stx-slot-partner-elim
                               fn-stx-lace-slot-first-of-member
                               fn-stx-slot-partner
                               (:d fn-lace-slot-conflictp)))))

; -----------------------------------------------------------------------------
; The two facts about a one-statement extension of a lace

(local (defthm fn-stx-slot-conflictp-of-append
         (iff (fn-lace-slot-conflictp s (append a b))
              (or (fn-lace-slot-conflictp s a)
                  (fn-lace-slot-conflictp s b)))))

(local (defthm fn-stx-scan-of-append-rest
         (iff (fn-lace-equivocator-scan (append a b) m p i)
              (or (fn-lace-equivocator-scan a m p i)
                  (fn-lace-equivocator-scan b m p i)))))

(local (defthm fn-stx-subsetp-equal-cons
         (implies (subsetp-equal a b)
                  (subsetp-equal a (cons x b)))))

(local (defthm fn-stx-subsetp-equal-reflexive
         (subsetp-equal x x)))

(local (defthm fn-stx-slot-conflictp-of-nil
         (not (fn-lace-slot-conflictp s nil))
         :hints (("Goal" :in-theory (enable (:d fn-lace-slot-conflictp))))))

(local (defthm fn-stx-slot-conflictp-of-singleton
         (iff (fn-lace-slot-conflictp x (list s))
              (and (not (equal s x)) (fn-lace-same-slotp s x)))
         :hints (("Goal" :in-theory (enable (:d fn-lace-slot-conflictp)
                                            (:d fn-lace-same-slotp))))))

(local (defthm fn-stx-scan-of-bigger-lace
         (implies (and (subsetp-equal rest lace)
                       (fn-lace-equivocator-scan rest (append lace (list s)) p i))
                  (or (fn-lace-equivocator-scan rest lace p i)
                      (and (equal (fn-stmt-creator s) p)
                           (equal (fn-stmt-incarnation s) i)
                           (fn-lace-slot-conflictp s lace))))
         :rule-classes nil
         :hints (("Goal" :induct (fn-lace-equivocator-scan rest lace p i)
                  :in-theory (e/d ((:d fn-lace-equivocator-scan)
                                   (:d fn-lace-same-slotp)
                                   fn-stx-slot-conflictp-of-singleton
                                   fn-lace-slot-conflictp-intro)
                                  ((:d fn-lace-slot-conflictp)))))))

(defthm fn-stx-equivocatorp-of-one-more
  (implies (fn-lace-p lace)
           (iff (fn-lace-equivocatorp (append lace (list s)) p i)
                (or (fn-lace-equivocatorp lace p i)
                    (and (equal (fn-stmt-creator s) p)
                         (equal (fn-stmt-incarnation s) i)
                         (fn-lace-slot-conflictp s lace)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-stx-scan-of-bigger-lace (rest lace))
                 (:instance fn-lace-equivocator-scan-monotone-rest
                            (rest lace) (lace (append lace (list s)))
                            (x (list s)))
                 (:instance fn-lace-equivocator-scan-monotone-lace
                            (rest lace) (x (list s)))
                 (:instance fn-lace-slot-conflictp-monotone (x (list s)))
                 (:instance fn-lace-equivocator-scan-intro
                            (s1 s) (rest (append lace (list s)))
                            (lace (append lace (list s)))
                            (principal p) (incarnation i)))
           :in-theory (disable fn-lace-equivocator-scan-monotone-rest
                               fn-lace-equivocator-scan-monotone-lace
                               fn-lace-slot-conflictp-monotone
                               fn-lace-equivocator-scan-intro
                               (:d fn-lace-slot-conflictp)))))

; -----------------------------------------------------------------------------
; The index record (three alists), opaque above its lemmas

(defun fn-stx-index-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)))
(defun fn-stx-index-bindings (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(verify-guards fn-stx-index-bindings)
(defun fn-stx-index-slots (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(verify-guards fn-stx-index-slots)
(defun fn-stx-index-records (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(verify-guards fn-stx-index-records)
(defun fn-stx-make-index (bindings slots records)
  (declare (xargs :guard t))
  (list bindings slots records))

(defthm fn-stx-index-shapep-of-fn-stx-make-index
  (fn-stx-index-shapep (fn-stx-make-index bindings slots records)))
(defthm fn-stx-index-bindings-of-fn-stx-make-index
  (equal (fn-stx-index-bindings (fn-stx-make-index bindings slots records))
         bindings))
(defthm fn-stx-index-slots-of-fn-stx-make-index
  (equal (fn-stx-index-slots (fn-stx-make-index bindings slots records))
         slots))
(defthm fn-stx-index-records-of-fn-stx-make-index
  (equal (fn-stx-index-records (fn-stx-make-index bindings slots records))
         records))

(in-theory (disable (:d fn-stx-index-shapep) (:d fn-stx-index-bindings)
                    (:d fn-stx-index-slots) (:d fn-stx-index-records)
                    (:d fn-stx-make-index)))

; -----------------------------------------------------------------------------
; The durable equivocation record

; `held` is the statement the slot already carried.  Under the index
; invariant it is always a statement -- it came out of the lace -- but the
; constructor does not need that to be total, and a record is a report, not
; a place to put a guard obligation.
(defun fn-stx-equivocation-record (held new)
  (declare (xargs :guard (fn-stmt-p new)))
  (list :equivocation
        (fn-stmt-creator new) (fn-stmt-incarnation new) (fn-stmt-sequence new)
        (if (fn-stmt-p held) (fn-stmt-id held) nil)
        (fn-stmt-id new)))

(defun fn-stx-record-creator (r)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr r)) :exec (fn-ag-car (fn-ag-cdr r))))
(verify-guards fn-stx-record-creator)
(defun fn-stx-record-incarnation (r)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr r))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr r)))))
(verify-guards fn-stx-record-incarnation)
(defun fn-stx-record-sequence (r)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr r))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr r))))))
(verify-guards fn-stx-record-sequence)
(defun fn-stx-record-id-held (r)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr r)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr r)))))))
(verify-guards fn-stx-record-id-held)
(defun fn-stx-record-id-new (r)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr r))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr r))))))))
(verify-guards fn-stx-record-id-new)

(defthm fn-stx-record-creator-of-fn-stx-equivocation-record
  (equal (fn-stx-record-creator (fn-stx-equivocation-record held new))
         (fn-stmt-creator new)))
(defthm fn-stx-record-incarnation-of-fn-stx-equivocation-record
  (equal (fn-stx-record-incarnation (fn-stx-equivocation-record held new))
         (fn-stmt-incarnation new)))
(defthm fn-stx-record-sequence-of-fn-stx-equivocation-record
  (equal (fn-stx-record-sequence (fn-stx-equivocation-record held new))
         (fn-stmt-sequence new)))
(defthm fn-stx-record-id-held-of-fn-stx-equivocation-record
  (implies (fn-stmt-p held)
           (equal (fn-stx-record-id-held (fn-stx-equivocation-record held new))
                  (fn-stmt-id held))))
(defthm fn-stx-record-id-new-of-fn-stx-equivocation-record
  (equal (fn-stx-record-id-new (fn-stx-equivocation-record held new))
         (fn-stmt-id new)))

(in-theory (disable (:d fn-stx-equivocation-record) (:d fn-stx-record-creator)
                    (:d fn-stx-record-incarnation) (:d fn-stx-record-sequence)
                    (:d fn-stx-record-id-held) (:d fn-stx-record-id-new)))

; -----------------------------------------------------------------------------
; The index itself

(defun fn-stx-alist-get (key al)
  (declare (xargs :guard t))
  (if (consp al)
      (if (and (consp (car al)) (equal (car (car al)) key))
          (car al)
        (fn-stx-alist-get key (cdr al)))
    nil))

(defun fn-stx-index-empty ()
  (declare (xargs :guard t))
  (fn-stx-make-index nil nil nil))

; One statement into the index.  A binding and a slot entry are written only
; when absent, so both hold the OLDEST statement -- which is what
; fn-lace-lookup and the lace's slot scan read.  A record is written exactly
; when the slot already holds a DIFFERENT statement: both forks stay in the
; store, and the record names the pair.
(defun fn-stx-index-add1 (index s)
  (declare (xargs :guard (fn-stmt-p s)))
  (let* ((b (fn-stx-index-bindings index))
         (sl (fn-stx-index-slots index))
         (rs (fn-stx-index-records index))
         (prev (fn-stx-alist-get (fn-stx-slot-key s) sl)))
    (fn-stx-make-index
     (if (fn-stx-alist-get (fn-stmt-id s) b)
         b
       (cons (cons (fn-stmt-id s) s) b))
     (if prev sl (cons (cons (fn-stx-slot-key s) s) sl))
     (if (and (consp prev) (not (equal (cdr prev) s)))
         (cons (fn-stx-equivocation-record (cdr prev) s) rs)
       rs))))

(defun fn-stx-index-add (index delta)
  (declare (xargs :guard (fn-lace-p delta)))
  (if (consp delta) (fn-stx-index-add1 index (car delta)) index))

(defthm fn-stx-bindings-of-add1
  (equal (fn-stx-index-bindings (fn-stx-index-add1 index s))
         (if (fn-stx-alist-get (fn-stmt-id s) (fn-stx-index-bindings index))
             (fn-stx-index-bindings index)
           (cons (cons (fn-stmt-id s) s) (fn-stx-index-bindings index)))))

(defthm fn-stx-slots-of-add1
  (equal (fn-stx-index-slots (fn-stx-index-add1 index s))
         (if (fn-stx-alist-get (fn-stx-slot-key s) (fn-stx-index-slots index))
             (fn-stx-index-slots index)
           (cons (cons (fn-stx-slot-key s) s) (fn-stx-index-slots index)))))

(defthm fn-stx-records-of-add1
  (equal (fn-stx-index-records (fn-stx-index-add1 index s))
         (let ((prev (fn-stx-alist-get (fn-stx-slot-key s)
                                       (fn-stx-index-slots index))))
           (if (and (consp prev) (not (equal (cdr prev) s)))
               (cons (fn-stx-equivocation-record (cdr prev) s)
                     (fn-stx-index-records index))
             (fn-stx-index-records index)))))

(in-theory (disable (:d fn-stx-index-add1)))

(defun fn-stx-index-of-store (articles keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp articles)
      (fn-stx-index-add (fn-stx-index-of-store (cdr articles) keyring)
                        (fn-stx-delta (fn-article-payload (car articles))
                                      keyring))
    (fn-stx-index-empty)))

; -----------------------------------------------------------------------------
; The three served-path queries

(defthm fn-stx-alist-get-is-cons-or-nil
  (or (consp (fn-stx-alist-get key al))
      (equal (fn-stx-alist-get key al) nil))
  :rule-classes :type-prescription)

(defun fn-stx-index-lookup (index id)
  (declare (xargs :guard t))
  (cdr (fn-stx-alist-get id (fn-stx-index-bindings index))))

(defun fn-stx-index-slot-first (index k)
  (declare (xargs :guard t))
  (cdr (fn-stx-alist-get k (fn-stx-index-slots index))))

(defun fn-stx-records-scan (rs p i)
  (declare (xargs :guard t))
  (if (consp rs)
      (or (and (equal (fn-stx-record-creator (car rs)) p)
               (equal (fn-stx-record-incarnation (car rs)) i))
          (fn-stx-records-scan (cdr rs) p i))
    nil))

(defun fn-stx-index-equivocatorp (index p i)
  (declare (xargs :guard t))
  (if (fn-stx-records-scan (fn-stx-index-records index) p i) t nil))

(defun fn-stx-recorded-equivocationp (index p i)
  (declare (xargs :guard t))
  (fn-stx-index-equivocatorp index p i))

; -----------------------------------------------------------------------------
; The invariant, and the agreement

(defun fn-stx-index-invariantp (index node keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (equal index (fn-stx-index-of-store (fn-stx-store node) keyring)))

(local (defthm fn-stx-lookup-of-append
         (equal (fn-lace-lookup (append a b) id)
                (if (member-equal id (fn-lace-ids a))
                    (fn-lace-lookup a id)
                  (fn-lace-lookup b id)))))

(local (defthm fn-stx-slot-first-of-append
         (implies (fn-lace-p a)
                  (equal (fn-stx-lace-slot-first (append a b) k)
                         (if (fn-stx-lace-slot-first a k)
                             (fn-stx-lace-slot-first a k)
                           (fn-stx-lace-slot-first b k))))))

(local (defthm fn-stx-lace-ids-of-append
         (equal (fn-lace-ids (append a b))
                (append (fn-lace-ids a) (fn-lace-ids b)))))

(local (defthm fn-stx-member-append
         (iff (member-equal x (append a b))
              (or (member-equal x a) (member-equal x b)))))

(local (defthm fn-stx-lookup-non-nil-iff-id
         (implies (fn-lace-p lace)
                  (iff (fn-lace-lookup lace id)
                       (member-equal id (fn-lace-ids lace))))))

; Three inductions, not one: each query is proved on its own, and the
; equivocator proof uses the slot agreement as a rewrite rule, which is how
; it reaches the slot of the incoming statement without an instantiation
; hint.  One five-conjunct induction hit the induction-depth limit.

(local (in-theory (disable fn-stx-delta)))

(defthm fn-stx-index-bindings-agree
  (and (equal (fn-stx-index-lookup (fn-stx-index-of-store articles keyring) id)
              (fn-lace-lookup (fn-stx-lace-of-store articles keyring) id))
       (iff (fn-stx-alist-get
             id (fn-stx-index-bindings (fn-stx-index-of-store articles keyring)))
            (member-equal id (fn-lace-ids (fn-stx-lace-of-store articles
                                                                keyring)))))
  :hints (("Goal" :induct (fn-stx-index-of-store articles keyring)
           :in-theory (e/d ((:d fn-stx-index-of-store) (:d fn-stx-lace-of-store)
                            (:d fn-stx-index-add)
                            (:d fn-stx-index-lookup) (:d fn-stx-alist-get))
                           (fn-stx-delta (:d fn-lace-slot-conflictp)
                            (:d fn-lace-equivocatorp) (:d fn-lace-same-slotp))))))

(defthm fn-stx-index-slots-agree
  (and (equal (fn-stx-index-slot-first (fn-stx-index-of-store articles keyring) k)
              (fn-stx-lace-slot-first (fn-stx-lace-of-store articles keyring) k))
       (iff (fn-stx-alist-get
             k (fn-stx-index-slots (fn-stx-index-of-store articles keyring)))
            (fn-stx-lace-slot-first (fn-stx-lace-of-store articles keyring) k)))
  :hints (("Goal" :induct (fn-stx-index-of-store articles keyring)
           :in-theory (e/d ((:d fn-stx-index-of-store) (:d fn-stx-lace-of-store)
                            (:d fn-stx-index-add)
                            (:d fn-stx-index-slot-first) (:d fn-stx-alist-get)
                            (:d fn-stx-lace-slot-first))
                           (fn-stx-delta (:d fn-lace-slot-conflictp)
                            (:d fn-lace-equivocatorp) (:d fn-lace-same-slotp))))))

; The fork half.  A record is written exactly when the slot already holds a
; DIFFERENT statement; when it holds the same one and the lace has forked
; anyway, the record is already there by the induction hypothesis.
(defthm fn-stx-index-equivocators-agree
  (iff (fn-stx-index-equivocatorp (fn-stx-index-of-store articles keyring) p i)
       (fn-lace-equivocatorp (fn-stx-lace-of-store articles keyring) p i))
  :hints (("Goal" :induct (fn-stx-index-of-store articles keyring)
           :in-theory (e/d ((:d fn-stx-index-of-store) (:d fn-stx-lace-of-store)
                            (:d fn-stx-index-add)
                            (:d fn-stx-index-equivocatorp)
                            (:d fn-stx-records-scan) (:d fn-stx-alist-get)
                            fn-lace-slot-conflictp-intro
                            fn-lace-distinct-same-slot-is-equivocation)
                           (fn-stx-delta (:d fn-lace-slot-conflictp)
                            (:d fn-lace-equivocatorp) (:d fn-lace-same-slotp)
                            fn-stx-slot-conflictp-of-append
                            fn-stx-slot-conflictp-of-singleton)))
          ("Subgoal *1/1"
           :use ((:instance fn-stx-equivocatorp-of-one-more
                            (lace (fn-stx-lace-of-store (cdr articles) keyring))
                            (s (car (fn-stx-delta
                                     (fn-article-payload (car articles))
                                     keyring))))
                 (:instance fn-stx-slot-conflictp-implies-slot-first
                            (lace (fn-stx-lace-of-store (cdr articles) keyring))
                            (s (car (fn-stx-delta
                                     (fn-article-payload (car articles))
                                     keyring))))
                 (:instance fn-stx-delta-is-lace
                            (octets (fn-article-payload (car articles))))
                 (:instance fn-stx-delta-is-nil-or-singleton
                            (octets (fn-article-payload (car articles))))))))

; S3-3, in the vocabulary of the served path.
(defthm fn-stx-index-agrees-with-lace
  (implies (fn-stx-index-invariantp index node keyring)
           (and (equal (fn-stx-index-lookup index id)
                       (fn-lace-lookup (fn-stx-lace node keyring) id))
                (iff (fn-stx-index-equivocatorp index p i)
                     (fn-lace-equivocatorp (fn-stx-lace node keyring) p i))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stx-index-bindings-agree
                                   (articles (fn-stx-store node)))
                        (:instance fn-stx-index-equivocators-agree
                                   (articles (fn-stx-store node))))
           :in-theory (disable fn-stx-index-bindings-agree
                               fn-stx-index-equivocators-agree
                               fn-stx-index-of-store fn-stx-lace-of-store
                               fn-stx-index-lookup fn-stx-index-equivocatorp))))

; The durable record is a proved twin of the lace, not a second authority.
(defthm fn-stx-recorded-equivocation-agrees-with-lace
  (implies (fn-stx-index-invariantp index node keyring)
           (iff (fn-stx-recorded-equivocationp index p i)
                (fn-lace-equivocatorp (fn-stx-lace node keyring) p i)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stx-index-agrees-with-lace))
           :in-theory (disable fn-stx-index-invariantp fn-stx-lace
                               fn-stx-index-equivocatorp))))

; The invariant is carried, not recomputed: one cons per accepted article.
(defthm fn-stx-index-invariant-preserved-by-accept
  (implies (and (fn-stx-index-invariantp index node keyring)
                (fn-stx-acceptedp node next article))
           (fn-stx-index-invariantp
            (fn-stx-index-add index
                              (fn-stx-delta (fn-article-payload article) keyring))
            next keyring))
  :hints (("Goal" :in-theory (enable (:d fn-stx-acceptedp)))))

; -----------------------------------------------------------------------------
; The cost shadow (D3): the served query walks the index, never the store.

(defun fn-stx-alist-steps (key al)
  (declare (xargs :guard t))
  (if (consp al)
      (if (and (consp (car al)) (equal (car (car al)) key))
          1
        (+ 1 (fn-stx-alist-steps key (cdr al))))
    0))

(defthm fn-stx-index-lookup-cost-is-index-bounded
  (<= (fn-stx-alist-steps id (fn-stx-index-bindings index))
      (len (fn-stx-index-bindings index)))
  :rule-classes :linear)

(defthm fn-stx-index-grows-by-at-most-one-binding
  (<= (len (fn-stx-index-bindings (fn-stx-index-add index delta)))
      (+ 1 (len (fn-stx-index-bindings index))))
  :rule-classes :linear)

; Named honestly: this is the support of the query, not a proof event.  No
; branch of fn-stx-index-lookup mentions fn-stx-lace, fn-stx-store,
; fn-article-parse or fn-stx-verdict, so no served query re-derives the
; projection or re-parses an article.
(defthm fn-stx-index-query-is-store-free-by-definition
  (equal (fn-stx-index-lookup index id)
         (cdr (fn-stx-alist-get id (fn-stx-index-bindings index))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).

(in-theory (disable (:d fn-stx-alist-get) (:d fn-stx-index-add1)
                    (:d fn-stx-index-add) (:d fn-stx-index-lookup)
                    (:d fn-stx-index-slot-first) (:d fn-stx-records-scan)
                    (:d fn-stx-index-equivocatorp)
                    (:d fn-stx-recorded-equivocationp)
                    (:d fn-stx-index-invariantp)
                    (:d fn-stx-lace-slot-first) (:d fn-stx-slot-partner)))
