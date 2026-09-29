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
; The policy column's key (the statement's policy group) and slot order (W5b,
; lane stx-model-2, 2026-09-29).
(include-book "policy-invariants")

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
  (and (true-listp x) (equal (len x) 4)))
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
; The fourth column (W5b): per (group . authority), the authority's policy
; statement of the greatest (incarnation, sequence) slot seen and whether a
; DISTINCT policy statement shares that slot -- fn-pol-current's answer
; (books/policy.lisp) without a walk of the lace; see fn-stx-index-policy-current.
(defun fn-stx-index-policies (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(verify-guards fn-stx-index-policies)
(defun fn-stx-make-index (bindings slots records policies)
  (declare (xargs :guard t))
  (list bindings slots records policies))

(defthm fn-stx-index-shapep-of-fn-stx-make-index
  (fn-stx-index-shapep (fn-stx-make-index bindings slots records policies)))
(defthm fn-stx-index-bindings-of-fn-stx-make-index
  (equal (fn-stx-index-bindings (fn-stx-make-index bindings slots records policies))
         bindings))
(defthm fn-stx-index-slots-of-fn-stx-make-index
  (equal (fn-stx-index-slots (fn-stx-make-index bindings slots records policies))
         slots))
(defthm fn-stx-index-records-of-fn-stx-make-index
  (equal (fn-stx-index-records (fn-stx-make-index bindings slots records policies))
         records))
(defthm fn-stx-index-policies-of-fn-stx-make-index
  (equal (fn-stx-index-policies (fn-stx-make-index bindings slots records policies))
         policies))

(in-theory (disable (:d fn-stx-index-shapep) (:d fn-stx-index-bindings)
                    (:d fn-stx-index-slots) (:d fn-stx-index-records)
                    (:d fn-stx-index-policies) (:d fn-stx-make-index)))

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

; -----------------------------------------------------------------------------
; The policy column's key and entry (W5b).  A statement keys the column when it
; is a :policy statement whose payload decodes to a policy: (group . creator).
; An entry is (stmt . conflictp): the greatest-slot policy statement seen under
; that key and whether a distinct one shares its slot.  The update is one
; comparison (fn-pol-slot-lessp, the order fn-pol-latest maximises); an entry
; that is not a statement (unreachable: every entry was consed here) is
; replaced.

; books/policy.lisp keeps the decoded policy's list shape local; the group
; accessor's guard needs it once more here.
(local (defthm fn-stx-policy-of-stmt-is-true-list
         (true-listp (fn-pol-statement-policy s))
         :hints (("Goal" :use fn-pol-statement-policy-is-policy
                  :in-theory (e/d (fn-pol-policy-p)
                                  (fn-pol-statement-policy
                                   fn-pol-statement-policy-is-policy))))))

(defun fn-stx-policy-key (s)
  (declare (xargs :guard (fn-stmt-p s)
                  :guard-hints (("Goal" :in-theory (disable fn-pol-statement-policy)))))
  (if (equal (fn-stmt-kind s) :policy)
      (let ((p (fn-pol-statement-policy s)))
        (if (consp p) (cons (fn-pol-policy-group p) (fn-stmt-creator s)) nil))
    nil))

(defun fn-stx-policy-entry-add (entry s)
  (declare (xargs :guard (fn-stmt-p s)))
  (if (not (and (consp entry) (fn-stmt-p (car entry))))
      (cons s nil)
    (cond ((fn-pol-slot-lessp (car entry) s) (cons s nil))
          ((fn-pol-slot-lessp s (car entry)) entry)
          ((equal s (car entry)) entry)
          (t (cons (car entry) t)))))

(defun fn-stx-index-empty ()
  (declare (xargs :guard t))
  (fn-stx-make-index nil nil nil nil))

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
         (ps (fn-stx-index-policies index))
         (prev (fn-stx-alist-get (fn-stx-slot-key s) sl))
         (k (fn-stx-policy-key s)))
    (fn-stx-make-index
     (if (fn-stx-alist-get (fn-stmt-id s) b)
         b
       (cons (cons (fn-stmt-id s) s) b))
     (if prev sl (cons (cons (fn-stx-slot-key s) s) sl))
     (if (and (consp prev) (not (equal (cdr prev) s)))
         (cons (fn-stx-equivocation-record (cdr prev) s) rs)
       rs)
     (if k
         (cons (cons k (fn-stx-policy-entry-add (cdr (fn-stx-alist-get k ps)) s)) ps)
       ps))))

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

(defthm fn-stx-policies-of-add1
  (equal (fn-stx-index-policies (fn-stx-index-add1 index s))
         (let ((k (fn-stx-policy-key s))
               (ps (fn-stx-index-policies index)))
           (if k
               (cons (cons k (fn-stx-policy-entry-add (cdr (fn-stx-alist-get k ps)) s))
                     ps)
             ps))))

(in-theory (disable (:d fn-stx-index-add1)))

;; The index of an article list whose payloads are OCTETS (the octet model's
;; articles).  A retained article's payload is a handle since the records
;; flip, so the store's opens build the index from the rows' bytes
;; (books/store-intern.lisp, books/records-freeze.lisp), and an open with no
;; keyring builds the empty index directly (fn-stx-index-of-store-without-a-
;; keyring: no statement verifies without a key, whatever the payloads).
(fn-payload-kind fn-stx-index-of-store :wire "its articles are the octet model's; opens pass rows' bytes, or no keyring and build (fn-stx-index-empty)")
; Executes by a loop (PKT-876, lane open-depth): the right fold ran one
; control-stack frame per article.  The :exec folds the reversed list from
; the left, the same additions in the same order; equal by the guard proof.
(fn-payload-kind fn-stx-index-of-store-loop :wire "fn-stx-index-of-store's loop twin: the same articles")
(defun fn-stx-index-of-store-loop (rev keyring index)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp rev)
      (fn-stx-index-of-store-loop (cdr rev) keyring
                                  (fn-stx-index-add index
                                                    (fn-stx-delta (fn-article-payload (car rev))
                                                                  keyring)))
    index))

(defun fn-stx-index-of-store (articles keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring) :verify-guards nil))
  (mbe :logic
       (if (consp articles)
           (fn-stx-index-add (fn-stx-index-of-store (cdr articles) keyring)
                             (fn-stx-delta (fn-article-payload (car articles))
                                           keyring))
         (fn-stx-index-empty))
       :exec (fn-stx-index-of-store-loop (fn-ag-rev-onto articles nil) keyring
                                         (fn-stx-index-empty))))

(encapsulate ()
  (local
   (defthm fn-stx-index-of-store-loop-of-rev-onto
     (equal (fn-stx-index-of-store-loop (fn-ag-rev-onto xs zs) keyring (fn-stx-index-empty))
            (fn-stx-index-of-store-loop zs keyring (fn-stx-index-of-store xs keyring)))
     :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                     :in-theory (disable fn-stx-index-add fn-stx-delta fn-stx-index-empty
                                         (:e fn-stx-index-empty))))))
  (verify-guards fn-stx-index-of-store
    :hints (("Goal" :in-theory (disable fn-stx-index-add fn-stx-delta fn-ag-rev-onto)
                    :use ((:instance fn-stx-index-of-store-loop-of-rev-onto
                                     (xs articles) (zs nil)))))))

;; KEYSTONE (PKT-859).  Without a keyring no statement verifies, so the
;; index of ANY article list -- handles, octets, anything -- is the empty
;; index.  The opens that have no keyring yet (books/config-observed.lisp,
;; books/store-checkpoint-open.lisp, books/replay-identity-index.lisp) build
;; (fn-stx-index-empty) and so never walk the retained articles parsing a
;; handle as a statement's octets.
(defthm fn-stx-index-of-store-without-a-keyring
  (equal (fn-stx-index-of-store articles nil) (fn-stx-index-empty))
  :hints (("Goal" :induct (fn-stx-index-of-store articles nil)
           :in-theory (enable fn-stx-delta fn-stx-verifiedp fn-prin-verifiedp))))

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

; The policy in force for (group, authority), from the column: the entry's
; statement unless a distinct policy statement shares its slot (W5b).  One
; alist lookup; no lace, no store, no parse.
(defun fn-stx-index-policy-current (index group authority)
  (declare (xargs :guard t))
  (let ((e (cdr (fn-stx-alist-get (cons group authority)
                                  (fn-stx-index-policies index)))))
    (if (and (consp e) (not (cdr e))) (car e) nil)))

; -----------------------------------------------------------------------------
; The agreement, over an article list.  The invariant over the NODE
; (fn-stx-index-invariantp) and the agreement and preservation stated over it
; are books/stx-node-lace.lisp's, which reads the node's handles through the
; arena (PKT-892, 2026-09-29); until then the invariant here compared the
; index with the octet model's fold over the node's HANDLES, which is the
; empty index for every node the machine produces.

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

(local (defthm fn-stx-equivocatorp-of-nil
         (not (fn-lace-equivocatorp nil p i))
         :hints (("Goal" :in-theory (enable (:d fn-lace-equivocatorp))))))

(local (defthm fn-stx-lace-car-is-consp
         (implies (and (fn-lace-p x) (consp x))
                  (consp (car x)))
         :hints (("Goal" :in-theory (enable fn-lace-p)))))

(local (defthm fn-stx-ids-of-short-list
         (implies (not (consp (cdr delta)))
                  (equal (fn-lace-ids delta)
                         (if (consp delta)
                             (list (fn-stmt-id (car delta)))
                           nil)))))

(local (defthm fn-stx-lookup-of-short-list
         (implies (not (consp (cdr delta)))
                  (equal (fn-lace-lookup delta id)
                         (if (and (consp delta)
                                  (equal (fn-stmt-id (car delta)) id))
                             (car delta)
                           nil)))))

(local (defthm fn-stx-slot-first-of-short-list
         (implies (not (consp (cdr delta)))
                  (equal (fn-stx-lace-slot-first delta k)
                         (if (and (consp delta)
                                  (equal (fn-stx-slot-key (car delta)) k))
                             (car delta)
                           nil)))))

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

; The fan tools/proof_profile.py named on fn-stx-index-equivocators-agree
; (persvati, ACL2 8.7, 2026-09-20): fifteen runes with ZERO useful
; applications, headed by fn-stx-index-stmt-is-consp at 18,651 frames, then
; (:type-prescription fn-stmt-p) at 8,540, (:definition fn-lace-p) at 6,996
; and (:definition fn-stx-alist-get) at 5,880.  Each backchains on every
; list-shaped subterm the induction produces.  The two forms below reason in
; index and lace vocabulary and need none of them, so they withdraw the lot.
(local
 (deftheory fn-stx-index-equivocator-fan
   '(fn-stx-index-stmt-is-consp
     fn-lace-member-is-stmt
     fn-stx-lace-slot-first-of-member
     fn-stx-lace-car-is-consp
     fn-prin-acceptablep-implies-shapes
     (:type-prescription fn-stmt-p)
     (:definition fn-lace-p)
     (:d fn-stx-alist-get))))

; (append x nil) is x for a true list.  :rule-classes nil and cited once:
; a general append-nil rewrite backchains on true-listp everywhere.
(local (defthm fn-stx-append-nil
         (implies (true-listp x) (equal (append x nil) x))
         :rule-classes nil))

; An index with no records reports no equivocator.  Stated over the record
; list rather than over (fn-stx-index-empty), because the base case of the
; induction has already evaluated the empty index to its constant.  This is
; what lets the induction run with fn-stx-index-equivocatorp and
; fn-stx-records-scan both closed.
(local (defthm fn-stx-index-equivocatorp-of-no-records
         (implies (not (fn-stx-index-records index))
                  (not (fn-stx-index-equivocatorp index p i)))
         :hints (("Goal" :in-theory (enable (:d fn-stx-index-equivocatorp)
                                            (:d fn-stx-records-scan))))))

; Two one-literal bridges between the index's slot query and the lace's
; equivocator predicate.  Both are stated with every hypothesis explicit and
; cited by :use, because the lemmas underneath them cannot fire as rewrites
; here: fn-lace-distinct-same-slot-is-equivocation takes the principal and
; the incarnation from a statement the goal does not name, and
; fn-lace-slot-conflictp-intro has a free s2.  Citing those two directly
; inside a larger proof scatters their hypotheses across the clausifier's
; cross product -- measured: one surviving checkpoint whose only defect was
; a branch in which fn-stx-slot-partner-elim's same-slot conjunct sat in a
; different clause from the one that needed it.  Neither statement below
; mentions the partner, so that cross product does not arise.

; The slot already holds THIS statement and the lace forks it anyway: the
; lace was an equivocator before the step, so the index already carries the
; record and no new one is needed.
(local (defthm fn-stx-slot-fork-is-equivocation
         (implies (and (fn-lace-p lace)
                       (fn-stx-lace-slot-first lace (fn-stx-slot-key s))
                       (equal (fn-stx-lace-slot-first lace (fn-stx-slot-key s))
                              s)
                       (fn-lace-slot-conflictp s lace))
                  (fn-lace-equivocatorp lace (fn-stmt-creator s)
                                        (fn-stmt-incarnation s)))
         :rule-classes nil
         :hints (("Goal"
                  :do-not-induct t
                  :use ((:instance fn-stx-lace-slot-first-is-member
                                   (k (fn-stx-slot-key s)))
                        (:instance fn-stx-slot-partner-elim)
                        (:instance fn-lace-distinct-same-slot-is-equivocation
                                   (s1 s) (s2 (fn-stx-slot-partner lace s))))
                  :in-theory (e/d ((:d fn-lace-same-slotp))
                                  (fn-stx-index-equivocator-fan
                                   (:d fn-lace-slot-conflictp)
                                   (:d fn-lace-equivocatorp)
                                   (:d fn-stx-lace-slot-first)
                                   (:d fn-stx-slot-partner)
                                   fn-stx-lace-slot-first-is-member
                                   fn-stx-slot-partner-elim
                                   fn-stx-slot-partner-is-member
                                   fn-stx-slot-partner-differs
                                   fn-stx-slot-partner-same-slot
                                   fn-lace-distinct-same-slot-is-equivocation))))))

; The slot already holds a DIFFERENT statement: that is a fork of s.
(local (defthm fn-stx-slot-first-differs-is-conflict
         (implies (and (fn-stx-lace-slot-first lace (fn-stx-slot-key s))
                       (not (equal (fn-stx-lace-slot-first lace
                                                           (fn-stx-slot-key s))
                                   s)))
                  (fn-lace-slot-conflictp s lace))
         :rule-classes nil
         :hints (("Goal"
                  :do-not-induct t
                  :use ((:instance fn-stx-lace-slot-first-is-member
                                   (k (fn-stx-slot-key s)))
                        (:instance fn-stx-lace-slot-first-key
                                   (k (fn-stx-slot-key s)))
                        (:instance fn-lace-slot-conflictp-intro
                                   (s1 s)
                                   (s2 (fn-stx-lace-slot-first
                                        lace (fn-stx-slot-key s)))))
                  :in-theory (e/d ((:d fn-lace-same-slotp))
                                  (fn-stx-index-equivocator-fan
                                   (:d fn-lace-slot-conflictp)
                                   (:d fn-stx-lace-slot-first)
                                   fn-stx-lace-slot-first-is-member
                                   fn-stx-lace-slot-first-key
                                   fn-lace-slot-conflictp-intro))))))

; The fork half, as ONE step over one more statement.
;
; A record is written exactly when the slot ALREADY holds a DIFFERENT
; statement.  The lace's equivocator predicate is wider by one case, and the
; two bridges above are that case and its converse.
;
; The first three hypotheses are exactly what fn-stx-lace-of-store-is-lace
; and fn-stx-index-slots-agree supply at the induction step; the last is the
; induction hypothesis.  Stating it over an arbitrary index and lace is what
; keeps the induction looking at a single step.
(local
 (defthm fn-stx-index-equivocatorp-of-add1
   (implies
    (and (fn-lace-p lace)
         (equal (fn-stx-index-slot-first index (fn-stx-slot-key s))
                (fn-stx-lace-slot-first lace (fn-stx-slot-key s)))
         (iff (fn-stx-alist-get (fn-stx-slot-key s)
                                (fn-stx-index-slots index))
              (fn-stx-lace-slot-first lace (fn-stx-slot-key s)))
         (iff (fn-stx-index-equivocatorp index p i)
              (fn-lace-equivocatorp lace p i)))
    (iff (fn-stx-index-equivocatorp (fn-stx-index-add1 index s) p i)
         (fn-lace-equivocatorp (append lace (list s)) p i)))
   :rule-classes nil
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance fn-stx-equivocatorp-of-one-more)
                  (:instance fn-stx-slot-conflictp-implies-slot-first)
                  (:instance fn-stx-slot-fork-is-equivocation)
                  (:instance fn-stx-slot-first-differs-is-conflict))
            :in-theory (e/d ((:d fn-stx-index-equivocatorp)
                             (:d fn-stx-records-scan)
                             (:d fn-stx-index-slot-first))
                            (fn-stx-index-equivocator-fan
                             (:d fn-lace-slot-conflictp)
                             (:d fn-lace-equivocatorp)
                             (:d fn-lace-same-slotp)
                             (:d fn-stx-lace-slot-first)
                             (:d fn-stx-slot-partner)
                             fn-stx-equivocatorp-of-one-more
                             fn-stx-slot-conflictp-implies-slot-first
                             fn-stx-lace-slot-first-is-member
                             fn-stx-lace-slot-first-key
                             fn-stx-lace-slot-first-of-member
                             fn-lace-slot-conflictp-intro
                             fn-lace-equivocator-scan-intro
                             fn-lace-distinct-same-slot-is-equivocation
                             fn-stx-slot-partner-elim
                             fn-stx-slot-partner-is-member
                             fn-stx-slot-partner-differs
                             fn-stx-slot-partner-same-slot
                             fn-stx-slot-conflictp-of-append
                             fn-stx-scan-of-append-rest
                             fn-stx-slot-conflictp-of-singleton))))))

; The same step over a delta that is nil or a singleton, which is the shape
; fn-stx-index-of-store and fn-stx-lace-of-store actually hand the induction.
; Doing the nil/singleton split here rather than in the induction is what
; keeps the main hint to one :use.
(local
 (defthm fn-stx-index-equivocatorp-of-add
   (implies
    (and (fn-lace-p lace)
         (true-listp lace)
         (fn-lace-p delta)
         (not (consp (cdr delta)))
         (equal (fn-stx-index-slot-first index (fn-stx-slot-key (car delta)))
                (fn-stx-lace-slot-first lace (fn-stx-slot-key (car delta))))
         (iff (fn-stx-alist-get (fn-stx-slot-key (car delta))
                                (fn-stx-index-slots index))
              (fn-stx-lace-slot-first lace (fn-stx-slot-key (car delta))))
         (iff (fn-stx-index-equivocatorp index p i)
              (fn-lace-equivocatorp lace p i)))
    (iff (fn-stx-index-equivocatorp (fn-stx-index-add index delta) p i)
         (fn-lace-equivocatorp (append lace delta) p i)))
   :rule-classes nil
   :hints (("Goal"
            :do-not-induct t
            :cases ((consp delta))
            :use ((:instance fn-stx-index-equivocatorp-of-add1 (s (car delta)))
                  (:instance fn-stx-append-nil (x lace)))
            ; (:d fn-lace-p) is re-enabled AFTER the fan withdraws it: the
            ; nil/singleton split is the one place this book needs it open.
            :in-theory (e/d ((:d fn-stx-index-add))
                            (fn-stx-index-equivocator-fan
                             (:d fn-stx-index-equivocatorp)
                             (:d fn-stx-records-scan)
                             (:d fn-lace-slot-conflictp)
                             (:d fn-lace-equivocatorp)
                             (:d fn-lace-same-slotp)
                             (:d fn-stx-lace-slot-first)
                             (:d fn-stx-index-add1)
                             fn-stx-slot-conflictp-of-append
                             fn-stx-scan-of-append-rest
                             fn-stx-slot-conflictp-of-singleton)
                            ((:d fn-lace-p)))))))

; S3-3's equivocator half.  The induction supplies the step lemma's
; hypotheses and does nothing else: the slot agreement is
; fn-stx-index-slots-agree above, the lace shape and its true-listp are
; fn-stx-lace-of-store-is-lace and -is-true-list, the delta shape is
; fn-stx-delta-is-lace and -is-nil-or-singleton, and the last hypothesis is
; the induction hypothesis itself.  Nothing here opens the equivocator
; predicate on either side.
(defthm fn-stx-index-equivocators-agree
  (iff (fn-stx-index-equivocatorp (fn-stx-index-of-store articles keyring) p i)
       (fn-lace-equivocatorp (fn-stx-lace-of-store articles keyring) p i))
  :hints (("Goal" :induct (fn-stx-index-of-store articles keyring)
           :in-theory (e/d ((:d fn-stx-index-of-store)
                            (:d fn-stx-lace-of-store))
                           (fn-stx-index-equivocator-fan
                            fn-stx-delta
                            (:d fn-stx-index-add)
                            (:d fn-stx-index-add1)
                            (:d fn-stx-index-equivocatorp)
                            (:d fn-stx-records-scan)
                            (:d fn-lace-slot-conflictp)
                            (:d fn-lace-equivocatorp)
                            (:d fn-lace-same-slotp)
                            (:d fn-stx-lace-slot-first)
                            fn-stx-slot-conflictp-of-append
                            fn-stx-scan-of-append-rest
                            fn-stx-slot-conflictp-of-singleton)))
          ("Subgoal *1/1"
           :use ((:instance fn-stx-index-equivocatorp-of-add
                            (index (fn-stx-index-of-store (cdr articles)
                                                          keyring))
                            (lace (fn-stx-lace-of-store (cdr articles) keyring))
                            (delta (fn-stx-delta
                                    (fn-article-payload (car articles))
                                    keyring)))))))

; S3-3 over the node -- fn-stx-index-agrees-with-lace,
; fn-stx-recorded-equivocation-agrees-with-lace and
; fn-stx-index-invariant-preserved-by-accept -- is books/stx-node-lace.lisp's.

; -----------------------------------------------------------------------------
; The cost shadow (D3): the served query walks the index, never the store.

(defun fn-stx-alist-steps (key al)
  (declare (xargs :guard t))
  (if (consp al)
      (if (and (consp (car al)) (equal (car (car al)) key))
          1
        (+ 1 (fn-stx-alist-steps key (cdr al))))
    0))

; The bound is proved of the walk, where the induction variable is the list;
; the cost shadow is that fact at the index's binding list.  Stated this way
; round because (fn-stx-index-bindings index) is not a variable, so the
; shadow on its own suggests no induction scheme.
(local (defthm fn-stx-alist-steps-is-len-bounded
         (<= (fn-stx-alist-steps key al) (len al))
         :rule-classes :linear))

(defthm fn-stx-index-lookup-cost-is-index-bounded
  (<= (fn-stx-alist-steps id (fn-stx-index-bindings index))
      (len (fn-stx-index-bindings index)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-stx-alist-steps-is-len-bounded
                                   (key id)
                                   (al (fn-stx-index-bindings index)))))))

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
; THE POLICY COLUMN AGREES WITH THE LACE (W5b, lane stx-model-2, 2026-09-29).
; fn-pol-current over the lace of the store (books/policy.lisp: the
; greatest-slot candidate unless the authority forked at that slot) is the
; column's answer.  Proved through an order-independent characterisation of
; the fold: after folding the candidates the entry holds a maximal candidate
; and records whether a distinct candidate shares its slot; fn-pol-latest is
; maximal too (fn-pol-latest-is-maximal), two maximal candidates of one
; authority share a slot, and fn-pol-same-slot-conflictp is exactly that.
; The keyring drops out because every member of the lace of the store is
; verified under it (fn-stx-delta emits nothing else).

(local (defthm fn-stx-pol-stmt-slots-are-natural
  (implies (fn-stmt-p s)
           (and (natp (fn-stmt-incarnation s)) (natp (fn-stmt-sequence s))))
  :hints (("Goal" :in-theory (enable fn-stmt-p fn-stmt-headerp fn-stmt-incarnation
                                     fn-stmt-sequence fn-record-uint32p)))))
(local (defthm fn-stx-pol-same-slotp-is-neither-below
  (implies (and (fn-stmt-p a) (fn-stmt-p b)
                (equal (fn-stmt-creator a) (fn-stmt-creator b)))
           (iff (fn-lace-same-slotp a b)
                (and (not (fn-pol-slot-lessp a b)) (not (fn-pol-slot-lessp b a)))))
  :hints (("Goal" :in-theory (e/d (fn-pol-slot-lessp (:d fn-lace-same-slotp)) (fn-stmt-p))))))
(local (defthm fn-stx-pol-candidatep-is-key
  (implies (fn-prin-verifiedp s keyring)
           (iff (fn-pol-candidatep s keyring group authority)
                (and (fn-stmt-p s) (equal (fn-stx-policy-key s) (cons group authority)))))
  :hints (("Goal" :in-theory (e/d (fn-pol-candidatep fn-stx-policy-key)
                                  (fn-pol-statement-policy fn-stmt-p fn-prin-verifiedp))))))
(local (defthm fn-stx-pol-delta-member-is-verified
  (implies (member-equal s (fn-stx-delta octets keyring))
           (fn-prin-verifiedp s keyring))
  :hints (("Goal" :in-theory (enable (:d fn-stx-delta) (:d fn-stx-verifiedp))))))
(local (defthm fn-stx-pol-delta-car-is-stmt
  (implies (consp (fn-stx-delta octets keyring))
           (fn-stmt-p (car (fn-stx-delta octets keyring))))
  :hints (("Goal" :use fn-stx-delta-is-lace :in-theory (e/d (fn-lace-p) (fn-stx-delta-is-lace))))))
(local (defun fn-stx-pol-all-verifiedp (lace keyring)
  (if (consp lace)
      (and (fn-prin-verifiedp (car lace) keyring)
           (fn-stx-pol-all-verifiedp (cdr lace) keyring))
    t)))
(local (defthm fn-stx-pol-all-verifiedp-of-append
  (iff (fn-stx-pol-all-verifiedp (append a b) keyring)
       (and (fn-stx-pol-all-verifiedp a keyring) (fn-stx-pol-all-verifiedp b keyring)))))
(local (defthm fn-stx-pol-delta-is-all-verified
  (fn-stx-pol-all-verifiedp (fn-stx-delta octets keyring) keyring)
  :hints (("Goal" :use (fn-stx-delta-is-nil-or-singleton
                        (:instance fn-stx-pol-delta-member-is-verified
                                   (s (car (fn-stx-delta octets keyring)))))
           :in-theory (e/d (member-equal) (fn-stx-delta-is-nil-or-singleton
                                           fn-stx-pol-delta-member-is-verified))
           :expand ((fn-stx-pol-all-verifiedp (fn-stx-delta octets keyring) keyring)
                    (fn-stx-pol-all-verifiedp (cdr (fn-stx-delta octets keyring)) keyring))))))
(local (defthm fn-stx-pol-lace-of-store-is-all-verified
  (fn-stx-pol-all-verifiedp (fn-stx-lace-of-store articles keyring) keyring)
  :hints (("Goal" :in-theory (e/d ((:d fn-stx-lace-of-store)) (fn-stx-delta fn-prin-verifiedp))))))
(local (defun fn-stx-pol-filter (lace group authority)
  (if (consp lace)
      (if (and (fn-stmt-p (car lace))
               (equal (fn-stx-policy-key (car lace)) (cons group authority)))
          (cons (car lace) (fn-stx-pol-filter (cdr lace) group authority))
        (fn-stx-pol-filter (cdr lace) group authority))
    nil)))
(local (defthm fn-stx-pol-candidates-of-verified-lace-are-filter
  (implies (fn-stx-pol-all-verifiedp lace keyring)
           (equal (fn-pol-candidates lace keyring group authority)
                  (fn-stx-pol-filter lace group authority)))
  :hints (("Goal" :in-theory (e/d (fn-pol-candidates) (fn-pol-candidatep fn-stmt-p fn-stx-policy-key fn-prin-verifiedp))))))
(local (defthm fn-stx-pol-filter-of-append
  (equal (fn-stx-pol-filter (append a b) group authority)
         (append (fn-stx-pol-filter a group authority) (fn-stx-pol-filter b group authority)))))
(local (defun fn-stx-pol-fold (cands entry)
  (if (consp cands)
      (fn-stx-pol-fold (cdr cands) (fn-stx-policy-entry-add entry (car cands)))
    entry)))
(local (defthm fn-stx-pol-fold-of-append
  (equal (fn-stx-pol-fold (append a b) e)
         (fn-stx-pol-fold b (fn-stx-pol-fold a e)))))
(local (defthm fn-stx-pol-filter-of-short-list
  (implies (not (consp (cdr d)))
           (equal (fn-stx-pol-filter d group authority)
                  (if (and (consp d) (fn-stmt-p (car d))
                           (equal (fn-stx-policy-key (car d)) (cons group authority)))
                      (list (car d))
                    nil)))
  :hints (("Goal" :in-theory (disable fn-stmt-p fn-stx-policy-key)))))
(local (defthm fn-stx-pol-column-of-store-is-the-fold
  (equal (cdr (fn-stx-alist-get (cons group authority)
                                (fn-stx-index-policies (fn-stx-index-of-store articles keyring))))
         (fn-stx-pol-fold (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority)
                          nil))
  :hints (("Goal" :induct (fn-stx-index-of-store articles keyring)
           :in-theory (e/d ((:d fn-stx-index-of-store) (:d fn-stx-lace-of-store)
                            (:d fn-stx-index-add) (:d fn-stx-alist-get)
                            fn-stx-pol-filter-of-append fn-stx-pol-fold-of-append)
                           (fn-stx-delta fn-stx-policy-key fn-stx-policy-entry-add fn-stmt-p
                            fn-stx-pol-filter))))))

(local (defun fn-stx-pol-not-above (m cands)
  (if (consp cands)
      (and (not (fn-pol-slot-lessp m (car cands))) (fn-stx-pol-not-above m (cdr cands)))
    t)))
(local (defun fn-stx-pol-conflictp (m cands)
  (if (consp cands)
      (or (and (not (equal (car cands) m))
               (not (fn-pol-slot-lessp m (car cands)))
               (not (fn-pol-slot-lessp (car cands) m)))
          (fn-stx-pol-conflictp m (cdr cands)))
    nil)))
(local (defun fn-stx-pol-entry-okp (e cands)
  (if (consp cands)
      (and (consp e)
           (member-equal (car e) cands)
           (fn-stx-pol-not-above (car e) cands)
           (iff (cdr e) (fn-stx-pol-conflictp (car e) cands)))
    (null e))))
(local (defthm fn-stx-pol-not-above-of-append-one
  (iff (fn-stx-pol-not-above m (append p (list x)))
       (and (fn-stx-pol-not-above m p) (not (fn-pol-slot-lessp m x))))
  :hints (("Goal" :in-theory (disable fn-pol-slot-lessp)))))
(local (defthm fn-stx-pol-conflictp-of-append-one
  (iff (fn-stx-pol-conflictp m (append p (list x)))
       (or (fn-stx-pol-conflictp m p)
           (and (not (equal x m)) (not (fn-pol-slot-lessp m x)) (not (fn-pol-slot-lessp x m)))))
  :hints (("Goal" :in-theory (disable fn-pol-slot-lessp)))))
(local (defthm fn-stx-pol-member-of-append-one
  (iff (member-equal y (append p (list x))) (or (member-equal y p) (equal y x)))))
(local (defthm fn-stx-pol-not-above-of-bigger
  (implies (and (fn-stx-pol-not-above m p) (fn-pol-slot-lessp m x))
           (fn-stx-pol-not-above x p))
  :hints (("Goal" :in-theory (enable fn-pol-slot-lessp)))))
(local (defthm fn-stx-pol-bigger-has-no-conflict-below
  (implies (and (fn-stx-pol-not-above m p) (fn-pol-slot-lessp m x))
           (not (fn-stx-pol-conflictp x p)))
  :hints (("Goal" :in-theory (enable fn-pol-slot-lessp)))))
(local (defthm fn-stx-pol-lace-member-is-stmt
  (implies (and (fn-lace-p p) (member-equal y p)) (fn-stmt-p y))
  :hints (("Goal" :in-theory (e/d (fn-lace-p) (fn-stmt-p))))))
(local (in-theory (enable fn-pol-invariants-vocabulary)))
(local (defthm fn-stx-pol-entry-add-keeps-okp
  (implies (and (fn-stx-pol-entry-okp e p) (fn-lace-p p) (fn-stmt-p x))
           (fn-stx-pol-entry-okp (fn-stx-policy-entry-add e x) (append p (list x))))
  :hints (("Goal" :in-theory (e/d (fn-stx-policy-entry-add) (fn-pol-slot-lessp fn-stmt-p fn-lace-p))))))
(local (defthm fn-stx-pol-append-assoc
  (equal (append (append a b) c) (append a (append b c)))))
(local (defun fn-stx-pol-fold-induct (c e p)
  (if (consp c)
      (fn-stx-pol-fold-induct (cdr c) (fn-stx-policy-entry-add e (car c)) (append p (list (car c))))
    (list c e p))))
(local (defthm fn-stx-pol-lace-p-of-append
  (implies (true-listp a)
           (iff (fn-lace-p (append a b)) (and (fn-lace-p a) (fn-lace-p b))))
  :hints (("Goal" :in-theory (e/d (fn-lace-p) (fn-stmt-p))))))
(local (defthm fn-stx-pol-lace-p-is-true-list
  (implies (fn-lace-p a) (true-listp a))
  :hints (("Goal" :in-theory (e/d (fn-lace-p) (fn-stmt-p))))))
(local (defthm fn-stx-pol-fold-keeps-okp
  (implies (and (fn-stx-pol-entry-okp e p) (fn-lace-p p) (fn-lace-p c))
           (fn-stx-pol-entry-okp (fn-stx-pol-fold c e) (append p c)))
  :hints (("Goal" :induct (fn-stx-pol-fold-induct c e p)
           :in-theory (e/d (fn-lace-p) (fn-stx-pol-entry-okp fn-stx-policy-entry-add fn-stmt-p
                                        fn-stx-pol-member-of-append-one
                                        fn-stx-pol-not-above-of-append-one
                                        fn-stx-pol-conflictp-of-append-one))))))
(local (defun fn-stx-pol-creators-are (cands authority)
  (if (consp cands)
      (and (equal (fn-stmt-creator (car cands)) authority)
           (fn-stx-pol-creators-are (cdr cands) authority))
    t)))
(local (defthm fn-stx-pol-key-names-the-creator
  (implies (equal (fn-stx-policy-key y) (cons group authority))
           (equal (fn-stmt-creator y) authority))
  :hints (("Goal" :in-theory (e/d (fn-stx-policy-key) (fn-pol-statement-policy fn-stmt-p))))))
(local (defthm fn-stx-pol-filter-facts
  (and (fn-lace-p (fn-stx-pol-filter lace group authority))
       (fn-stx-pol-creators-are (fn-stx-pol-filter lace group authority) authority))
  :hints (("Goal" :in-theory (e/d (fn-lace-p) (fn-stmt-p fn-stx-policy-key))))))
(local (defthm fn-stx-pol-creators-member
  (implies (and (fn-stx-pol-creators-are cands authority) (member-equal y cands))
           (equal (fn-stmt-creator y) authority))))
(local (defthm fn-stx-pol-not-above-member
  (implies (and (fn-stx-pol-not-above m cands) (member-equal x cands))
           (not (fn-pol-slot-lessp m x)))
  :hints (("Goal" :in-theory (disable fn-pol-slot-lessp)))))
(local (defthm fn-stx-pol-conflictp-is-same-slot-conflictp
  (implies (and (fn-stmt-p m) (equal (fn-stmt-creator m) authority)
                (fn-lace-p cands) (fn-stx-pol-creators-are cands authority))
           (iff (fn-stx-pol-conflictp m cands)
                (fn-pol-same-slot-conflictp m cands)))
  :hints (("Goal" :induct (fn-stx-pol-conflictp m cands)
           :in-theory (e/d (fn-pol-same-slot-conflictp fn-lace-p)
                           (fn-pol-slot-lessp fn-stmt-p (:d fn-lace-same-slotp)))))))
(local (defthm fn-stx-pol-same-slot-conflictp-by-member
  (implies (and (member-equal z cands) (not (equal z l)) (fn-lace-same-slotp z l))
           (fn-pol-same-slot-conflictp l cands))
  :hints (("Goal" :in-theory (e/d (fn-pol-same-slot-conflictp) ((:d fn-lace-same-slotp)))))))
(local (defthm fn-stx-pol-maximal-pair-is-same-slot
  (implies (and (fn-lace-p cands) (fn-stx-pol-creators-are cands authority)
                (member-equal a cands) (member-equal b cands)
                (fn-stx-pol-not-above a cands) (fn-stx-pol-not-above b cands))
           (fn-lace-same-slotp a b))
  :hints (("Goal" :use ((:instance fn-stx-pol-same-slotp-is-neither-below))
           :in-theory (disable fn-pol-slot-lessp fn-stmt-p (:d fn-lace-same-slotp)
                               fn-stx-pol-same-slotp-is-neither-below)))))
(local (defthm fn-stx-pol-conflict-case
  (implies (and (fn-lace-p cands) (fn-stx-pol-creators-are cands authority)
                (fn-stx-pol-entry-okp e cands) (cdr e))
           (fn-pol-same-slot-conflictp (fn-pol-latest cands) cands))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-stx-pol-maximal-pair-is-same-slot (a (car e)) (b (fn-pol-latest cands)))
                 (:instance fn-stx-pol-same-slot-conflictp-by-member (z (car e)) (l (fn-pol-latest cands)))
                 (:instance fn-stx-pol-conflictp-is-same-slot-conflictp (m (car e))))
           :in-theory (e/d () (fn-pol-slot-lessp fn-stmt-p (:d fn-lace-same-slotp) fn-pol-latest
                               fn-pol-same-slot-conflictp fn-stx-pol-conflictp fn-stx-pol-not-above
                               fn-stx-pol-maximal-pair-is-same-slot
                               fn-stx-pol-same-slot-conflictp-by-member
                               fn-stx-pol-conflictp-is-same-slot-conflictp))))))
(local (defthm fn-stx-pol-no-conflict-case
  (implies (and (fn-lace-p cands) (fn-stx-pol-creators-are cands authority)
                (fn-stx-pol-entry-okp e cands) (consp cands) (not (cdr e)))
           (and (equal (fn-pol-latest cands) (car e))
                (not (fn-pol-same-slot-conflictp (car e) cands))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-stx-pol-maximal-pair-is-same-slot (a (fn-pol-latest cands)) (b (car e)))
                 (:instance fn-stx-pol-same-slot-conflictp-by-member (z (fn-pol-latest cands)) (l (car e)))
                 (:instance fn-stx-pol-conflictp-is-same-slot-conflictp (m (car e))))
           :in-theory (e/d () (fn-pol-slot-lessp fn-stmt-p (:d fn-lace-same-slotp) fn-pol-latest
                               fn-pol-same-slot-conflictp fn-stx-pol-conflictp fn-stx-pol-not-above
                               fn-stx-pol-maximal-pair-is-same-slot
                               fn-stx-pol-same-slot-conflictp-by-member
                               fn-stx-pol-conflictp-is-same-slot-conflictp))))))
(defthm fn-stx-index-policy-agrees
  (equal (fn-stx-index-policy-current (fn-stx-index-of-store articles keyring) group authority)
         (fn-pol-current (fn-stx-lace-of-store articles keyring) keyring group authority))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-stx-pol-fold-keeps-okp (p nil) (e nil)
                            (c (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority)))
                 (:instance fn-stx-pol-conflict-case
                            (cands (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority))
                            (e (fn-stx-pol-fold (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority) nil)))
                 (:instance fn-stx-pol-no-conflict-case
                            (cands (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority))
                            (e (fn-stx-pol-fold (fn-stx-pol-filter (fn-stx-lace-of-store articles keyring) group authority) nil))))
           :in-theory (e/d (fn-stx-index-policy-current fn-pol-current)
                           (fn-pol-slot-lessp fn-stmt-p fn-pol-latest fn-pol-same-slot-conflictp
                            fn-stx-pol-conflictp fn-stx-pol-not-above fn-stx-pol-fold fn-stx-pol-filter
                            fn-stx-pol-entry-okp fn-pol-candidates fn-stx-lace-of-store fn-stx-index-of-store
                            fn-stx-pol-fold-keeps-okp fn-stx-pol-conflict-case fn-stx-pol-no-conflict-case)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).

(in-theory (disable (:d fn-stx-alist-get) (:d fn-stx-index-add1)
                    (:d fn-stx-index-add) (:d fn-stx-index-lookup)
                    (:d fn-stx-index-slot-first) (:d fn-stx-records-scan)
                    (:d fn-stx-index-equivocatorp)
                    (:d fn-stx-recorded-equivocationp)
                    (:d fn-stx-policy-key) (:d fn-stx-policy-entry-add)
                    (:d fn-stx-index-policy-current)
                    (:d fn-stx-lace-slot-first) (:d fn-stx-slot-partner)))
