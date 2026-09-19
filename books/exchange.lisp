; fn M4 exchange: a pure, finite, transport-independent immutable-fact model.
;
; This book models neither a serialized batch format nor signatures, storage,
; or peer behavior.  `provenance' is an already-validated authorization token
; supplied by the caller.  Unknown schemas are rejected: an opaque relay path
; needs a separately specified encoding and authority policy before it exists.
;
; Records are opaque and `fn-exchange-statep' is a carried invariant guarding
; `fn-exchange-admissible-batchp' and `fn-exchange-ingest'
; (docs/proof-style.md).  The :logic bodies are the original total ones.

(in-package "ACL2")
; Reuse the proved total CAR/CDR and membership execution helpers.
(include-book "acceptance-alloc")

; -----------------------------------------------------------------------------
; Portable facts, identities, and explicit validation policy

; Fact: (schema kind message-id content-id origin incarnation sequence provenance)
; `message-id', `content-id', and `(origin incarnation sequence)' deliberately
; name different namespaces.  Facts that share a Message-ID but differ in their
; content IDs are retained as separate evidence.
(defun fn-exchange-fact-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 8)))
(defun fn-exchange-schema (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(verify-guards fn-exchange-schema)
(defun fn-exchange-kind (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(verify-guards fn-exchange-kind)
(defun fn-exchange-message-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(verify-guards fn-exchange-message-id)
(defun fn-exchange-content-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(verify-guards fn-exchange-content-id)
(defun fn-exchange-origin (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(verify-guards fn-exchange-origin)
(defun fn-exchange-incarnation (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))))
(verify-guards fn-exchange-incarnation)
(defun fn-exchange-sequence (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                     (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))
(verify-guards fn-exchange-sequence)
(defun fn-exchange-provenance (x)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                     (fn-ag-cdr (fn-ag-cdr
                                                 (fn-ag-cdr (fn-ag-cdr x))))))))))
(verify-guards fn-exchange-provenance)

(defun fn-exchange-make-fact
  (schema kind message-id content-id origin incarnation sequence provenance)
  (declare (xargs :guard t))
  (list schema kind message-id content-id origin incarnation sequence provenance))

(defthm fn-exchange-fact-shapep-of-fn-exchange-make-fact
  (fn-exchange-fact-shapep
   (fn-exchange-make-fact schema kind message-id content-id origin incarnation
                          sequence provenance)))
(defthm fn-exchange-schema-of-fn-exchange-make-fact
  (equal (fn-exchange-schema
          (fn-exchange-make-fact schema kind message-id content-id origin
                                 incarnation sequence provenance))
         schema))
(defthm fn-exchange-kind-of-fn-exchange-make-fact
  (equal (fn-exchange-kind
          (fn-exchange-make-fact schema kind message-id content-id origin
                                 incarnation sequence provenance))
         kind))
(defthm fn-exchange-message-id-of-fn-exchange-make-fact
  (equal (fn-exchange-message-id
          (fn-exchange-make-fact schema kind message-id content-id origin
                                 incarnation sequence provenance))
         message-id))
(defthm fn-exchange-content-id-of-fn-exchange-make-fact
  (equal (fn-exchange-content-id
          (fn-exchange-make-fact schema kind message-id content-id origin
                                 incarnation sequence provenance))
         content-id))
(defthm fn-exchange-origin-of-fn-exchange-make-fact
  (equal (fn-exchange-origin
          (fn-exchange-make-fact schema kind message-id content-id origin
                                 incarnation sequence provenance))
         origin))
(defthm fn-exchange-incarnation-of-fn-exchange-make-fact
  (equal (fn-exchange-incarnation
          (fn-exchange-make-fact schema kind message-id content-id origin
                                 incarnation sequence provenance))
         incarnation))
(defthm fn-exchange-sequence-of-fn-exchange-make-fact
  (equal (fn-exchange-sequence
          (fn-exchange-make-fact schema kind message-id content-id origin
                                 incarnation sequence provenance))
         sequence))
(defthm fn-exchange-provenance-of-fn-exchange-make-fact
  (equal (fn-exchange-provenance
          (fn-exchange-make-fact schema kind message-id content-id origin
                                 incarnation sequence provenance))
         provenance))

; What opacity takes away, exported back: the shape and a well-typed field
; each imply the record is a cons (forward-chaining, never rewrite).
(defthm fn-exchange-fact-shapep-forward-shape
  (implies (fn-exchange-fact-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-exchange-fact-shapep))))
(defthm fn-exchange-fact-accessors-forward-consp
  (and
   (implies (fn-exchange-schema x) (consp x))
   (implies (fn-exchange-kind x) (consp x))
   (implies (fn-exchange-message-id x) (consp x))
   (implies (fn-exchange-content-id x) (consp x))
   (implies (fn-exchange-origin x) (consp x))
   (implies (fn-exchange-incarnation x) (consp x))
   (implies (fn-exchange-sequence x) (consp x))
   (implies (fn-exchange-provenance x) (consp x))
   )
  :rule-classes
  ((:forward-chaining :corollary (implies (fn-exchange-schema x) (consp x))
                      :trigger-terms ((fn-exchange-schema x)))
   (:forward-chaining :corollary (implies (fn-exchange-kind x) (consp x))
                      :trigger-terms ((fn-exchange-kind x)))
   (:forward-chaining :corollary (implies (fn-exchange-message-id x) (consp x))
                      :trigger-terms ((fn-exchange-message-id x)))
   (:forward-chaining :corollary (implies (fn-exchange-content-id x) (consp x))
                      :trigger-terms ((fn-exchange-content-id x)))
   (:forward-chaining :corollary (implies (fn-exchange-origin x) (consp x))
                      :trigger-terms ((fn-exchange-origin x)))
   (:forward-chaining :corollary (implies (fn-exchange-incarnation x) (consp x))
                      :trigger-terms ((fn-exchange-incarnation x)))
   (:forward-chaining :corollary (implies (fn-exchange-sequence x) (consp x))
                      :trigger-terms ((fn-exchange-sequence x)))
   (:forward-chaining :corollary (implies (fn-exchange-provenance x) (consp x))
                      :trigger-terms ((fn-exchange-provenance x)))
   )
  :hints (("Goal" :in-theory (enable fn-exchange-schema fn-exchange-kind fn-exchange-message-id fn-exchange-content-id fn-exchange-origin fn-exchange-incarnation fn-exchange-sequence fn-exchange-provenance))))

(in-theory (disable (:d fn-exchange-fact-shapep) (:d fn-exchange-schema) (:d fn-exchange-kind) (:d fn-exchange-message-id) (:d fn-exchange-content-id) (:d fn-exchange-origin) (:d fn-exchange-incarnation) (:d fn-exchange-sequence) (:d fn-exchange-provenance) (:d fn-exchange-make-fact)))

(defun fn-exchange-kindp (x)
  (declare (xargs :guard t :verify-guards nil))
  (or (equal x :object) (equal x :statement)))

(verify-guards fn-exchange-kindp)

(defun fn-exchange-origin-event-id (x)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-exchange-origin x)
        (fn-exchange-incarnation x)
        (fn-exchange-sequence x)))

(verify-guards fn-exchange-origin-event-id)

(defun fn-exchange-factp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-exchange-fact-shapep x)
       (natp (fn-exchange-schema x))
       (fn-exchange-kindp (fn-exchange-kind x))
       (stringp (fn-exchange-message-id x))
       (stringp (fn-exchange-content-id x))
       (stringp (fn-exchange-origin x))
       (stringp (fn-exchange-incarnation x))
       (natp (fn-exchange-sequence x))
       (stringp (fn-exchange-provenance x))))

(defthm fn-exchange-factp-forward-shape
  (implies (fn-exchange-factp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-exchange-factp))))

(verify-guards fn-exchange-factp)

(defun fn-exchange-string-listp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (stringp (car xs))
           (fn-exchange-string-listp (cdr xs)))
    (null xs)))

(verify-guards fn-exchange-string-listp)

(defun fn-exchange-no-duplicatesp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp xs)
                  (and (not (member-equal (car xs) (cdr xs)))
                       (fn-exchange-no-duplicatesp (cdr xs)))
                t)
       :exec (if (consp xs)
                 (and (not (fn-ag-member (car xs) (cdr xs)))
                      (fn-exchange-no-duplicatesp (cdr xs)))
               t)))

(verify-guards fn-exchange-no-duplicatesp)

; Policy: (enabled-schemas authorized-provenances).  Schema 1 is the one
; understood semantic schema in this model.  A policy cannot promote another
; schema by listing it; this makes unknown input unable to authorize a change.
(defun fn-exchange-policy-shapep (p)
  (declare (xargs :guard t))
  (and (true-listp p) (equal (len p) 2)))
(defun fn-exchange-policy-schemas (p)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car p) :exec (fn-ag-car p)))
(verify-guards fn-exchange-policy-schemas)
(defun fn-exchange-policy-authorizations (p)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr p)) :exec (fn-ag-car (fn-ag-cdr p))))
(verify-guards fn-exchange-policy-authorizations)

(defun fn-exchange-make-policy (schemas authorizations)
  (declare (xargs :guard t))
  (list schemas authorizations))

(defthm fn-exchange-policy-shapep-of-fn-exchange-make-policy
  (fn-exchange-policy-shapep (fn-exchange-make-policy schemas authorizations)))
(defthm fn-exchange-policy-schemas-of-fn-exchange-make-policy
  (equal (fn-exchange-policy-schemas
          (fn-exchange-make-policy schemas authorizations))
         schemas))
(defthm fn-exchange-policy-authorizations-of-fn-exchange-make-policy
  (equal (fn-exchange-policy-authorizations
          (fn-exchange-make-policy schemas authorizations))
         authorizations))

; What opacity takes away, exported back: the shape and a well-typed field
; each imply the record is a cons (forward-chaining, never rewrite).
(defthm fn-exchange-policy-shapep-forward-shape
  (implies (fn-exchange-policy-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-exchange-policy-shapep))))
(defthm fn-exchange-policy-accessors-forward-consp
  (and
   (implies (fn-exchange-policy-schemas x) (consp x))
   (implies (fn-exchange-policy-authorizations x) (consp x))
   )
  :rule-classes
  ((:forward-chaining :corollary (implies (fn-exchange-policy-schemas x) (consp x))
                      :trigger-terms ((fn-exchange-policy-schemas x)))
   (:forward-chaining :corollary (implies (fn-exchange-policy-authorizations x) (consp x))
                      :trigger-terms ((fn-exchange-policy-authorizations x)))
   )
  :hints (("Goal" :in-theory (enable fn-exchange-policy-schemas fn-exchange-policy-authorizations))))

(in-theory (disable (:d fn-exchange-policy-shapep) (:d fn-exchange-policy-schemas) (:d fn-exchange-policy-authorizations) (:d fn-exchange-make-policy)))

(defun fn-exchange-policyp (p)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-exchange-policy-shapep p)
       (true-listp (fn-exchange-policy-schemas p))
       (fn-exchange-no-duplicatesp (fn-exchange-policy-schemas p))
       (fn-exchange-string-listp (fn-exchange-policy-authorizations p))
       (fn-exchange-no-duplicatesp (fn-exchange-policy-authorizations p))))

(defthm fn-exchange-policyp-forward-shape
  (implies (fn-exchange-policyp p) (and (consp p) (true-listp p)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-exchange-policyp))))

(verify-guards fn-exchange-policyp)

(defun fn-exchange-known-schemap (schema policy)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (and (equal schema 1)
                   (member-equal schema (fn-exchange-policy-schemas policy)))
       :exec (and (equal schema 1)
                  (fn-ag-member schema (fn-exchange-policy-schemas policy)))))

(verify-guards fn-exchange-known-schemap)

(defun fn-exchange-authorizedp (provenance policy)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (member-equal provenance
                            (fn-exchange-policy-authorizations policy))
       :exec (fn-ag-member provenance
                           (fn-exchange-policy-authorizations policy))))

(verify-guards fn-exchange-authorizedp)

(defun fn-exchange-validatep (fact policy)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-exchange-policyp policy)
       (fn-exchange-factp fact)
       (fn-exchange-known-schemap (fn-exchange-schema fact) policy)
       (fn-exchange-authorizedp (fn-exchange-provenance fact) policy)))

(verify-guards fn-exchange-validatep)

(defun fn-exchange-batch-validp (batch policy)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp batch)
      (and (fn-exchange-validatep (car batch) policy)
           (fn-exchange-batch-validp (cdr batch) policy))
    (null batch)))

(verify-guards fn-exchange-batch-validp)

; -----------------------------------------------------------------------------
; Immutable set operations.  Their cons order is deliberately not observable.

(defun fn-exchange-add-fact (fact facts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (member-equal fact facts) facts (cons fact facts))
       :exec (if (fn-ag-member fact facts) facts (cons fact facts))))

(verify-guards fn-exchange-add-fact)

(defun fn-exchange-merge (batch facts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp batch)
      (fn-exchange-merge (cdr batch)
                         (fn-exchange-add-fact (car batch) facts))
    facts))

(verify-guards fn-exchange-merge)

(defun fn-exchange-subsetp (xs ys)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp xs)
                  (and (member-equal (car xs) ys)
                       (fn-exchange-subsetp (cdr xs) ys))
                t)
       :exec (if (consp xs)
                 (and (fn-ag-member (car xs) ys)
                      (fn-exchange-subsetp (cdr xs) ys))
               t)))

(verify-guards fn-exchange-subsetp)

(defun fn-exchange-set-equiv (xs ys)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-exchange-subsetp xs ys)
       (fn-exchange-subsetp ys xs)))

(verify-guards fn-exchange-set-equiv)

(defthm fn-exchange-subsetp-right-extension
  (implies (fn-exchange-subsetp xs ys)
           (fn-exchange-subsetp xs (cons y ys)))
  :hints (("Goal" :induct (fn-exchange-subsetp xs ys)
           :in-theory (enable fn-exchange-subsetp))))

(defthm fn-exchange-subsetp-reflexive
  (fn-exchange-subsetp xs xs)
  :hints (("Goal" :induct (fn-exchange-subsetp xs xs)
           :in-theory (enable fn-exchange-subsetp))))

(defthm fn-exchange-add-fact-member
  (iff (member-equal x (fn-exchange-add-fact fact facts))
       (or (equal x fact) (member-equal x facts)))
  :hints (("Goal" :in-theory (enable fn-exchange-add-fact))))

(defthm fn-exchange-merge-member
  (iff (member-equal x (fn-exchange-merge batch facts))
       (or (member-equal x batch) (member-equal x facts)))
  :hints (("Goal" :induct (fn-exchange-merge batch facts)
           :in-theory (enable fn-exchange-merge))))

(defthm fn-exchange-member-append
  (iff (member-equal x (append left right))
       (or (member-equal x left) (member-equal x right)))
  :hints (("Goal" :induct (append left right))))

(defthm fn-exchange-merge-idempotent
  (fn-exchange-set-equiv
   (fn-exchange-merge batch (fn-exchange-merge batch facts))
   (fn-exchange-merge batch facts))
  :hints (("Goal" :in-theory (enable fn-exchange-set-equiv
                                      fn-exchange-subsetp))))

; This pointwise theorem is the executable set-equivalence observation for
; reordering: every possible fact has the same membership on either side.
(defthm fn-exchange-merge-commutative-member
  (iff (member-equal x
                      (fn-exchange-merge
                       left (fn-exchange-merge right facts)))
       (member-equal x
                      (fn-exchange-merge
                       right (fn-exchange-merge left facts))))
  :hints (("Goal" :in-theory (enable fn-exchange-merge-member))))

; -----------------------------------------------------------------------------
; A bounded all-or-nothing fact-store transition.

; State: (capacity facts).  Capacity is charged by distinct retained facts in
; this abstract slice.  A real byte/obligation charge needs the storage and
; retention correspondence; no such durability claim is made here.
(defun fn-exchange-state-shapep (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 2)))
(defun fn-exchange-capacity (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car s) :exec (fn-ag-car s)))
(verify-guards fn-exchange-capacity)
(defun fn-exchange-facts (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr s)) :exec (fn-ag-car (fn-ag-cdr s))))
(verify-guards fn-exchange-facts)

(defun fn-exchange-make-state (capacity facts)
  (declare (xargs :guard t))
  (list capacity facts))

(defthm fn-exchange-state-shapep-of-fn-exchange-make-state
  (fn-exchange-state-shapep (fn-exchange-make-state capacity facts)))
(defthm fn-exchange-capacity-of-fn-exchange-make-state
  (equal (fn-exchange-capacity (fn-exchange-make-state capacity facts))
         capacity))
(defthm fn-exchange-facts-of-fn-exchange-make-state
  (equal (fn-exchange-facts (fn-exchange-make-state capacity facts))
         facts))

; What opacity takes away, exported back: the shape and a well-typed field
; each imply the record is a cons (forward-chaining, never rewrite).
(defthm fn-exchange-state-shapep-forward-shape
  (implies (fn-exchange-state-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-exchange-state-shapep))))
(defthm fn-exchange-state-accessors-forward-consp
  (and
   (implies (fn-exchange-capacity x) (consp x))
   (implies (fn-exchange-facts x) (consp x))
   )
  :rule-classes
  ((:forward-chaining :corollary (implies (fn-exchange-capacity x) (consp x))
                      :trigger-terms ((fn-exchange-capacity x)))
   (:forward-chaining :corollary (implies (fn-exchange-facts x) (consp x))
                      :trigger-terms ((fn-exchange-facts x)))
   )
  :hints (("Goal" :in-theory (enable fn-exchange-capacity fn-exchange-facts))))

(in-theory (disable (:d fn-exchange-state-shapep) (:d fn-exchange-capacity) (:d fn-exchange-facts) (:d fn-exchange-make-state)))

(defun fn-exchange-fact-listp (facts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp facts)
      (and (fn-exchange-factp (car facts))
           (fn-exchange-fact-listp (cdr facts)))
    (null facts)))

(verify-guards fn-exchange-fact-listp)

(defun fn-exchange-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-exchange-state-shapep s)
       (natp (fn-exchange-capacity s))
       (fn-exchange-fact-listp (fn-exchange-facts s))
       (fn-exchange-no-duplicatesp (fn-exchange-facts s))
       (<= (len (fn-exchange-facts s)) (fn-exchange-capacity s))))

(defthm fn-exchange-statep-forward-shape
  (implies (fn-exchange-statep s) (and (consp s) (true-listp s)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-exchange-statep))))

(verify-guards fn-exchange-statep)

(defun fn-exchange-initial-state (capacity)
  (declare (xargs :guard t :verify-guards nil))
  (fn-exchange-make-state capacity nil))

(verify-guards fn-exchange-initial-state)

(defun fn-exchange-new-facts (batch facts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp batch)
                  (if (member-equal (car batch) facts)
                      (fn-exchange-new-facts (cdr batch) facts)
                    (cons (car batch)
                          (fn-exchange-new-facts (cdr batch)
                                                 (cons (car batch) facts))))
                nil)
       :exec (if (consp batch)
                 (if (fn-ag-member (car batch) facts)
                     (fn-exchange-new-facts (cdr batch) facts)
                   (cons (car batch)
                         (fn-exchange-new-facts (cdr batch)
                                                (cons (car batch) facts))))
               nil)))

(verify-guards fn-exchange-new-facts)

; Admissibility is decided under the carried invariant: the :logic body keeps
; the whole-state recognizer as its first conjunct, the :exec path relies on
; the guard.
(defun fn-exchange-admissible-batchp (s batch policy)
  (declare (xargs :guard (fn-exchange-statep s) :verify-guards nil))
  (and (mbe :logic (fn-exchange-statep s) :exec t)
       (fn-exchange-batch-validp batch policy)
       (<= (+ (len (fn-exchange-facts s))
              (len (fn-exchange-new-facts batch (fn-exchange-facts s))))
           (fn-exchange-capacity s))))

(verify-guards fn-exchange-admissible-batchp)

; Capacity or validation refusal leaves the state exact.  In particular this
; never installs a prefix of an unaffordable batch and never erases facts.
(defun fn-exchange-ingest (s batch policy)
  (declare (xargs :guard (fn-exchange-statep s) :verify-guards nil))
  (if (fn-exchange-admissible-batchp s batch policy)
      (fn-exchange-make-state
       (fn-exchange-capacity s)
       (fn-exchange-merge batch (fn-exchange-facts s)))
    s))

(verify-guards fn-exchange-ingest)

; A `-by-definition' fact: the refusing branch with its test as hypothesis.
; Not a registry event and not a rewrite rule; used by :use.
(defthm fn-exchange-ingest-refusal-is-no-op
  (implies (not (fn-exchange-admissible-batchp s batch policy))
           (equal (fn-exchange-ingest s batch policy) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-exchange-ingest))))

; The observable result of an admitted batch is its immutable fact set; list
; ordering is a local representation detail.
(defthm fn-exchange-admitted-ingest-member
  (implies (fn-exchange-admissible-batchp s batch policy)
           (iff (member-equal x
                              (fn-exchange-facts
                               (fn-exchange-ingest s batch policy)))
                (or (member-equal x batch)
                    (member-equal x (fn-exchange-facts s)))))
  :hints (("Goal" :in-theory (enable fn-exchange-ingest))))

; If each ordering is admissible as a complete atomic batch, they converge to
; the same observable set.  The hypotheses matter: finite capacity intentionally
; permits refusal rather than silently retaining only an arrival-order prefix.
(defthm fn-exchange-admitted-order-member
  (implies (and (fn-exchange-admissible-batchp s (append left right) policy)
                (fn-exchange-admissible-batchp s (append right left) policy))
           (iff (member-equal x
                              (fn-exchange-facts
                               (fn-exchange-ingest s (append left right) policy)))
                (member-equal x
                              (fn-exchange-facts
                               (fn-exchange-ingest s (append right left) policy)))))
  :hints (("Goal"
           :use ((:instance fn-exchange-admitted-ingest-member
                            (batch (append left right)))
                 (:instance fn-exchange-admitted-ingest-member
                            (batch (append right left))))
           :in-theory (enable fn-exchange-member-append))))

; -----------------------------------------------------------------------------
; Deterministic local Message-ID status, without timestamp winner selection.

(defun fn-exchange-object-for-messagep (message-id fact)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-exchange-kind fact) :object)
       (equal (fn-exchange-message-id fact) message-id)))

(verify-guards fn-exchange-object-for-messagep)

(defun fn-exchange-any-object-for-messagep (message-id facts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp facts)
      (or (fn-exchange-object-for-messagep message-id (car facts))
          (fn-exchange-any-object-for-messagep message-id (cdr facts)))
    nil))

(verify-guards fn-exchange-any-object-for-messagep)

(defun fn-exchange-conflicting-with-contentp (message-id content-id facts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp facts)
      (or (and (fn-exchange-object-for-messagep message-id (car facts))
               (not (equal content-id (fn-exchange-content-id (car facts)))))
          (fn-exchange-conflicting-with-contentp message-id content-id (cdr facts)))
    nil))

(verify-guards fn-exchange-conflicting-with-contentp)

(defun fn-exchange-conflicting-messagep (message-id facts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp facts)
      (or (and (fn-exchange-object-for-messagep message-id (car facts))
               (fn-exchange-conflicting-with-contentp
                message-id
                (fn-exchange-content-id (car facts))
                (cdr facts)))
          (fn-exchange-conflicting-messagep message-id (cdr facts)))
    nil))

(verify-guards fn-exchange-conflicting-messagep)

(defun fn-exchange-message-status (message-id facts)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-exchange-any-object-for-messagep message-id facts))
      :absent
    (if (fn-exchange-conflicting-messagep message-id facts)
        :conflict
      :single)))

(verify-guards fn-exchange-message-status)

; -----------------------------------------------------------------------------
; Export.  Records were disabled at their definitions.  Withdrawn here: the
; recognizers, the initial state, admissibility and ingest, and the set
; lemmas that are proof vocabulary rather than keystones (exchange-invariants
; enables them locally).  Keystones stay enabled: the two merge observations,
; `fn-exchange-admitted-ingest-member' and `fn-exchange-admitted-order-member'.
(deftheory fn-exchange-set-vocabulary
  '(fn-exchange-subsetp-right-extension
    fn-exchange-subsetp-reflexive
    fn-exchange-add-fact-member
    fn-exchange-merge-member
    fn-exchange-member-append))
(in-theory (disable fn-exchange-set-vocabulary
                    (:d fn-exchange-factp) (:d fn-exchange-policyp) (:d fn-exchange-statep) (:d fn-exchange-initial-state) (:d fn-exchange-admissible-batchp) (:d fn-exchange-ingest)))
