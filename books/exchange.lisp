; fn M4 exchange: a pure, finite, transport-independent immutable-fact model.
;
; This book models neither a serialized batch format nor signatures, storage,
; or peer behavior.  `provenance' is an already-validated authorization token
; supplied by the caller.  Unknown schemas are rejected: an opaque relay path
; needs a separately specified encoding and authority policy before it exists.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Portable facts, identities, and explicit validation policy

; Fact: (schema kind message-id content-id origin incarnation sequence provenance)
; `message-id', `content-id', and `(origin incarnation sequence)' deliberately
; name different namespaces.  Facts that share a Message-ID but differ in their
; content IDs are retained as separate evidence.
(defun fn-exchange-schema (x) (car x))
(defun fn-exchange-kind (x) (car (cdr x)))
(defun fn-exchange-message-id (x) (car (cdr (cdr x))))
(defun fn-exchange-content-id (x) (car (cdr (cdr (cdr x)))))
(defun fn-exchange-origin (x) (car (cdr (cdr (cdr (cdr x))))))
(defun fn-exchange-incarnation (x) (car (cdr (cdr (cdr (cdr (cdr x)))))))
(defun fn-exchange-sequence (x) (car (cdr (cdr (cdr (cdr (cdr (cdr x))))))))
(defun fn-exchange-provenance (x)
  (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))

(defun fn-exchange-make-fact
  (schema kind message-id content-id origin incarnation sequence provenance)
  (list schema kind message-id content-id origin incarnation sequence provenance))

(defun fn-exchange-kindp (x)
  (or (equal x :object) (equal x :statement)))

(defun fn-exchange-origin-event-id (x)
  (list (fn-exchange-origin x)
        (fn-exchange-incarnation x)
        (fn-exchange-sequence x)))

(defun fn-exchange-factp (x)
  (and (true-listp x)
       (equal (len x) 8)
       (natp (fn-exchange-schema x))
       (fn-exchange-kindp (fn-exchange-kind x))
       (stringp (fn-exchange-message-id x))
       (stringp (fn-exchange-content-id x))
       (stringp (fn-exchange-origin x))
       (stringp (fn-exchange-incarnation x))
       (natp (fn-exchange-sequence x))
       (stringp (fn-exchange-provenance x))))

(defun fn-exchange-string-listp (xs)
  (if (consp xs)
      (and (stringp (car xs))
           (fn-exchange-string-listp (cdr xs)))
    (null xs)))

(defun fn-exchange-no-duplicatesp (xs)
  (if (consp xs)
      (and (not (member-equal (car xs) (cdr xs)))
           (fn-exchange-no-duplicatesp (cdr xs)))
    t))

; Policy: (enabled-schemas authorized-provenances).  Schema 1 is the one
; understood semantic schema in this model.  A policy cannot promote another
; schema by listing it; this makes unknown input unable to authorize a change.
(defun fn-exchange-policy-schemas (p) (car p))
(defun fn-exchange-policy-authorizations (p) (car (cdr p)))

(defun fn-exchange-make-policy (schemas authorizations)
  (list schemas authorizations))

(defun fn-exchange-policyp (p)
  (and (true-listp p)
       (equal (len p) 2)
       (true-listp (fn-exchange-policy-schemas p))
       (fn-exchange-no-duplicatesp (fn-exchange-policy-schemas p))
       (fn-exchange-string-listp (fn-exchange-policy-authorizations p))
       (fn-exchange-no-duplicatesp (fn-exchange-policy-authorizations p))))

(defun fn-exchange-known-schemap (schema policy)
  (and (equal schema 1)
       (member-equal schema (fn-exchange-policy-schemas policy))))

(defun fn-exchange-authorizedp (provenance policy)
  (member-equal provenance (fn-exchange-policy-authorizations policy)))

(defun fn-exchange-validatep (fact policy)
  (and (fn-exchange-policyp policy)
       (fn-exchange-factp fact)
       (fn-exchange-known-schemap (fn-exchange-schema fact) policy)
       (fn-exchange-authorizedp (fn-exchange-provenance fact) policy)))

(defun fn-exchange-batch-validp (batch policy)
  (if (consp batch)
      (and (fn-exchange-validatep (car batch) policy)
           (fn-exchange-batch-validp (cdr batch) policy))
    (null batch)))

; -----------------------------------------------------------------------------
; Immutable set operations.  Their cons order is deliberately not observable.

(defun fn-exchange-add-fact (fact facts)
  (if (member-equal fact facts)
      facts
    (cons fact facts)))

(defun fn-exchange-merge (batch facts)
  (if (consp batch)
      (fn-exchange-merge (cdr batch)
                         (fn-exchange-add-fact (car batch) facts))
    facts))

(defun fn-exchange-subsetp (xs ys)
  (if (consp xs)
      (and (member-equal (car xs) ys)
           (fn-exchange-subsetp (cdr xs) ys))
    t))

(defun fn-exchange-set-equiv (xs ys)
  (and (fn-exchange-subsetp xs ys)
       (fn-exchange-subsetp ys xs)))

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
(defun fn-exchange-capacity (s) (car s))
(defun fn-exchange-facts (s) (car (cdr s)))

(defun fn-exchange-make-state (capacity facts)
  (list capacity facts))

(defun fn-exchange-fact-listp (facts)
  (if (consp facts)
      (and (fn-exchange-factp (car facts))
           (fn-exchange-fact-listp (cdr facts)))
    (null facts)))

(defun fn-exchange-statep (s)
  (and (true-listp s)
       (equal (len s) 2)
       (natp (fn-exchange-capacity s))
       (fn-exchange-fact-listp (fn-exchange-facts s))
       (fn-exchange-no-duplicatesp (fn-exchange-facts s))
       (<= (len (fn-exchange-facts s)) (fn-exchange-capacity s))))

(defun fn-exchange-initial-state (capacity)
  (fn-exchange-make-state capacity nil))

(defun fn-exchange-new-facts (batch facts)
  (if (consp batch)
      (if (member-equal (car batch) facts)
          (fn-exchange-new-facts (cdr batch) facts)
        (cons (car batch)
              (fn-exchange-new-facts (cdr batch)
                                     (cons (car batch) facts))))
    nil))

(defun fn-exchange-admissible-batchp (s batch policy)
  (and (fn-exchange-statep s)
       (fn-exchange-batch-validp batch policy)
       (<= (+ (len (fn-exchange-facts s))
              (len (fn-exchange-new-facts batch (fn-exchange-facts s))))
           (fn-exchange-capacity s))))

; Capacity or validation refusal leaves the state exact.  In particular this
; never installs a prefix of an unaffordable batch and never erases facts.
(defun fn-exchange-ingest (s batch policy)
  (if (fn-exchange-admissible-batchp s batch policy)
      (fn-exchange-make-state
       (fn-exchange-capacity s)
       (fn-exchange-merge batch (fn-exchange-facts s)))
    s))

(defthm fn-exchange-ingest-refusal-is-no-op
  (implies (not (fn-exchange-admissible-batchp s batch policy))
           (equal (fn-exchange-ingest s batch policy) s))
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
  (and (equal (fn-exchange-kind fact) :object)
       (equal (fn-exchange-message-id fact) message-id)))

(defun fn-exchange-any-object-for-messagep (message-id facts)
  (if (consp facts)
      (or (fn-exchange-object-for-messagep message-id (car facts))
          (fn-exchange-any-object-for-messagep message-id (cdr facts)))
    nil))

(defun fn-exchange-conflicting-with-contentp (message-id content-id facts)
  (if (consp facts)
      (or (and (fn-exchange-object-for-messagep message-id (car facts))
               (not (equal content-id (fn-exchange-content-id (car facts)))))
          (fn-exchange-conflicting-with-contentp message-id content-id (cdr facts)))
    nil))

(defun fn-exchange-conflicting-messagep (message-id facts)
  (if (consp facts)
      (or (and (fn-exchange-object-for-messagep message-id (car facts))
               (fn-exchange-conflicting-with-contentp
                message-id
                (fn-exchange-content-id (car facts))
                (cdr facts)))
          (fn-exchange-conflicting-messagep message-id (cdr facts)))
    nil))

(defun fn-exchange-message-status (message-id facts)
  (if (not (fn-exchange-any-object-for-messagep message-id facts))
      :absent
    (if (fn-exchange-conflicting-messagep message-id facts)
        :conflict
      :single)))
