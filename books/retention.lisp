; fn M1 retention ledger: executable, finite-capacity obligation accounting.
;
; A pin charges capacity once per obligation, including one permanent abstract
; history unit for the release record.  This is intentionally conservative: it
; does not deduplicate bytes shared by several obligations.
; An implementation that deduplicates needs a correspondence argument before it
; can replace this ledger.  Evidence equality is an executable stand-in for an
; already authenticated and locally committed authorization event; this book
; neither implements cryptography nor proves peer honesty or disk durability.
;
; Records are opaque and `fn-retain-statep' is a carried invariant guarding
; `fn-retain-admissiblep', `fn-retain-admit' and `fn-retain-release'
; (docs/proof-style.md).  The :logic bodies are the original total ones.

(in-package "ACL2")
(include-book "acceptance-alloc")

; -----------------------------------------------------------------------------
; Records and finite-list utilities

(defun fn-retain-kindp (kind)
  (declare (xargs :guard t))
  (or (equal kind :archive)
      (equal kind :forward)))

(defun fn-retain-string-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (stringp (car xs))
           (fn-retain-string-listp (cdr xs)))
    (null xs)))

(defun fn-retain-no-duplicatesp (xs)
  (declare (xargs :guard (true-listp xs)))
  (if (consp xs)
      (and (not (member-equal (car xs) (cdr xs)))
           (fn-retain-no-duplicatesp (cdr xs)))
    t))

; Obligation: (identity immutable-subject kind required-evidence charge).
; A positive charge includes at least one permanent history unit; the remaining
; charge is active content/evidence retained while the obligation is pinned.
(defun fn-retain-obligation-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5)))
(defun fn-retain-obligation-id (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-retain-obligation-subject (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-retain-obligation-kind (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-retain-obligation-evidence (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-retain-obligation-charge (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))

(defun fn-retain-make-obligation (id subject kind evidence charge)
  (declare (xargs :guard t))
  (list id subject kind evidence charge))

(defthm fn-retain-obligation-shapep-of-fn-retain-make-obligation
  (fn-retain-obligation-shapep
   (fn-retain-make-obligation id subject kind evidence charge)))
(defthm fn-retain-obligation-id-of-fn-retain-make-obligation
  (equal (fn-retain-obligation-id
          (fn-retain-make-obligation id subject kind evidence charge))
         id))
(defthm fn-retain-obligation-subject-of-fn-retain-make-obligation
  (equal (fn-retain-obligation-subject
          (fn-retain-make-obligation id subject kind evidence charge))
         subject))
(defthm fn-retain-obligation-kind-of-fn-retain-make-obligation
  (equal (fn-retain-obligation-kind
          (fn-retain-make-obligation id subject kind evidence charge))
         kind))
(defthm fn-retain-obligation-evidence-of-fn-retain-make-obligation
  (equal (fn-retain-obligation-evidence
          (fn-retain-make-obligation id subject kind evidence charge))
         evidence))
(defthm fn-retain-obligation-charge-of-fn-retain-make-obligation
  (equal (fn-retain-obligation-charge
          (fn-retain-make-obligation id subject kind evidence charge))
         charge))

; What opacity takes away, exported back: the shape and a well-typed field
; each imply the record is a cons (forward-chaining, never rewrite).
(defthm fn-retain-obligation-shapep-forward-shape
  (implies (fn-retain-obligation-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-retain-obligation-shapep))))
(defthm fn-retain-obligation-accessors-forward-consp
  (and
   (implies (fn-retain-obligation-id x) (consp x))
   (implies (fn-retain-obligation-subject x) (consp x))
   (implies (fn-retain-obligation-kind x) (consp x))
   (implies (fn-retain-obligation-evidence x) (consp x))
   (implies (fn-retain-obligation-charge x) (consp x))
   )
  :rule-classes
  ((:forward-chaining :corollary (implies (fn-retain-obligation-id x) (consp x))
                      :trigger-terms ((fn-retain-obligation-id x)))
   (:forward-chaining :corollary (implies (fn-retain-obligation-subject x) (consp x))
                      :trigger-terms ((fn-retain-obligation-subject x)))
   (:forward-chaining :corollary (implies (fn-retain-obligation-kind x) (consp x))
                      :trigger-terms ((fn-retain-obligation-kind x)))
   (:forward-chaining :corollary (implies (fn-retain-obligation-evidence x) (consp x))
                      :trigger-terms ((fn-retain-obligation-evidence x)))
   (:forward-chaining :corollary (implies (fn-retain-obligation-charge x) (consp x))
                      :trigger-terms ((fn-retain-obligation-charge x)))
   )
  :hints (("Goal" :in-theory (enable fn-retain-obligation-id fn-retain-obligation-subject fn-retain-obligation-kind fn-retain-obligation-evidence fn-retain-obligation-charge))))

(in-theory (disable (:d fn-retain-obligation-shapep) (:d fn-retain-obligation-id) (:d fn-retain-obligation-subject) (:d fn-retain-obligation-kind) (:d fn-retain-obligation-evidence) (:d fn-retain-obligation-charge) (:d fn-retain-make-obligation)))

(defun fn-retain-obligationp (x)
  (declare (xargs :guard t))
  (and (fn-retain-obligation-shapep x)
       (stringp (fn-retain-obligation-id x))
       (stringp (fn-retain-obligation-subject x))
       (fn-retain-kindp (fn-retain-obligation-kind x))
       (stringp (fn-retain-obligation-evidence x))
       (posp (fn-retain-obligation-charge x))))

(defthm fn-retain-obligationp-forward-shape
  (implies (fn-retain-obligationp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-retain-obligationp))))

(defun fn-retain-obligation-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-retain-obligationp (car xs))
           (fn-retain-obligation-listp (cdr xs)))
    (null xs)))

(defun fn-retain-obligation-ids (xs)
  (declare (xargs :guard (fn-retain-obligation-listp xs)))
  (if (consp xs)
      (cons (fn-retain-obligation-id (car xs))
            (fn-retain-obligation-ids (cdr xs)))
    nil))

(defun fn-retain-sum (pins)
  (declare (xargs :guard (fn-retain-obligation-listp pins)))
  (if (consp pins)
      (+ (fn-retain-obligation-charge (car pins))
         (fn-retain-sum (cdr pins)))
    0))

(defun fn-retain-find-id (id pins)
  (declare (xargs :guard (fn-retain-obligation-listp pins)))
  (if (consp pins)
      (if (equal id (fn-retain-obligation-id (car pins)))
          (car pins)
        (fn-retain-find-id id (cdr pins)))
    nil))

(defun fn-retain-remove-id (id pins)
  (declare (xargs :guard (fn-retain-obligation-listp pins)))
  (if (consp pins)
      (if (equal id (fn-retain-obligation-id (car pins)))
          (cdr pins)
        (cons (car pins) (fn-retain-remove-id id (cdr pins))))
    nil))

; A release record preserves the identity, subject, kind, and evidence that
; authorized the decision.  It is distinct from an active obligation.
(defun fn-retain-release-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))
(defun fn-retain-release-id (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-retain-release-subject (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-retain-release-kind (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-retain-release-evidence (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(defun fn-retain-make-release (id subject kind evidence)
  (declare (xargs :guard t))
  (list id subject kind evidence))

(defthm fn-retain-release-shapep-of-fn-retain-make-release
  (fn-retain-release-shapep (fn-retain-make-release id subject kind evidence)))
(defthm fn-retain-release-id-of-fn-retain-make-release
  (equal (fn-retain-release-id (fn-retain-make-release id subject kind evidence))
         id))
(defthm fn-retain-release-subject-of-fn-retain-make-release
  (equal (fn-retain-release-subject
          (fn-retain-make-release id subject kind evidence))
         subject))
(defthm fn-retain-release-kind-of-fn-retain-make-release
  (equal (fn-retain-release-kind
          (fn-retain-make-release id subject kind evidence))
         kind))
(defthm fn-retain-release-evidence-of-fn-retain-make-release
  (equal (fn-retain-release-evidence
          (fn-retain-make-release id subject kind evidence))
         evidence))

; What opacity takes away, exported back: the shape and a well-typed field
; each imply the record is a cons (forward-chaining, never rewrite).
(defthm fn-retain-release-shapep-forward-shape
  (implies (fn-retain-release-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-retain-release-shapep))))
(defthm fn-retain-release-accessors-forward-consp
  (and
   (implies (fn-retain-release-id x) (consp x))
   (implies (fn-retain-release-subject x) (consp x))
   (implies (fn-retain-release-kind x) (consp x))
   (implies (fn-retain-release-evidence x) (consp x))
   )
  :rule-classes
  ((:forward-chaining :corollary (implies (fn-retain-release-id x) (consp x))
                      :trigger-terms ((fn-retain-release-id x)))
   (:forward-chaining :corollary (implies (fn-retain-release-subject x) (consp x))
                      :trigger-terms ((fn-retain-release-subject x)))
   (:forward-chaining :corollary (implies (fn-retain-release-kind x) (consp x))
                      :trigger-terms ((fn-retain-release-kind x)))
   (:forward-chaining :corollary (implies (fn-retain-release-evidence x) (consp x))
                      :trigger-terms ((fn-retain-release-evidence x)))
   )
  :hints (("Goal" :in-theory (enable fn-retain-release-id fn-retain-release-subject fn-retain-release-kind fn-retain-release-evidence))))

(in-theory (disable (:d fn-retain-release-shapep) (:d fn-retain-release-id) (:d fn-retain-release-subject) (:d fn-retain-release-kind) (:d fn-retain-release-evidence) (:d fn-retain-make-release)))

(defun fn-retain-releasep (x)
  (declare (xargs :guard t))
  (and (fn-retain-release-shapep x)
       (stringp (fn-retain-release-id x))
       (stringp (fn-retain-release-subject x))
       (fn-retain-kindp (fn-retain-release-kind x))
       (stringp (fn-retain-release-evidence x))))

(defthm fn-retain-releasep-forward-shape
  (implies (fn-retain-releasep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-retain-releasep))))

(defun fn-retain-release-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-retain-releasep (car xs))
           (fn-retain-release-listp (cdr xs)))
    (null xs)))

(defun fn-retain-release-ids (xs)
  (declare (xargs :guard (fn-retain-release-listp xs)))
  (if (consp xs)
      (cons (fn-retain-release-id (car xs))
            (fn-retain-release-ids (cdr xs)))
    nil))

(defun fn-retain-known-idp (id pins releases)
  (declare (xargs :guard (and (fn-retain-obligation-listp pins)
                              (fn-retain-release-listp releases))))
  (or (member-equal id (fn-retain-obligation-ids pins))
      (member-equal id (fn-retain-release-ids releases))))

; -----------------------------------------------------------------------------
; Ledger state and transitions

; State: (finite-capacity reserved active-pins release-records).  `reserved`
; is stored explicitly and equals active charges plus one unit for every
; permanent release record.  This ledger unit is not yet a byte-accurate
; metadata layout, but it prevents unbounded release history at fixed capacity.
(defun fn-retain-state-shapep (s)
  (declare (xargs :guard t))
  (and (true-listp s) (equal (len s) 4)))
(defun fn-retain-capacity (s)
  (declare (xargs :guard t))
  (mbe :logic (car s) :exec (fn-ag-car s)))
(defun fn-retain-reserved (s)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr s)) :exec (fn-ag-car (fn-ag-cdr s))))
(defun fn-retain-pins (s)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr s)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))
(defun fn-retain-releases (s)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr s))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))

(defun fn-retain-make-state (capacity reserved pins releases)
  (declare (xargs :guard t))
  (list capacity reserved pins releases))

(defthm fn-retain-state-shapep-of-fn-retain-make-state
  (fn-retain-state-shapep
   (fn-retain-make-state capacity reserved pins releases)))
(defthm fn-retain-capacity-of-fn-retain-make-state
  (equal (fn-retain-capacity (fn-retain-make-state capacity reserved pins releases))
         capacity))
(defthm fn-retain-reserved-of-fn-retain-make-state
  (equal (fn-retain-reserved (fn-retain-make-state capacity reserved pins releases))
         reserved))
(defthm fn-retain-pins-of-fn-retain-make-state
  (equal (fn-retain-pins (fn-retain-make-state capacity reserved pins releases))
         pins))
(defthm fn-retain-releases-of-fn-retain-make-state
  (equal (fn-retain-releases (fn-retain-make-state capacity reserved pins releases))
         releases))

; What opacity takes away, exported back: the shape and a well-typed field
; each imply the record is a cons (forward-chaining, never rewrite).
(defthm fn-retain-state-shapep-forward-shape
  (implies (fn-retain-state-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-retain-state-shapep))))
(defthm fn-retain-state-accessors-forward-consp
  (and
   (implies (fn-retain-capacity x) (consp x))
   (implies (fn-retain-reserved x) (consp x))
   (implies (fn-retain-pins x) (consp x))
   (implies (fn-retain-releases x) (consp x))
   )
  :rule-classes
  ((:forward-chaining :corollary (implies (fn-retain-capacity x) (consp x))
                      :trigger-terms ((fn-retain-capacity x)))
   (:forward-chaining :corollary (implies (fn-retain-reserved x) (consp x))
                      :trigger-terms ((fn-retain-reserved x)))
   (:forward-chaining :corollary (implies (fn-retain-pins x) (consp x))
                      :trigger-terms ((fn-retain-pins x)))
   (:forward-chaining :corollary (implies (fn-retain-releases x) (consp x))
                      :trigger-terms ((fn-retain-releases x)))
   )
  :hints (("Goal" :in-theory (enable fn-retain-capacity fn-retain-reserved fn-retain-pins fn-retain-releases))))

(in-theory (disable (:d fn-retain-state-shapep) (:d fn-retain-capacity) (:d fn-retain-reserved) (:d fn-retain-pins) (:d fn-retain-releases) (:d fn-retain-make-state)))

(defun fn-retain-statep (s)
  (declare (xargs :guard t))
  (and (fn-retain-state-shapep s)
       (natp (fn-retain-capacity s))
       (natp (fn-retain-reserved s))
       (fn-retain-obligation-listp (fn-retain-pins s))
       (fn-retain-release-listp (fn-retain-releases s))
       (fn-retain-no-duplicatesp (fn-retain-obligation-ids
                                  (fn-retain-pins s)))
       (fn-retain-no-duplicatesp (fn-retain-release-ids
                                  (fn-retain-releases s)))
       (not (intersection-equal (fn-retain-obligation-ids
                                 (fn-retain-pins s))
                                (fn-retain-release-ids
                                 (fn-retain-releases s))))
       (equal (fn-retain-reserved s)
              (+ (fn-retain-sum (fn-retain-pins s))
                 (len (fn-retain-releases s))))
       (<= (fn-retain-reserved s) (fn-retain-capacity s))))

(defthm fn-retain-statep-forward-shape
  (implies (fn-retain-statep s) (and (consp s) (true-listp s)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-retain-statep))))

(defun fn-retain-initial-state (capacity)
  (declare (xargs :guard t))
  (fn-retain-make-state capacity 0 nil nil))

; Admissibility is decided under the carried invariant: the :logic body keeps
; the whole-state recognizer as its first conjunct, the :exec path relies on
; the guard.
(defun fn-retain-admissiblep (s id subject kind evidence charge)
  (declare (xargs :guard (fn-retain-statep s)))
  (and (mbe :logic (fn-retain-statep s) :exec t)
       (stringp id)
       (stringp subject)
       (fn-retain-kindp kind)
       (stringp evidence)
       (posp charge)
       (not (fn-retain-known-idp id (fn-retain-pins s)
                                 (fn-retain-releases s)))
       (<= (+ (fn-retain-reserved s) charge)
           (fn-retain-capacity s))))

; Refusal occurs before creating any pin or reservation.
(defun fn-retain-admit (s id subject kind evidence charge)
  (declare (xargs :guard (fn-retain-statep s)))
  (if (fn-retain-admissiblep s id subject kind evidence charge)
      (fn-retain-make-state
       (fn-retain-capacity s)
       (+ (fn-retain-reserved s) charge)
       (cons (fn-retain-make-obligation id subject kind evidence charge)
             (fn-retain-pins s))
       (fn-retain-releases s))
    s))

(defun fn-retain-matching-releasep (pin id subject kind evidence)
  (declare (xargs :guard t))
  (and (consp pin)
       (equal id (fn-retain-obligation-id pin))
       (equal subject (fn-retain-obligation-subject pin))
       (equal kind (fn-retain-obligation-kind pin))
       (equal evidence (fn-retain-obligation-evidence pin))))

; The found pin is an obligation, so its charge is a number: a guard fact,
; local and used by :use.
(local
 (defthm fn-retain-guard-find-is-obligation
   (implies (and (fn-retain-obligation-listp pins)
                 (consp (fn-retain-find-id id pins)))
            (fn-retain-obligationp (fn-retain-find-id id pins)))))

; The caller supplies evidence only after its authentication/authorization and
; durable-commit boundary.  A forwarding receipt and a local archive release
; have distinct kind/evidence values, so either cannot discharge the other.
; Release retains the one-unit history charge; a charge of one frees no space.
(defun fn-retain-release (s id subject kind evidence)
  (declare
   (xargs :guard (fn-retain-statep s)
          :guard-hints
          (("Goal"
            :use ((:instance fn-retain-guard-find-is-obligation
                             (pins (fn-retain-pins s))))))))
  (if (mbe :logic (not (fn-retain-statep s)) :exec nil)
      s
    (let ((pin (fn-retain-find-id id (fn-retain-pins s))))
      (if (fn-retain-matching-releasep pin id subject kind evidence)
          (fn-retain-make-state
           (fn-retain-capacity s)
           (+ 1 (- (fn-retain-reserved s) (fn-retain-obligation-charge pin)))
           (fn-retain-remove-id id (fn-retain-pins s))
           (cons (fn-retain-make-release id subject kind evidence)
                 (fn-retain-releases s)))
        s))))

; Verify the complete executable retention graph.  Public recognizers stay
; total; the three ledger transitions carry `fn-retain-statep'; structural
; folds require typed lists.
(verify-guards fn-retain-kindp)
(verify-guards fn-retain-string-listp)
(verify-guards fn-retain-no-duplicatesp)
(verify-guards fn-retain-obligation-shapep)
(verify-guards fn-retain-obligation-id)
(verify-guards fn-retain-obligation-subject)
(verify-guards fn-retain-obligation-kind)
(verify-guards fn-retain-obligation-evidence)
(verify-guards fn-retain-obligation-charge)
(verify-guards fn-retain-make-obligation)
(verify-guards fn-retain-obligationp)
(verify-guards fn-retain-obligation-listp)
(verify-guards fn-retain-obligation-ids)
(verify-guards fn-retain-sum)
(verify-guards fn-retain-find-id)
(verify-guards fn-retain-remove-id)
(verify-guards fn-retain-release-shapep)
(verify-guards fn-retain-release-id)
(verify-guards fn-retain-release-subject)
(verify-guards fn-retain-release-kind)
(verify-guards fn-retain-release-evidence)
(verify-guards fn-retain-make-release)
(verify-guards fn-retain-releasep)
(verify-guards fn-retain-release-listp)
(verify-guards fn-retain-release-ids)
(verify-guards fn-retain-known-idp)
(verify-guards fn-retain-state-shapep)
(verify-guards fn-retain-capacity)
(verify-guards fn-retain-reserved)
(verify-guards fn-retain-pins)
(verify-guards fn-retain-releases)
(verify-guards fn-retain-make-state)
(verify-guards fn-retain-statep)
(verify-guards fn-retain-initial-state)
(verify-guards fn-retain-admissiblep)
(verify-guards fn-retain-admit)
(verify-guards fn-retain-matching-releasep)
(verify-guards fn-retain-release)

; -----------------------------------------------------------------------------
; Mechanical safety properties for the abstract ledger.

(defthm fn-retain-initial-state-is-state
  (implies (natp capacity)
           (fn-retain-statep (fn-retain-initial-state capacity)))
  :hints (("Goal" :in-theory (enable fn-retain-initial-state
                                      fn-retain-statep))))

(defthm fn-retain-accounting-nonnegative
  (implies (fn-retain-statep s)
           (natp (fn-retain-reserved s)))
  :hints (("Goal" :in-theory (enable fn-retain-statep))))

(defthm fn-retain-accounting-within-capacity
  (implies (fn-retain-statep s)
           (<= (fn-retain-reserved s) (fn-retain-capacity s)))
  :hints (("Goal" :in-theory (enable fn-retain-statep))))

; The two `-by-definition' facts below restate a branch of the transition
; with the branch test as hypothesis.  They are not registry events and are
; not rewrite rules; a proof that needs one uses it by :use.
(defthm fn-retain-admission-refusal-is-no-op
  (implies (not (fn-retain-admissiblep s id subject kind evidence charge))
           (equal (fn-retain-admit s id subject kind evidence charge) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-retain-admit))))

(defthm fn-retain-admission-conserves-charge
  (implies (fn-retain-admissiblep s id subject kind evidence charge)
           (equal (fn-retain-reserved
                   (fn-retain-admit s id subject kind evidence charge))
                  (+ (fn-retain-reserved s) charge)))
  :hints (("Goal" :in-theory (enable fn-retain-admit))))

(defthm fn-retain-admit-preserves-statep
  (implies (fn-retain-statep s)
           (fn-retain-statep
            (fn-retain-admit s id subject kind evidence charge)))
  :hints (("Goal" :in-theory (enable fn-retain-admit
                                      fn-retain-admissiblep
                                      fn-retain-statep))))

(defthm fn-retain-admission-binds-subject-immutably
  (implies (fn-retain-admissiblep s id subject kind evidence charge)
           (equal (fn-retain-find-id
                   id
                   (fn-retain-pins
                    (fn-retain-admit s id subject kind evidence charge)))
                  (fn-retain-make-obligation id subject kind evidence charge)))
  :hints (("Goal" :in-theory (enable fn-retain-admit))))

; A known identity refuses admission whatever the rest of the ledger is: the
; former `(fn-retain-statep s)' hypothesis was unnecessary (admissibility
; already fails on a non-state) and is dropped, as the teeth book recorded.
(defthm fn-retain-known-obligation-id-is-not-reused
  (implies (fn-retain-known-idp id (fn-retain-pins s)
                                (fn-retain-releases s))
           (equal (fn-retain-admit s id subject kind evidence charge) s))
  :hints (("Goal" :in-theory (enable fn-retain-admit
                                      fn-retain-admissiblep))))

(defthm fn-retain-wrong-evidence-does-not-release
  (implies (and (fn-retain-statep s)
                (not (fn-retain-matching-releasep
                      (fn-retain-find-id id (fn-retain-pins s))
                      id subject kind evidence)))
           (equal (fn-retain-release s id subject kind evidence) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-retain-release))))

(defthm fn-retain-exact-release-records-its-evidence
  (implies (and (fn-retain-statep s)
                (fn-retain-matching-releasep
                 (fn-retain-find-id id (fn-retain-pins s))
                 id subject kind evidence))
           (equal (car (fn-retain-releases
                        (fn-retain-release s id subject kind evidence)))
                  (fn-retain-make-release id subject kind evidence)))
  :hints (("Goal" :in-theory (enable fn-retain-release))))

; -----------------------------------------------------------------------------
; Export.  Records were disabled at their definitions.  Recognizers, the
; initial state and the three ledger transitions are withdrawn here.  The
; list folds, `fn-retain-known-idp' and `fn-retain-matching-releasep' stay
; enabled: they are accessor-vocabulary glue that theorem statements use.
(in-theory (disable (:d fn-retain-obligationp) (:d fn-retain-releasep) (:d fn-retain-statep) (:d fn-retain-initial-state) (:d fn-retain-admissiblep) (:d fn-retain-admit) (:d fn-retain-release)))
