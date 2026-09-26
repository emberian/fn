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
(include-book "defrecord")
(include-book "provenance")

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

; Quadratic in :logic; linear in :exec through `fn-no-duplicatesp' (a hash
; set for long lists, books/acceptance-alloc.lisp), equal by
; `fn-retain-no-duplicatesp-is-no-duplicatesp' (checkpoint-cost, PKT-142).
(defun fn-retain-no-duplicatesp (xs)
  (declare (xargs :guard (true-listp xs) :verify-guards nil))
  (mbe :logic
       (if (consp xs)
           (and (not (member-equal (car xs) (cdr xs)))
                (fn-retain-no-duplicatesp (cdr xs)))
         t)
       :exec (fn-no-duplicatesp xs)))

(defthmd fn-retain-no-duplicatesp-is-no-duplicatesp
  (equal (fn-retain-no-duplicatesp xs) (fn-no-duplicatesp xs)))

(verify-guards fn-retain-no-duplicatesp
  :hints (("Goal" :use fn-retain-no-duplicatesp-is-no-duplicatesp)))

; Obligation: (identity immutable-subject kind required-evidence charge).
; A positive charge includes at least one permanent history unit; the remaining
; charge is active content/evidence retained while the obligation is pinned.
(fn-defrecord fn-retain-obligation
  :constructor (fn-retain-make-obligation id subject kind evidence charge)
  :fields ((fn-retain-obligation-id stringp)
           (fn-retain-obligation-subject stringp)
           (fn-retain-obligation-kind
            (fn-retain-kindp (fn-retain-obligation-kind x)))
           (fn-retain-obligation-evidence fn-provp)
           (fn-retain-obligation-charge posp)))

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
(fn-defrecord fn-retain-release
  :constructor (fn-retain-make-release id subject kind evidence)
  :fields ((fn-retain-release-id stringp)
           (fn-retain-release-subject stringp)
           (fn-retain-release-kind
            (fn-retain-kindp (fn-retain-release-kind x)))
           (fn-retain-release-evidence fn-provp)))

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

; The admission test the host executes (served-path-scale, PRF-173): the same
; question asked by walking the pins and the releases, without consing their
; identity lists first.  `fn-retain-known-idp' built both lists on every
; admission -- every POST and every step of a full replay -- which was 26.8
; percent of the 20,000-article fixture's full-replay open (sb-sprof,
; planning/evidence/served-path-scale-2026-09-26.md).  Equal as a truth value
; by `fn-retain-known-id-scanp-is-known-idp'; `fn-retain-admissiblep' runs it
; through `mbe', so no logical definition changes.
(defun fn-retain-pin-id-scanp (id pins)
  (declare (xargs :guard (fn-retain-obligation-listp pins)))
  (if (consp pins)
      (or (equal id (fn-retain-obligation-id (car pins)))
          (fn-retain-pin-id-scanp id (cdr pins)))
    nil))

(defun fn-retain-release-id-scanp (id releases)
  (declare (xargs :guard (fn-retain-release-listp releases)))
  (if (consp releases)
      (or (equal id (fn-retain-release-id (car releases)))
          (fn-retain-release-id-scanp id (cdr releases)))
    nil))

(defun fn-retain-known-id-scanp (id pins releases)
  (declare (xargs :guard (and (fn-retain-obligation-listp pins)
                              (fn-retain-release-listp releases))))
  (or (fn-retain-pin-id-scanp id pins)
      (fn-retain-release-id-scanp id releases)))

(local
 (defthm fn-retain-pin-id-scanp-is-member
   (iff (fn-retain-pin-id-scanp id pins)
        (member-equal id (fn-retain-obligation-ids pins)))))

(local
 (defthm fn-retain-release-id-scanp-is-member
   (iff (fn-retain-release-id-scanp id releases)
        (member-equal id (fn-retain-release-ids releases)))))

(defthm fn-retain-known-id-scanp-is-known-idp
  (iff (fn-retain-known-id-scanp id pins releases)
       (fn-retain-known-idp id pins releases)))

; -----------------------------------------------------------------------------
; Ledger state and transitions

; State: (finite-capacity reserved active-pins release-records).  `reserved`
; is stored explicitly and equals active charges plus one unit for every
; permanent release record.  This ledger unit is not yet a byte-accurate
; metadata layout, but it prevents unbounded release history at fixed capacity.
; The conjuncts of `fn-retain-statep' keep the order they were written in:
; each whole-state conjunct rides with the last field it reads, so the
; recognizer ACL2 admits is the same term as before.

(fn-defrecord fn-retain-state
  :constructor (fn-retain-make-state capacity reserved pins releases)
  :fields ((fn-retain-capacity natp)
           (fn-retain-reserved natp)
           (fn-retain-pins (fn-retain-obligation-listp (fn-retain-pins x)))
           (fn-retain-releases
            (and (fn-retain-release-listp (fn-retain-releases x))
                 (fn-retain-no-duplicatesp (fn-retain-obligation-ids
                                            (fn-retain-pins x)))
                 (fn-retain-no-duplicatesp (fn-retain-release-ids
                                            (fn-retain-releases x)))
                 (not (intersection-equal (fn-retain-obligation-ids
                                           (fn-retain-pins x))
                                          (fn-retain-release-ids
                                           (fn-retain-releases x))))
                 (equal (fn-retain-reserved x)
                        (+ (fn-retain-sum (fn-retain-pins x))
                           (len (fn-retain-releases x))))
                 (<= (fn-retain-reserved x) (fn-retain-capacity x))))))

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
       (fn-provp evidence)
       (posp charge)
       (mbe :logic (not (fn-retain-known-idp id (fn-retain-pins s)
                                             (fn-retain-releases s)))
            :exec (not (fn-retain-known-id-scanp id (fn-retain-pins s)
                                                 (fn-retain-releases s))))
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
(verify-guards fn-retain-pin-id-scanp)
(verify-guards fn-retain-release-id-scanp)
(verify-guards fn-retain-known-id-scanp)
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
