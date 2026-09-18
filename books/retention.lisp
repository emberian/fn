; fn M1 retention ledger: executable, finite-capacity obligation accounting.
;
; A pin charges capacity once per obligation.  This is intentionally
; conservative: it does not deduplicate bytes shared by several obligations.
; An implementation that deduplicates needs a correspondence argument before it
; can replace this ledger.  Evidence equality is an executable stand-in for an
; already authenticated and locally committed authorization event; this book
; neither implements cryptography nor proves peer honesty or disk durability.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Records and finite-list utilities

(defun fn-retain-kindp (kind)
  (or (equal kind :archive)
      (equal kind :forward)))

(defun fn-retain-string-listp (xs)
  (if (consp xs)
      (and (stringp (car xs))
           (fn-retain-string-listp (cdr xs)))
    (null xs)))

(defun fn-retain-no-duplicatesp (xs)
  (if (consp xs)
      (and (not (member-equal (car xs) (cdr xs)))
           (fn-retain-no-duplicatesp (cdr xs)))
    t))

; Obligation: (identity immutable-subject kind required-evidence charge).
(defun fn-retain-obligation-id (x) (car x))
(defun fn-retain-obligation-subject (x) (car (cdr x)))
(defun fn-retain-obligation-kind (x) (car (cdr (cdr x))))
(defun fn-retain-obligation-evidence (x) (car (cdr (cdr (cdr x)))))
(defun fn-retain-obligation-charge (x) (car (cdr (cdr (cdr (cdr x))))))

(defun fn-retain-make-obligation (id subject kind evidence charge)
  (list id subject kind evidence charge))

(defun fn-retain-obligationp (x)
  (and (true-listp x)
       (equal (len x) 5)
       (stringp (fn-retain-obligation-id x))
       (stringp (fn-retain-obligation-subject x))
       (fn-retain-kindp (fn-retain-obligation-kind x))
       (stringp (fn-retain-obligation-evidence x))
       (posp (fn-retain-obligation-charge x))))

(defun fn-retain-obligation-listp (xs)
  (if (consp xs)
      (and (fn-retain-obligationp (car xs))
           (fn-retain-obligation-listp (cdr xs)))
    (null xs)))

(defun fn-retain-obligation-ids (xs)
  (if (consp xs)
      (cons (fn-retain-obligation-id (car xs))
            (fn-retain-obligation-ids (cdr xs)))
    nil))

(defun fn-retain-sum (pins)
  (if (consp pins)
      (+ (fn-retain-obligation-charge (car pins))
         (fn-retain-sum (cdr pins)))
    0))

(defun fn-retain-find-id (id pins)
  (if (consp pins)
      (if (equal id (fn-retain-obligation-id (car pins)))
          (car pins)
        (fn-retain-find-id id (cdr pins)))
    nil))

(defun fn-retain-remove-id (id pins)
  (if (consp pins)
      (if (equal id (fn-retain-obligation-id (car pins)))
          (cdr pins)
        (cons (car pins) (fn-retain-remove-id id (cdr pins))))
    nil))

; A release record preserves the identity, subject, kind, and evidence that
; authorized the decision.  It is distinct from an active obligation.
(defun fn-retain-release-id (x) (car x))
(defun fn-retain-release-subject (x) (car (cdr x)))
(defun fn-retain-release-kind (x) (car (cdr (cdr x))))
(defun fn-retain-release-evidence (x) (car (cdr (cdr (cdr x)))))

(defun fn-retain-make-release (id subject kind evidence)
  (list id subject kind evidence))

(defun fn-retain-releasep (x)
  (and (true-listp x)
       (equal (len x) 4)
       (stringp (fn-retain-release-id x))
       (stringp (fn-retain-release-subject x))
       (fn-retain-kindp (fn-retain-release-kind x))
       (stringp (fn-retain-release-evidence x))))

(defun fn-retain-release-listp (xs)
  (if (consp xs)
      (and (fn-retain-releasep (car xs))
           (fn-retain-release-listp (cdr xs)))
    (null xs)))

(defun fn-retain-release-ids (xs)
  (if (consp xs)
      (cons (fn-retain-release-id (car xs))
            (fn-retain-release-ids (cdr xs)))
    nil))

(defun fn-retain-known-idp (id pins releases)
  (or (member-equal id (fn-retain-obligation-ids pins))
      (member-equal id (fn-retain-release-ids releases))))

; -----------------------------------------------------------------------------
; Ledger state and transitions

; State: (finite-capacity reserved active-pins release-records).  `reserved`
; is stored explicitly and must equal the active per-obligation charge sum.
(defun fn-retain-capacity (s) (car s))
(defun fn-retain-reserved (s) (car (cdr s)))
(defun fn-retain-pins (s) (car (cdr (cdr s))))
(defun fn-retain-releases (s) (car (cdr (cdr (cdr s)))))

(defun fn-retain-make-state (capacity reserved pins releases)
  (list capacity reserved pins releases))

(defun fn-retain-statep (s)
  (and (true-listp s)
       (equal (len s) 4)
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
              (fn-retain-sum (fn-retain-pins s)))
       (<= (fn-retain-reserved s) (fn-retain-capacity s))))

(defun fn-retain-initial-state (capacity)
  (fn-retain-make-state capacity 0 nil nil))

(defun fn-retain-admissiblep (s id subject kind evidence charge)
  (and (fn-retain-statep s)
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
  (if (fn-retain-admissiblep s id subject kind evidence charge)
      (fn-retain-make-state
       (fn-retain-capacity s)
       (+ (fn-retain-reserved s) charge)
       (cons (fn-retain-make-obligation id subject kind evidence charge)
             (fn-retain-pins s))
       (fn-retain-releases s))
    s))

(defun fn-retain-matching-releasep (pin id subject kind evidence)
  (and (consp pin)
       (equal id (fn-retain-obligation-id pin))
       (equal subject (fn-retain-obligation-subject pin))
       (equal kind (fn-retain-obligation-kind pin))
       (equal evidence (fn-retain-obligation-evidence pin))))

; The caller supplies evidence only after its authentication/authorization and
; durable-commit boundary.  A forwarding receipt and a local archive release
; have distinct kind/evidence values, so either cannot discharge the other.
(defun fn-retain-release (s id subject kind evidence)
  (if (not (fn-retain-statep s))
      s
    (let ((pin (fn-retain-find-id id (fn-retain-pins s))))
      (if (fn-retain-matching-releasep pin id subject kind evidence)
          (fn-retain-make-state
           (fn-retain-capacity s)
           (- (fn-retain-reserved s) (fn-retain-obligation-charge pin))
           (fn-retain-remove-id id (fn-retain-pins s))
           (cons (fn-retain-make-release id subject kind evidence)
                 (fn-retain-releases s)))
        s))))

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

(defthm fn-retain-admission-refusal-is-no-op
  (implies (not (fn-retain-admissiblep s id subject kind evidence charge))
           (equal (fn-retain-admit s id subject kind evidence charge) s))
  :hints (("Goal" :in-theory (enable fn-retain-admit))))

(defthm fn-retain-admission-conserves-charge
  (implies (fn-retain-admissiblep s id subject kind evidence charge)
           (equal (fn-retain-reserved
                   (fn-retain-admit s id subject kind evidence charge))
                  (+ (fn-retain-reserved s) charge)))
  :hints (("Goal" :in-theory (enable fn-retain-admit))))

(defthm fn-retain-admission-binds-subject-immutably
  (implies (fn-retain-admissiblep s id subject kind evidence charge)
           (equal (fn-retain-find-id
                   id
                   (fn-retain-pins
                    (fn-retain-admit s id subject kind evidence charge)))
                  (fn-retain-make-obligation id subject kind evidence charge)))
  :hints (("Goal" :in-theory (enable fn-retain-admit))))

(defthm fn-retain-known-obligation-id-is-not-reused
  (implies (and (fn-retain-statep s)
                (fn-retain-known-idp id (fn-retain-pins s)
                                     (fn-retain-releases s)))
           (equal (fn-retain-admit s id subject kind evidence charge) s))
  :hints (("Goal" :in-theory (enable fn-retain-admit
                                      fn-retain-admissiblep))))

(defthm fn-retain-wrong-evidence-does-not-release
  (implies (and (fn-retain-statep s)
                (not (fn-retain-matching-releasep
                      (fn-retain-find-id id (fn-retain-pins s))
                      id subject kind evidence)))
           (equal (fn-retain-release s id subject kind evidence) s))
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
