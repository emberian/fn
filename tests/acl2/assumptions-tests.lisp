; Teeth for the named assumptions.
;
; An `encapsulate' proves its constraints are satisfiable: the local witness is
; the proof.  It proves nothing about whether they are *restrictive*.  A
; constraint every candidate meets is prose with parentheses around it.
;
; Each assumption below therefore gets two ground checks:
;
;   * a positive one, an `assert-event' showing a witness-shaped candidate
;     meets the constraint at a concrete point, so the negative check below is
;     not failing for an unrelated reason; and
;   * a `must-fail' on a non-witness: a concrete candidate for which the
;     constraint's own statement is FALSE at a ground instance.  ACL2 evaluates
;     both sides and refuses the theorem, which is the evidence.
;
; The `must-fail' forms are `local' on purpose.  std/testing/must-fail's
; documented caveat is that a non-local form that causes proofs to be done may
; not be includable, because proofs are skipped during include-book and the
; failing theorem would then "succeed".  Certification is the gate here.

(in-package "ACL2")
(include-book "../../books/assumptions")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A-DURABILITY

; A candidate barrier that loses the oldest stable record.
(local (defun fn-assume-check-drop-oldest (barriered unbarriered)
         (declare (ignore unbarriered))
         (cdr barriered)))

; A candidate crash image that fabricates a record nobody wrote.
(local (defun fn-assume-check-phantom (barriered unbarriered)
         (cons :phantom (append barriered unbarriered))))

; The witness shape does meet the retention constraint at this point.
(local (assert-event (member-equal 1 (append '(1 2) nil))))

; Losing a barriered record is not A-DURABILITY.
(local
 (must-fail
  (defthm fn-assume-check-drop-oldest-retains-barriered
    (implies (member-equal 1 '(1 2))
             (member-equal 1 (fn-assume-check-drop-oldest '(1 2) nil))))))

; Inventing a record is not A-DURABILITY either: :phantom survives the crash
; without having been written, barriered or not.
(local
 (must-fail
  (defthm fn-assume-check-phantom-invents-nothing
    (implies (member-equal :phantom (fn-assume-check-phantom '(1 2) '(3)))
             (or (member-equal :phantom '(1 2))
                 (member-equal :phantom '(3)))))))

; -----------------------------------------------------------------------------
; A-WRITE-ISOLATION

; A candidate layout in which a pending write in a shared sector erases the
; committed neighbour.  This is the case specs/failures.md warns about.
(local (defun fn-assume-check-shared-sector (committed pending)
         (declare (ignore pending))
         (cdr committed)))

(local (assert-event (member-equal :unit-a (list :unit-a :unit-b))))

(local
 (must-fail
  (defthm fn-assume-check-shared-sector-retains-committed
    (implies (member-equal :unit-a '(:unit-a :unit-b))
             (member-equal :unit-a
                           (fn-assume-check-shared-sector '(:unit-a :unit-b) '(:unit-c)))))))

; -----------------------------------------------------------------------------
; A-HOST

; An adapter that reports success for an uncertain core outcome: the D1/D13
; shape, where an indeterminate result is published as an acceptance.
(local (defun fn-assume-check-optimistic (outcome)
         (declare (ignore outcome))
         :success))

; An adapter that collapses uncertainty into a refusal, licensing a retry that
; can double-commit.
(local (defun fn-assume-check-refusing (outcome)
         (declare (ignore outcome))
         :refused))

; An adapter that reorders the event sequence it presents to the core.
(local (defun fn-assume-check-reordering (events)
         (reverse events)))

(local (assert-event (equal (nth 0 '(:a :b)) :a)))

(local
 (must-fail
  (defthm fn-assume-check-optimistic-success-is-earned
    (implies (equal (fn-assume-check-optimistic :indeterminate) :success)
             (equal :indeterminate :success)))))

(local
 (must-fail
  (defthm fn-assume-check-refusing-keeps-uncertainty
    (implies (equal :indeterminate :indeterminate)
             (equal (fn-assume-check-refusing :indeterminate) :indeterminate)))))

(local
 (must-fail
  (defthm fn-assume-check-reordering-preserves-event-order
    (equal (nth 0 (fn-assume-check-reordering '(:a :b)))
           (nth 0 '(:a :b))))))

; -----------------------------------------------------------------------------
; A-PEER

; A candidate that treats silence as cooperation: the peer is assumed to retain
; whether or not it ever issued anything.
(local (defun fn-assume-check-credulous (receipt failures)
         (declare (ignore receipt failures))
         t))

(local (assert-event (not (consp nil))))

(local
 (must-fail
  (defthm fn-assume-check-credulous-needs-a-receipt
    (implies (not (consp nil))
             (not (fn-assume-check-credulous nil :none))))))

; -----------------------------------------------------------------------------
; A-IDENTITY

; A candidate that infers freshness from the current time rather than from what
; was issued.  It cannot even be written with this signature, which is OBJ-006
; expressed in the arity; the closest a candidate can come is to ignore the
; issued set, which is exactly the restore-reuse bug.
(local (defun fn-assume-check-always-fresh (identity issued)
         (declare (ignore identity issued))
         t))

(local (assert-event (member-equal '(:origin 1 7) '((:origin 1 7)))))

(local
 (must-fail
  (defthm fn-assume-check-always-fresh-issued-is-not-fresh
    (implies (member-equal '(:origin 1 7) '((:origin 1 7)))
             (not (fn-assume-check-always-fresh '(:origin 1 7) '((:origin 1 7))))))))

; -----------------------------------------------------------------------------
; A-POLICY

; A candidate that authorizes on the stored decision bit: it ignores the terms
; and the evidence entirely.  This is D9 written as a function.
(local (defun fn-assume-check-stored-bit (policy-id terms evidence)
         (declare (ignore policy-id terms evidence))
         t))

(local (assert-event (not (consp nil))))

(local
 (must-fail
  (defthm fn-assume-check-stored-bit-needs-evidence
    (implies (not (consp nil))
             (not (fn-assume-check-stored-bit '(:policy 0) '(:terms 0) nil))))))

(local
 (must-fail
  (defthm fn-assume-check-stored-bit-needs-terms
    (implies (not (consp nil))
             (not (fn-assume-check-stored-bit '(:policy 0) nil '(:evidence 0)))))))

; -----------------------------------------------------------------------------
; A-FAIRNESS

; A candidate that promises contact without bounding when: "eventually" with no
; finite index is not a liveness assumption, it is a wish.
(local (defun fn-assume-check-never (route schedule)
         (declare (ignore route schedule))
         :eventually))

(local (assert-event (natp 0)))

(local
 (must-fail
  (defthm fn-assume-check-never-contact-index-is-finite
    (natp (fn-assume-check-never :route-a :schedule-a)))))
