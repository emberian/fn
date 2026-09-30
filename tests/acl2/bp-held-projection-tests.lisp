; Teeth for books/bp-held-projection.lisp (lane bp-catalog).
; The witness is bp-fnbs-family-replay-tests' journal: two kind-5 arrivals
; (a two-fragment family, the offset-2 fragment before the offset-0 one)
; and the kind-18 family row that reassembles them.
(in-package "ACL2")
(include-book "../../books/bp-recovery-guards")
(include-book "bp-fnbs-family-replay-tests")
(include-book "must-fail-checked")

(defun bphpt-base () (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-base *bpnff-state*))

; Positive witness of fn-bphp-replay-rows-is-aux, antecedent and conclusion:
; every prefix of the journal (coverage after each row), the relation at the
; entry (empty held list, octets 0), the projected fold equal to the spec,
; and the spec :ready (non-degenerate: the family row reassembles).
(defun bphpt-prefix (n) (declare (xargs :guard t :verify-guards nil))
  (take n (bpnfr-replay-rows)))
(assert-event (equal 0 (fn-bpnf-held-octets nil)))
(assert-event
 (and (equal (fn-bphp-replay-rows (bphpt-prefix 1) (bphpt-base) nil nil nil 0 0)
             (fn-bpnf-family-replay-rows-aux (bphpt-prefix 1) (bphpt-base) nil nil nil 0))
      (equal (car (fn-bpnf-family-replay-rows-aux (bphpt-prefix 1) (bphpt-base) nil nil nil 0))
             :ready)
      (equal (len (nth 1 (fn-bpnf-family-replay-rows-aux (bphpt-prefix 1) (bphpt-base) nil nil nil 0)))
             1)))
(assert-event
 (and (equal (fn-bphp-replay-rows (bphpt-prefix 2) (bphpt-base) nil nil nil 0 0)
             (fn-bpnf-family-replay-rows-aux (bphpt-prefix 2) (bphpt-base) nil nil nil 0))
      (equal (len (nth 1 (fn-bpnf-family-replay-rows-aux (bphpt-prefix 2) (bphpt-base) nil nil nil 0)))
             2)))
(assert-event
 (and (equal (fn-bphp-replay-rows (bpnfr-replay-rows) (bphpt-base) nil nil nil 0 0)
             (fn-bpnf-family-replay-rows-aux (bpnfr-replay-rows) (bphpt-base) nil nil nil 0))
      (equal (car (bpnfr-replay-answer)) :ready)
      (equal (fn-bpnf-held-wire (car (nth 1 (bpnfr-replay-answer))))
             (nth 2 *bpnfr-replay-plan*))))

; The relation mid-fold: from the one-row state the projected fold with the
; state's own octet total equals the spec.
(defun bphpt-held1 () (declare (xargs :guard t :verify-guards nil))
  (nth 1 (fn-bpnf-family-replay-rows-aux (bphpt-prefix 1) (bphpt-base) nil nil nil 0)))
(assert-event
 (let ((o (fn-bpnf-held-octets (bphpt-held1))))
   (and (< 0 o)
        (equal (fn-bphp-replay-rows (cdr (bpnfr-replay-rows)) (bphpt-base)
                                    (bphpt-held1) nil (cons 3 0) 1 o)
               (fn-bpnf-family-replay-rows-aux (cdr (bpnfr-replay-rows)) (bphpt-base)
                                               (bphpt-held1) nil (cons 3 0) 1)))))

; Hypothesis removal: with OCTETS not the held list's total the projected fold
; is NOT the spec (a projection past the profile's bound refuses a journal the
; spec admits).  The retained parts hold: the spec is :ready on those rows.
(assert-event
 (equal (car (fn-bpnf-family-replay-rows-aux (bpnfr-replay-rows) (bphpt-base) nil nil nil 0))
        :ready))
(assert-event
 (not (equal (fn-bpnf-held-octets nil) (fn-bpn-machine-state-max-octets (bphpt-base)))))
(assert-event
 (equal (car (fn-bphp-replay-rows (bpnfr-replay-rows) (bphpt-base) nil nil nil 0
                                  (fn-bpn-machine-state-max-octets (bphpt-base))))
        :fault))
(must-fail-checked
 (assert-event
  (equal (fn-bphp-replay-rows (bpnfr-replay-rows) (bphpt-base) nil nil nil 0
                              (fn-bpn-machine-state-max-octets (bphpt-base)))
         (fn-bpnf-family-replay-rows-aux (bpnfr-replay-rows) (bphpt-base) nil nil nil 0))))

; The host entry over the same journal, no checkpoint (plan (:none)): the
; event equals fn-bpnr-recover-auto-event's.
(defconst *bphpt-st* (fn-bpnf-state (fn-bpnf-base *bpnff-state*) nil nil nil nil nil nil 0 0))
(assert-event
 (equal (fn-bphp-recover-auto-event *bphpt-st* nil :ready (bpnfr-replay-rows) '(:none))
        (fn-bpnr-recover-auto-event *bphpt-st* nil :ready (bpnfr-replay-rows) '(:none))))
(assert-event
 (equal (car (fn-bpn-nth 4 (fn-bphp-recover-auto-event *bphpt-st* nil :ready
                                                       (bpnfr-replay-rows) '(:none))))
        :ready))

; The one-pass recovery check (books/bp-node-foundation.lisp,
; fn-bpnf-recovery-heldp-fast-is-logic): on the replayed held list both
; forms admit under the profile and both refuse one octet below its total.
(defun bphpt-held () (declare (xargs :guard t :verify-guards nil))
  (nth 1 (bpnfr-replay-answer)))
(assert-event
 (let ((o (fn-bpnf-held-octets (bphpt-held))))
   (and (equal (fn-bpnf-recovery-heldp-fast (bphpt-held) 8 o) t)
        (equal (fn-bpnf-recovery-heldp (bphpt-held) 8 o) t)
        (equal (fn-bpnf-recovery-heldp-fast (bphpt-held) 8 (1- o)) nil)
        (equal (fn-bpnf-recovery-heldp (bphpt-held) 8 (1- o)) nil)
        (equal (fn-bpnf-recovery-heldp-fast (bphpt-held) 0 o) nil)
        (equal (fn-bpnf-recovery-heldp (bphpt-held) 0 o) nil))))

; The host's actual recovery subject is guard-verified in this world, and
; the named refinement theorem mentions that subject directly.
(assert-event
 (and (eq (symbol-class 'fn-bphp-recover-auto-event (w state))
          :common-lisp-compliant)
      (member-eq 'fn-bphp-recover-auto-event
                 (all-fnnames
                  (getpropc 'fn-bphp-recover-auto-event-is-bpnr
                            'theorem nil (w state))))))
