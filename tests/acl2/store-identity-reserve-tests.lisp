(in-package "ACL2")
(include-book "../../books/store-identity-reserve")
(include-book "../../books/store-log-route")
(include-book "../../books/store-observed")
(include-book "../../books/store-capacity-vector")
(include-book "../../books/codec-attach")

(defconst *idr-undertake* '(:undertake "work-1" "subject-1" "receipt-1" 2))
(defconst *idr-release* '(:release "work-1" "subject-1" "receipt-1" 0))
(defconst *idr-initial* (fn-sn-initial '("fn.test") 16))
(defconst *idr-record* (fn-idr-retention-candidate *idr-initial* *idr-undertake*))
(defconst *idr-held*
  (fn-sn-finish (fn-olr-sn-order
    (fn-sn-prepare-retention (fn-olr-sn-reserve *idr-initial*) *idr-record*))))

(defun idr-test-recovery (n s)
  (if (zp n) s
    (idr-test-recovery (1- n) (fn-sn-io s :recovery-barrier :ok))))
(defconst *idr-open*
  (fn-sn-open-observed '("fn.test") 16 (- *fn-sf-max-uint* 2)
                      (list *idr-record*)))
(defconst *idr-near*
  (idr-test-recovery *fn-sf-recovery-barrier-count* (fn-sn-open-state *idr-open*)))
(defconst *idr-frontier* (fn-sf-frontier (fn-sn-files *idr-near*)))
(defconst *idr-debt* (fn-cvec-record-debt (fn-sf-records (fn-sn-files *idr-near*))))

; Productive ordinary reservation at an actually reopened, nonempty ledger.
; Complete literal antecedent/conclusion of the called reservation keystone.
(assert-event
 (and (fn-sn-open-okp *idr-open*) (fn-sn-statep *idr-near*)
      (equal *idr-debt* 1)
      (consp (fn-retain-pins (fn-node-retention (fn-sn-node *idr-near*))))
      (natp (fn-idr-reservation *idr-near* *idr-debt* nil))
      (<= (nfix *idr-debt*)
          (- *fn-sf-max-uint* (nfix (fn-idr-reservation *idr-near* *idr-debt* nil))))))

; Per-literal arithmetic keystone teeth, with nonzero promised debt.
(assert-event
 (and (natp (fn-idr-next *idr-frontier* *idr-debt* :ordinary))
      (<= (nfix *idr-debt*)
          (- *fn-sf-max-uint* (nfix (fn-idr-next *idr-frontier* *idr-debt* :ordinary))))))
(assert-event
 (and (natp (fn-idr-next (- *idr-frontier* 1) *idr-debt* :undertake))
      (<= (+ 1 (nfix *idr-debt*))
          (- *fn-sf-max-uint*
             (fn-idr-next (- *idr-frontier* 1) *idr-debt* :undertake)))))
(assert-event
 (and (natp (fn-idr-next *idr-frontier* *idr-debt* :release))
      (posp *idr-debt*)
      (<= (- *idr-debt* 1)
          (- *fn-sf-max-uint* (nfix (fn-idr-next *idr-frontier* *idr-debt* :release))))))
(assert-event
 (and (natp (fn-idr-next *idr-frontier* *idr-debt* :ordinary))
      (natp *idr-frontier*)
      (equal (fn-idr-next *idr-frontier* *idr-debt* :ordinary) (+ 1 *idr-frontier*))
      (<= (fn-idr-next *idr-frontier* *idr-debt* :ordinary) *fn-sf-max-uint*)))

; Hypothesis removal: no retained hypotheses. Explicitly unaffordable demands
; refute each headroom conclusion when the successful-grant premise is gone.
(defconst *idr-too-much* (+ *fn-sf-max-uint* 2))
(assert-event
 (and (not (natp (fn-idr-next *idr-frontier* *idr-too-much* :ordinary)))
      (not (<= (nfix *idr-too-much*)
                (- *fn-sf-max-uint* (nfix (fn-idr-next *idr-frontier* *idr-too-much* :ordinary)))))))
(assert-event
 (and (not (natp (fn-idr-next *idr-frontier* *idr-too-much* :undertake)))
      (not (<= (+ 1 (nfix *idr-too-much*))
                (- *fn-sf-max-uint* (nfix (fn-idr-next *idr-frontier* *idr-too-much* :undertake)))))))
(assert-event
 (and (not (natp (fn-idr-next *idr-frontier* *idr-too-much* :release)))
      (not (and (posp *idr-too-much*)
                (<= (- *idr-too-much* 1)
                    (- *fn-sf-max-uint* (nfix (fn-idr-next *idr-frontier* *idr-too-much* :release))))))))
(assert-event
 (and (not (natp (fn-idr-next *fn-sf-max-uint* 1 :ordinary)))
      (not (and (natp *fn-sf-max-uint*)
                (equal (fn-idr-next *fn-sf-max-uint* 1 :ordinary) (+ 1 *fn-sf-max-uint*))
                (<= (fn-idr-next *fn-sf-max-uint* 1 :ordinary) *fn-sf-max-uint*)))))
(assert-event
 (and (not (natp (fn-idr-reservation *idr-near* *idr-too-much* nil)))
      (not (<= (nfix *idr-too-much*)
                (- *fn-sf-max-uint* (nfix (fn-idr-reservation *idr-near* *idr-too-much* nil)))))))

; Actual reserve/refuse burns one ordinary ID; another ordinary request now
; refuses before reservation while the admitted release still fits exactly.
(defconst *idr-one-burn*
 (fn-sn-refuse-reservation (fn-olr-sn-reserve *idr-near*) *idr-frontier*))
(assert-event
 (and (fn-sn-statep *idr-one-burn*)
      (equal (fn-idr-reservation *idr-one-burn* 1 nil) :identity-reserve)
      (equal (fn-idr-purpose *idr-one-burn* *idr-release*) :release)
      (equal (fn-idr-reservation *idr-one-burn* 1 *idr-release*) *fn-sf-max-uint*)
      (equal (fn-idr-reservation *idr-one-burn* 1 *idr-undertake*) :operation-refused)
      (equal (fn-idr-reservation *idr-one-burn* 1 :release) :operation-refused)
      (equal (fn-idr-reservation *idr-one-burn* 1
                  '(:release "other-work" "subject-1" "receipt-1" 0)) :operation-refused)))

; Grant bound to exact operation and reservation; mutation is labelled.
(defconst *idr-grant* (fn-idr-grant *idr-one-burn* *idr-release*))
(defconst *idr-release-record* (fn-idr-retention-candidate *idr-one-burn* *idr-release*))
(defconst *idr-reserved* (fn-olr-sn-reserve *idr-one-burn*))
(assert-event
 (and (fn-idr-grant-boundp *idr-reserved* *idr-release-record* *idr-grant*)
      (mv-let (allowed remaining)
        (fn-idr-consume-grant *idr-reserved* *idr-release-record* *idr-grant*)
        (and allowed (null remaining)
             (mv-let (again unused)
               (fn-idr-consume-grant *idr-reserved* *idr-release-record* remaining)
               (declare (ignore unused))
               (not again))))
      (not (fn-idr-grant-boundp *idr-one-burn* *idr-release-record* *idr-grant*))
      (not (fn-idr-grant-boundp *idr-reserved* *idr-release-record* nil))
      ; Mutation: a different event cannot steal the grant's one identity.
      (not (fn-idr-grant-boundp *idr-reserved* *idr-record* *idr-grant*))
      (equal (fn-sf-phase (fn-sn-files
                (fn-sn-prepare-retention *idr-reserved* *idr-release-record*))) :record-staged)))

; If the maintenance reservation itself fails after issue, it burns the last
; ID without discharging debt.  Explicit finite refusal, no retry promise.
(defconst *idr-release-failed*
  (fn-sn-refuse-reservation *idr-reserved* (- *fn-sf-max-uint* 1)))
(assert-event
 (and (equal (fn-idr-reservation *idr-release-failed* 1 *idr-release*) :identity-exhausted)
      (equal (fn-node-retention (fn-sn-node *idr-release-failed*))
             (fn-node-retention (fn-sn-node *idr-one-burn*)))) )
