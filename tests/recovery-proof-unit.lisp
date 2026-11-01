; Evaluated teeth of B5's keystones: the actual commit fixture, simulated
; death, post-death faults on the durable image, and B5's recovery row.
(in-package "ACL2")
(include-book "../books/recovery-proof")

(defconst *fn2-rp-full* (make-list 600 :initial-element '(:auto 26)))
(defun fn2-rp-hyps-intact (p r)
 (declare (xargs :verify-guards nil))
 (let ((s (fn2-recovery-proof-state r)))
  (and (fn2-commit-proof-admitted r) (fn2-cm-profilep p) (fn2-cm-persistence-fence p)
       (fn2-lm-state-valid s) (fn2-lm-no-destructionp s))))
(defun fn2-rp-intact (r)
 (declare (xargs :verify-guards nil))
 (fn2-lm-acknowledged-in-historyp
  (fn2-lm-state-acknowledged (fn2-recovery-proof-state r)) (fn2-commit-proof-recovered r)))

; Positive: both batches acknowledged and recovered, :intact.
(defun fn2-recovery-proof-intact-positive (mode)
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :crash-only t t nil 0 0))
        (r (fn2-recovery-proof-run *fn2-rp-full* p mode 2 1 nil)))
  (and (fn2-rp-hyps-intact p r) (fn2-rp-intact r)
       (equal (fn2-commit-proof-acks r) '(2 2))
       (equal (len (fn2-commit-proof-recovered r)) 2)
       (eq (fn2-commit-proof-classification r) :intact))))
(defun fn2-recovery-proof-intact-baseline () (declare (xargs :verify-guards nil)) (fn2-recovery-proof-intact-positive 0))
(defun fn2-recovery-proof-intact-fua () (declare (xargs :verify-guards nil)) (fn2-recovery-proof-intact-positive 1))
; Removing A-PERSISTENCE-FENCE: a lying flush acknowledges batches the
; device never kept; recovery cannot and does not recover them.
(defun fn2-recovery-proof-fence-removal ()
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :lying nil t nil 0 0))
        (r (fn2-recovery-proof-run (make-list 600 :initial-element '(:auto 10)) p 0 2 1 nil)))
  (and (fn2-commit-proof-admitted r) (not (fn2-cm-persistence-fence p))
       (equal (fn2-commit-proof-acks r) '(2 2)) (not (fn2-rp-intact r)))))
; Removing no-later-destruction: an acknowledged batch corrupted at rest.
(defun fn2-recovery-proof-destruction-removal ()
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :broad t t nil 0 1))
        (r (fn2-recovery-proof-run *fn2-rp-full* p 0 2 1 '((:corrupt 1 2 100))))
        (s (fn2-recovery-proof-state r)))
  (and (fn2-commit-proof-admitted r) (fn2-cm-persistence-fence p) (fn2-lm-state-valid s)
       (not (fn2-lm-no-destructionp s)) (not (fn2-rp-intact r))
       (if (member-eq (fn2-commit-proof-classification r) '(:unknown :damaged)) t nil))))

; A dirty tail: death after the leader's three writes and before its fence
; (76 steps of this schedule), with one byte of dirt in its unfenced seal frame.
(defconst *fn2-rp-tail* (make-list 76 :initial-element '(:auto 26)))
(defun fn2-rp-tail-run (kind)
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile kind t t nil 0 0))
        (r (fn2-recovery-proof-run *fn2-rp-tail* p 0 2 1 '((:corrupt 1 2 100)))))
  (list p r (fn2-recovery-proof-state r))))
(defun fn2-recovery-proof-broad-tail ()
 (declare (xargs :verify-guards nil))
 (let* ((x (fn2-rp-tail-run :broad)) (r (cadr x)) (s (caddr x)))
  (and (fn2-commit-proof-admitted r) (fn2-lm-state-valid s) (fn2-lm-state-bad-tail s)
       (eq (fn2-commit-proof-classification r) :unknown))))
; Removing "not crash-only": the same evidence is a harmless torn tail.
(defun fn2-recovery-proof-crash-only-tail ()
 (declare (xargs :verify-guards nil))
 (let* ((x (fn2-rp-tail-run :crash-only)) (r (cadr x)) (s (caddr x)))
  (and (fn2-commit-proof-admitted r) (fn2-lm-state-valid s) (fn2-lm-state-bad-tail s)
       (eq (fn2-commit-proof-classification r) :torn-tail))))

; Rollback to batch 1 after both were acknowledged.
(defun fn2-rp-rollback (frontier faults)
 (declare (xargs :verify-guards nil))
 (let* ((p (fn2-cm-profile :broad t t frontier 0 0))
        (r (fn2-recovery-proof-run *fn2-rp-full* p 0 2 1 faults)))
  (list p r (fn2-recovery-proof-state r))))
(defun fn2-recovery-proof-witnessed-rollback ()
 (declare (xargs :verify-guards nil))
 (let* ((x (fn2-rp-rollback t '((:witness 2) (:rollback 1)))) (r (cadr x)))
  (and (fn2-commit-proof-admitted r) (eq (fn2-commit-proof-outcome r) :rollback-detected)
       (eq (fn2-commit-proof-classification r) :damaged)
       (equal (len (fn2-commit-proof-recovered r)) 1))))
; Removing the witness: the older image is recovered with no detection claim.
(defun fn2-recovery-proof-unwitnessed-rollback ()
 (declare (xargs :verify-guards nil))
 (let* ((x (fn2-rp-rollback t '((:rollback 1)))) (r (cadr x)))
  (and (fn2-commit-proof-admitted r) (eq (fn2-commit-proof-outcome r) :none)
       (eq (fn2-commit-proof-classification r) :intact)
       (equal (len (fn2-commit-proof-recovered r)) 1))))
; Removing A-INDEPENDENT-FRONTIER: a presented receipt is not credited.
(defun fn2-recovery-proof-uncredited-witness ()
 (declare (xargs :verify-guards nil))
 (let* ((x (fn2-rp-rollback nil '((:witness 2) (:rollback 1)))) (r (cadr x)))
  (and (fn2-commit-proof-admitted r) (eq (fn2-commit-proof-outcome r) :uncredited)
       (not (eq (fn2-commit-proof-classification r) :damaged)))))
; A covered witness: consistent, intact.
(defun fn2-recovery-proof-consistent-witness ()
 (declare (xargs :verify-guards nil))
 (let* ((x (fn2-rp-rollback t '((:witness 1) (:rollback 1)))) (r (cadr x)))
  (and (fn2-commit-proof-admitted r) (eq (fn2-commit-proof-outcome r) :consistent)
       (eq (fn2-commit-proof-classification r) :intact))))

(defun fn2-recovery-proof-summary (r)
 (declare (xargs :verify-guards nil))
 (list (fn2-commit-proof-admitted r) (fn2-commit-proof-acks r) (len (fn2-commit-proof-recovered r))
       (fn2-commit-proof-classification r) (fn2-commit-proof-outcome r)))

(fn2-assert-owed-teeth fn2-recovery-never-shortens-intact fn2-recovery-broad-bad-tail-unknown
                       fn2-recovery-rollback-needs-witness)
