; The consumer interface must not turn an evidence projection into an
; inductive invariant.  A constructed, well-formed unfenced notify state
; refutes that attempted lift.  J1-J4 must exclude it from permitted runs.
(in-package "ACL2")
(include-book "../books/commit-durable-all")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-cet-unfenced-notify-core (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (ids (fn2-env-commit-ids *fn2-profile-tiny*))
       (id (car ids)) (partner (cadr ids))
       (fn2-core (fn2-commit-put-core id (phase *fn2-commit-state-notify*)
                         (batch-no 1) (member-count 1) (cb-acks 0) (partner partner)))
       (fn2-core (fn2-exec-wake id fn2-core))
       (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                 (fn2-env-inv ids nil nil fn2-core)
                 ;; J1 excludes it: a :notify row's batch is above the installed root (0)
                 (not (fn2-env-dur-inv ids nil nil fn2-core))
                 (not (fn2-env-j-rows ids nil fn2-core))
                 (fn2-env-j-frontier nil fn2-core)))
       ((mv & & visits & fn2-core) (fn2-turn fn2-core))
       (acked (fn2-env-observe ids nil fn2-core)))
    (mv (list pre (< 0 visits) (member-equal 1 acked)
              (not (fn2-env-inv ids acked nil fn2-core))) fn2-core)))
(defun fn2-cet-unfenced-notify ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-cet-unfenced-notify-core fn2-core) result)))
(assert-event (equal (fn2-cet-unfenced-notify) '(t t (1) t)))

; The intended instance is executable proof syntax in the consumer.  It
; must remain refused until its predicate includes the phase/history facts;
; this is paired with the actual fn2-turn counterexample, not a search claim.
(set-prover-step-limit 10000)
(must-fail (fn2-env-turn-instance))

; EARLY NOTIFY BEFORE THE REQUIRED FENCE (barrier mode 0). Batch 1's three
; units are written and answered done in full, but no fence was taken; the
; root installs and publishes 1 and the row is at :notify. FN2-ENV-INV holds
; (nothing acknowledged yet); the strengthened invariant is false at J4 (batch
; 1 is not durable: its writes are unfenced) while J1 and J2's unfenced facts
; hold. With the fence and its answer appended, J4 holds again.
(defun fn2-cet-zero-values (layout)
  (declare (xargs :verify-guards nil))
  (if (atom layout) nil
    (cons (case (fn2-layout-kind-code (cadar layout))
            (7 (make-list 33 :initial-element 0)) ((10 15 16) nil) (otherwise 0))
          (fn2-cet-zero-values (cdr layout)))))
(defun fn2-cet-seal-octets (batch)
  (declare (xargs :verify-guards nil))
  (let* ((seal (fn2-layout-octets *fn2-format-sealed-batch*
                                  (update-nth *fn2-format-sealed-batch-field-commit* batch
                                              (fn2-cet-zero-values *fn2-format-sealed-batch*))))
         (header (fn2-layout-octets
                  *fn2-format-frame-header*
                  (update-nth *fn2-format-frame-header-field-payload-length* (len seal)
                              (update-nth *fn2-format-frame-header-field-frame-kind* *frame-kind-seal*
                                          (fn2-cet-zero-values *fn2-format-frame-header*))))))
    (append header seal)))
(assert-event (equal (fn2-env-seal-commit (fn2-cet-seal-octets 1)) 1))
(defun fn2-cet-unit-log (offset slot octets)
  (declare (xargs :verify-guards nil))
  (list (list :take slot 1 *fn2-action-write* offset 0 octets)
        (list :result slot 1 *fn2-event-write-result* *fn2-outcome-done* (len octets))))
(defun fn2-cet-early-log (base)
  (declare (xargs :verify-guards nil))
  (append (fn2-cet-unit-log base 1 (make-list 8 :initial-element 0))
          (fn2-cet-unit-log (+ base *fn2-commit-unit-bytes*) 2 (make-list 8 :initial-element 0))
          (fn2-cet-unit-log (+ base (* 2 *fn2-commit-unit-bytes*)) 3 (fn2-cet-seal-octets 1))))
(defconst *fn2-cet-fence*
  (list (list :take 4 1 *fn2-action-fence* 0 0 nil)
        (list :result 4 1 *fn2-event-fence-result* *fn2-outcome-done* 0)))
(defun fn2-cet-early-notify-core (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
       (ids (fn2-env-commit-ids *fn2-profile-tiny*))
       (id (car ids)) (partner (cadr ids))
       (fn2-core (fn2-commit-put-core id (phase *fn2-commit-state-notify*)
                         (batch-no 1) (member-count 1) (cb-acks 0) (partner partner)
                         (cb-deps-ok 1) (cb-log-ok 1) (cb-fence-ok 0) (cb-mode 0)))
       (fn2-core (stobj-let ((fn2-commit-root (fn2-core-commit-root fn2-core))) (fn2-commit-root)
                   (let* ((fn2-commit-root (fn2-commit-root-set-installed 0 1 fn2-commit-root))
                          (fn2-commit-root (fn2-commit-root-set-published 0 1 fn2-commit-root)))
                     fn2-commit-root)
                   fn2-core))
       (base (fn2-env-role-offset id 0 fn2-core))
       (log (fn2-cet-early-log base))
       (fenced (append log *fn2-cet-fence*)))
    (mv (list (fn2-env-inv ids nil log fn2-core)
              (fn2-env-j-rows ids log fn2-core)
              (fn2-env-j-frontier log fn2-core)
              (fn2-env-dur-inv ids nil log fn2-core)
              (fn2-env-batch-durable-p 1 fenced)
              (fn2-env-dur-inv ids nil fenced fn2-core))
        fn2-core)))
(defun fn2-cet-early-notify ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core) (fn2-cet-early-notify-core fn2-core) result)))
(assert-event (equal (fn2-cet-early-notify) '(t t nil nil t t)))
;; Hypothesis removal for FN2-ENV-DUR-TURN-PRESERVES: without J1-J4 (only the
;; evidence projection) one fn2-turn acknowledges batch 1 with an empty log;
;; the strengthened invariant is false of that state before the turn, and
;; the early notify's state fails J4 until its fence is logged.
(defun fn2-dur-turn-j-removal ()
  (declare (xargs :verify-guards nil))
  (and (equal (fn2-cet-unfenced-notify) '(t t (1) t))
       (equal (fn2-cet-early-notify) '(t t nil nil t t))))
(assert-event (fn2-dur-turn-j-removal))
