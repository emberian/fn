; Teeth of books/bp-run-class.lisp and books/bp-node-run-class.lisp (PRF-131
; part 1): the class of a BP verb's run and its exit code.  A reachable
; witness per keystone, and per hypothesis a witness that checks the retained
; hypotheses, the failure of the omitted one and the failure of the
; conclusion, then a must-fail of the weakened theorem (the counterexample is
; the assert-event before it; the must-fail's search is cut short on purpose).
(in-package "ACL2")
(include-book "../../books/bp-node-run-class")
(include-book "bp-node-job-offer-tests")
(include-book "std/testing/must-fail" :dir :system)

;; ---------------------------------------------------------------------------
;; fn-bprc-exit-code-separates-the-classes.  Witness: the five codes.
(assert-event
 (equal (list (fn-bprc-exit-code :accepted) (fn-bprc-exit-code :refused)
              (fn-bprc-exit-code :interrupted) (fn-bprc-exit-code :fenced)
              (fn-bprc-exit-code :not-connected))
        '(0 1 6 3 7)))
;; Without (member c1 classes): a word that is no class answers the fenced
;; code, so it collides with :fenced.
(assert-event
 (and (not (member-equal :bogus *fn-bprc-classes*))
      (member-equal :fenced *fn-bprc-classes*)
      (not (equal :bogus :fenced))
      (equal (fn-bprc-exit-code :bogus) (fn-bprc-exit-code :fenced))))
(must-fail
 (defthm bprct-codes-without-c1-class
   (implies (and (member-equal c2 *fn-bprc-classes*) (not (equal c1 c2)))
            (not (equal (fn-bprc-exit-code c1) (fn-bprc-exit-code c2))))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))
(assert-event
 (and (member-equal :fenced *fn-bprc-classes*)
      (not (member-equal :bogus *fn-bprc-classes*))
      (equal (fn-bprc-exit-code :fenced) (fn-bprc-exit-code :bogus))))
(must-fail
 (defthm bprct-codes-without-c2-class
   (implies (and (member-equal c1 *fn-bprc-classes*) (not (equal c1 c2)))
            (not (equal (fn-bprc-exit-code c1) (fn-bprc-exit-code c2))))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))
;; Without (not (equal c1 c2)): one class, one code.
(assert-event
 (and (member-equal :interrupted *fn-bprc-classes*)
      (equal (fn-bprc-exit-code :interrupted) (fn-bprc-exit-code :interrupted))))
(must-fail
 (defthm bprct-codes-without-distinct
   (implies (and (member-equal c1 *fn-bprc-classes*)
                 (member-equal c2 *fn-bprc-classes*))
            (not (equal (fn-bprc-exit-code c1) (fn-bprc-exit-code c2))))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------------
;; fn-bprc-fence-is-never-masked (no hypotheses).  Witness: a refusal and a
;; lost connection before the fence, a refusal and a failed connect after.
(defconst *bprct-mixed*
  (fn-bprc-note-all (fn-bprc-note (fn-bprc-note-all (fn-bprc-empty)
                                                    '(:refused :uncertain))
                                  :fenced)
                    '(:refused :failed :accepted)))
(assert-event (and (equal *bprct-mixed* '(2 1 1 1))
                   (equal (fn-bprc-class *bprct-mixed*) :fenced)
                   (equal (fn-bprc-run-exit-code *bprct-mixed*) 3)))
;; The same run without the fence is a lost connection (exit 6): the fence
;; is what makes it :fenced.
(assert-event
 (equal (fn-bprc-class (fn-bprc-note-all (fn-bprc-empty)
                                         '(:refused :uncertain :refused :failed)))
        :interrupted))

;; ---------------------------------------------------------------------------
;; fn-bprc-connection-local-never-fences.  Witness: every connection-local
;; word, and each class it can reach.
(assert-event
 (and (fn-bprc-connection-local-wordsp '(:failed))
      (equal (fn-bprc-class (fn-bprc-note-all (fn-bprc-empty) '(:failed)))
             :not-connected)
      (equal (fn-bprc-class (fn-bprc-note-all (fn-bprc-empty) '(:failed :uncertain)))
             :interrupted)
      (equal (fn-bprc-class (fn-bprc-note-all (fn-bprc-empty) '(:failed :refused)))
             :refused)
      (equal (fn-bprc-class (fn-bprc-note-all (fn-bprc-empty) '(:accepted nil)))
             :accepted)))
;; Without the hypothesis: a word outside the connection-local set (here an
;; unknown session word, which fails closed) fences.
(assert-event
 (and (not (fn-bprc-connection-local-wordsp '(:failed :lost)))
      (equal (fn-bprc-class (fn-bprc-note-all (fn-bprc-empty) '(:failed :lost)))
             :fenced)))
(must-fail
 (defthm bprct-local-without-hypothesis
   (not (equal (fn-bprc-class (fn-bprc-note-all (fn-bprc-empty) words))
               :fenced))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))

;; The session evidence the host records for a TCPCL connection.
(assert-event
 (and (equal (fn-bprc-session-evidence :uncertain nil) :uncertain)
      (equal (fn-bprc-session-evidence :uncertain t) :fenced)
      (equal (fn-bprc-session-evidence :refused nil) :refused)
      (equal (fn-bprc-session-evidence nil nil) nil)
      (equal (fn-bprc-session-evidence :accepted nil) nil)))

;; ---------------------------------------------------------------------------
;; fn-bpnrc-job-result-class-is-the-transport-class over the reachable
;; attempting state of the PRF-120 teeth (*jo-st-a*, KEY2's attempt 2), each
;; outcome through the served job-result step.
(defun bprct-run-class (st key attempt outcome)
  (fn-bprc-class
   (fn-bprc-note-effects
    (fn-bprc-empty)
    (fn-bpn-pending-success-effects
     (fn-bpn-machine-state-pending
      (fn-bpnf-base (fn-bpnf-answer-state
                     (fn-bpnj-step st (list :job-result key attempt outcome)))))))))
(defun bprct-hyps (st key attempt)
  (let ((base (fn-bpnf-base st)))
    (and (fn-bpn-machine-statep base)
         (not (fn-bpnf-issued st))
         (not (fn-bpah-delivery-uncertainp st))
         (not (fn-bpn-machine-state-fenced base))
         (not (fn-bpn-machine-state-pending base))
         (natp attempt)
         (equal (fn-bpnj-attempt-token st key) attempt)
         (< (fn-bpn-machine-state-next-token base) *fn-bpn-machine-max-records*))))
(assert-event
 (and (bprct-hyps *jo-st-a* *jo-key2* 2)
      (equal (bprct-run-class *jo-st-a* *jo-key2* 2 :accepted) :accepted)
      (equal (bprct-run-class *jo-st-a* *jo-key2* 2 :refused) :refused)
      (equal (bprct-run-class *jo-st-a* *jo-key2* 2 :uncertain) :interrupted)
      (equal (bprct-run-class *jo-st-a* *jo-key2* 2 :failed) :not-connected)
      (equal (fn-bprc-run-exit-code
              (fn-bprc-note-effects
               (fn-bprc-empty)
               (fn-bpn-pending-success-effects
                (fn-bpn-machine-state-pending
                 (fn-bpnf-base (fn-bpnf-answer-state
                                (fn-bpnj-step *jo-st-a*
                                              (list :job-result *jo-key2* 2 :failed))))))))
             7)))
;; Without the attempt hypothesis (attempt 1 names an earlier record): the
;; result is stale, nothing is proposed, and a failed connect renders
;; :accepted, not :not-connected.
(assert-event
 (and (let ((base (fn-bpnf-base *jo-st-a*)))
        (and (fn-bpn-machine-statep base) (not (fn-bpnf-issued *jo-st-a*))
             (not (fn-bpah-delivery-uncertainp *jo-st-a*))
             (not (fn-bpn-machine-state-fenced base))
             (not (fn-bpn-machine-state-pending base))
             (natp 1)
             (< (fn-bpn-machine-state-next-token base) *fn-bpn-machine-max-records*)))
      (not (equal (fn-bpnj-attempt-token *jo-st-a* *jo-key2*) 1))
      (not (equal (bprct-run-class *jo-st-a* *jo-key2* 1 :failed)
                  (fn-bprc-transfer-class :failed)))))
(must-fail
 (defthm bprct-job-result-without-attempt
   (let* ((base (fn-bpnf-base st))
          (token (fn-bpn-machine-state-next-token base)))
     (implies (and (fn-bpn-machine-statep base)
                   (not (fn-bpnf-issued st))
                   (not (fn-bpah-delivery-uncertainp st))
                   (not (fn-bpn-machine-state-fenced base))
                   (not (fn-bpn-machine-state-pending base))
                   (natp attempt)
                   (< token *fn-bpn-machine-max-records*))
              (equal (bprct-run-class st key attempt outcome)
                     (fn-bprc-transfer-class outcome))))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))
;; Without "no pending proposal": the state *jo-st-p* whose attempting record
;; is unanswered proposes nothing for the result.
(assert-event
 (and (fn-bpn-machine-state-pending (fn-bpnf-base *jo-st-p*))
      (natp 2)
      (not (equal (bprct-run-class *jo-st-p* *jo-key2* 2 :failed)
                  :not-connected))))
