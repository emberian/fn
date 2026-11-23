; Discharges fn2-lm-durable-acknowledgement (books/log-model.lisp). Every
; trace state's acknowledgements are a true list of positive batch numbers.
; Under honest fences with no rollback, fn2-lm-recovery-allowedp's
; fn2-lm-protected-acks-p puts each acknowledged batch inside the recovered
; history unless corruption or the dirty tail lies at or below it;
; fn2-lm-no-destructionp excludes corruption and requires every
; acknowledgement to lie strictly below the dirty tail.
(in-package "ACL2")
(include-book "log-model")
(include-book "owed-discharge")

(local (defun fn2-lm-ack-ids-p (x)
  (if (consp x) (and (posp (car x)) (fn2-lm-ack-ids-p (cdr x))) (null x))))

(local (defthm fn2-lm-state-acknowledged-of-update-nth
  (implies (natp i)
           (equal (fn2-lm-state-acknowledged (update-nth i v s))
                  (if (equal i 3) v (fn2-lm-state-acknowledged s))))
  :hints (("Goal" :use ((:instance nth-update-nth (m 3) (n i) (val v) (l s)))
           :in-theory (e/d (nth) (nth-update-nth)) :expand ((:free (n x) (nth n x)))))))

(local (defthm fn2-lm-acknowledge-allowed-argument-posp
  (implies (and (fn2-lm-event-allowedp event s)
                (equal (fn2-lm-event-tag event) :acknowledge))
           (posp (fn2-lm-event-argument event)))
  :rule-classes nil))

(local (defthm fn2-lm-ack-ids-p-of-step
  (implies (fn2-lm-ack-ids-p (fn2-lm-state-acknowledged s))
           (fn2-lm-ack-ids-p (fn2-lm-state-acknowledged (fn2-lm-step event s))))
  :hints (("Goal" :use fn2-lm-acknowledge-allowed-argument-posp
           :in-theory (disable fn2-lm-event-allowedp fn2-lm-state-acknowledged
                               fn2-lm-event-tag fn2-lm-event-argument fn2-lm-event-extra
                               update-nth)))))

(local (defthm fn2-lm-ack-ids-p-of-run
  (implies (fn2-lm-ack-ids-p (fn2-lm-state-acknowledged s))
           (fn2-lm-ack-ids-p (fn2-lm-state-acknowledged (fn2-lm-run trace s))))
  :hints (("Goal" :in-theory (disable fn2-lm-step fn2-lm-state-acknowledged)))))

(local (defthm fn2-lm-ack-ids-p-of-trace-state
  (fn2-lm-ack-ids-p (fn2-lm-state-acknowledged (fn2-lm-trace-state trace)))
  :hints (("Goal" :use ((:instance fn2-lm-ack-ids-p-of-run (s (fn2-lm-initial))))
           :in-theory (disable fn2-lm-ack-ids-p-of-run fn2-lm-run)))))

(local (defthm fn2-lm-protected-acks-without-corruption
  (implies (and (fn2-lm-ack-ids-p acked) (not (consp corrupt))
                (fn2-lm-protected-acks-p acked corrupt recovered))
           (fn2-lm-acknowledged-in-historyp acked recovered))))

(local (defthm fn2-lm-protected-acks-below-bad-tail
  (implies (and (fn2-lm-ack-ids-p acked) (not (consp corrupt))
                (fn2-lm-acks-below-p acked bad-tail)
                (fn2-lm-protected-acks-p acked (cons bad-tail corrupt) recovered))
           (fn2-lm-acknowledged-in-historyp acked recovered))))

(defthm fn2-lm-durable-acknowledgement-proved
  (fn2-lm-durable-acknowledgement$owed trace profile classification recovered-history)
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-lm-durable-acknowledgement$owed
                                   fn2-lm-durable-ack-hyps fn2-lm-recovery-allowedp
                                   fn2-lm-no-destructionp)
                                  (fn2-lm-trace-state
                                   fn2-lm-state-submitted fn2-lm-state-completed
                                   fn2-lm-state-fenced fn2-lm-state-acknowledged
                                   fn2-lm-state-crashed fn2-lm-state-corrupt
                                   fn2-lm-state-bad-tail fn2-lm-state-rollback
                                   fn2-lm-state-witnesses fn2-lm-state-survivors
                                   fn2-lm-state-valid fn2-cm-profilep
                                   fn2-cm-profile-kind fn2-cm-persistence-fence
                                   fn2-cm-integrity-evidence fn2-cm-independent-frontier
                                   fn2-cm-corruption-budget)))))

(fn2-owed-discharge fn2-lm-durable-acknowledgement
                    fn2-lm-durable-acknowledgement-proved)
