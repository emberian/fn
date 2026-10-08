; Statement-bound teeth for the actual control-owner step.
(in-package "ACL2")
(include-book "../../books/control-receipt-wire")
(include-book "../../books/defkeystone")

(defteeth fn-nco-receipt-completes-exactly-once
  :claim (((requested (equal (fn-nco-at 3 st) :requested))
           (same (equal token (fn-nco-at 2 st)))
           (terminal (fn-nco-terminalp outcome)))
          (let* ((r (fn-nco-owner-step st (list :complete token outcome reason)))
                 (next (cadr r)))
            (and (equal (car r) :completed)
                 (equal (fn-nco-at 3 next) :completed)
                 (equal (fn-nco-at 4 next) outcome)
                 (equal (fn-nco-at 5 next) reason)
                 (equal (fn-nco-owner-step next (list :complete token other why))
                        (list :refused next)))))
  :subject fn-nco-owner-step
  :witness ((st (cadr (fn-nco-owner-step (fn-nco-initial "epoch")
                           (list :request (caar *fn-nco-store-verbs*)))))
            (token '("epoch" 1)) (outcome :accepted) (reason :installed)
            (other :refused) (why :failed))
  :breaks ((requested ((st '("epoch" 1 ("epoch" 1) :completed :accepted :installed nil))))
           (same ((token '("epoch" 2))))
           (terminal ((outcome :requested))))
  :mutations
  ((second-completion-admitted
    (:conclusion
     (equal (car (fn-nco-owner-step
                  (cadr (fn-nco-owner-step st (list :complete token outcome reason)))
                  (list :complete token other why))) :completed))
    ((st (cadr (fn-nco-owner-step (fn-nco-initial "epoch")
                           (list :request (caar *fn-nco-store-verbs*)))))
     (token '("epoch" 1)) (outcome :accepted) (reason :installed)
     (other :refused) (why :failed))
    :fault "a second completion replaces the first terminal status")))

(defteeth fn-nco-owner-step-has-no-orphan
  :claim (((paired (fn-nco-no-orphanp st)))
          (fn-nco-no-orphanp (cadr (fn-nco-owner-step st event))))
  :subject fn-nco-owner-step
  :witness ((st (fn-nco-initial "epoch"))
            (event (list :request (caar *fn-nco-store-verbs*))))
  :breaks ((paired ((st '("epoch" 1 ("epoch" 1) :requested nil nil nil))
                    (event '(:status)))))
  :mutations
  ((drop-accepted-job
    (:conclusion
     (fn-nco-no-orphanp (update-nth 6 nil (cadr (fn-nco-owner-step st event)))))
    ((st (fn-nco-initial "epoch"))
     (event (list :request (caar *fn-nco-store-verbs*))))
    :fault "acknowledgement loses the pending producer job")))

(defteeth fn-nco-only-job-outcome-leaves-requested
  :claim (((paired (fn-nco-no-orphanp st))
           (requested (equal (fn-nco-at 3 st) :requested))
           (leaving (not (equal (fn-nco-at 3 (cadr (fn-nco-owner-step st event)))
                                :requested))))
          (and (equal (fn-nco-at 0 event) :complete)
               (equal (fn-nco-at 1 event) (fn-nco-at 0 (fn-nco-pending-job st)))
               (fn-nco-terminalp (fn-nco-at 2 event))
               (equal (car (fn-nco-owner-step st event)) :completed)
               (not (fn-nco-at 6 (cadr (fn-nco-owner-step st event))))))
  :subject fn-nco-owner-step
  :witness ((st (cadr (fn-nco-owner-step (fn-nco-initial "epoch")
                                      (list :request (caar *fn-nco-store-verbs*)))))
            (event '(:complete ("epoch" 1) :accepted :installed)))
  :breaks ((paired ((st '("epoch" 1 ("epoch" 1) :requested nil nil nil))))
           (requested ((st (fn-nco-initial "epoch")) (event '(:status))))
           (leaving ((event '(:release ("epoch" 1))))))
  :mutations
  ((keep-job-after-outcome
    (:conclusion (consp (fn-nco-at 6 (cadr (fn-nco-owner-step st event)))))
    ((st (cadr (fn-nco-owner-step (fn-nco-initial "epoch")
                                (list :request (caar *fn-nco-store-verbs*)))))
     (event '(:complete ("epoch" 1) :accepted :installed)))
    :fault "a completed receipt still has runnable work")))

(defteeth fn-nco-unknown-receipt-status
  :claim (((unknown
            (not (and (fn-nco-at 2 st)
                      (equal text (fn-record-string-octets
                                   (fn-nco-token-text (fn-nco-at 2 st))))))))
          (let ((r (fn-nco-wire-step st (fn-nco-status-argv text nil))))
            (and (equal r (list st (list :reason :uncertain :receipt-unknown)))
                 (not (equal (fn-nco-at 2 (fn-nco-at 1 r)) :requested))
                 (not (fn-nco-terminalp (fn-nco-at 2 (fn-nco-at 1 r)))))))
  :subject fn-nco-wire-step
  :witness ((st (fn-nco-initial "restarted"))
            (text (fn-record-string-octets "epoch-1")))
  :breaks ((unknown ((st (cadr (fn-nco-owner-step (fn-nco-initial "epoch")
                                 (list :request (caar *fn-nco-store-verbs*))))))))
  :mutations
  ((unknown-promises-work
    (:conclusion
     (equal (fn-nco-at 2 (fn-nco-at 1 (fn-nco-wire-step
                                      st (fn-nco-status-argv text nil)))) :requested))
    ((st (fn-nco-initial "restarted")) (text (fn-record-string-octets "epoch-1")))
    :fault "a restarted owner promises a job it does not hold")))

(defteeth fn-nco-unknown-receipt-stops-with-exit-3
  :claim (((unknown (equal word (fn-nctrl-reason-word :receipt-unknown))))
          (and (equal (fn-nco-client-status status word) :uncertain)
               (not (fn-nco-client-waitp (fn-nco-client-status status word) word))
               (equal (fn-outcome-code
                       (fn-outcome-of-status (fn-nco-client-status status word))) 3)))
  :subject fn-nco-client-status
  :witness ((status :accepted) (word (fn-nctrl-reason-word :receipt-unknown)))
  :breaks ((unknown ((word (fn-nctrl-reason-word :requested)))))
  :mutations
  ((poll-unknown-forever
    (:conclusion (fn-nco-client-waitp (fn-nco-client-status status word) word))
    ((status :accepted) (word (fn-nctrl-reason-word :receipt-unknown)))
    :fault "an unknown receipt keeps polling after process death")))
