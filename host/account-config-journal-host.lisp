; One registered typed C journal operation. The native executor reports I/O
; observations against its opaque issued token; it cannot supply a completion.
(in-package "ACL2")
(include-book "account-config-source-host")
(include-book "account-config-preparation-host")
(include-book "../books/journal-publish")
(include-book "../books/native-admin-shape")

(include-book "../books/history-config-journal-state")

(defun fn-owner-history-config-journal-begin
 (slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (let* ((lease (fn-owner-account-config-source state))
        (holder (fn-owner-account-adoption-operation state)))
  (cond
   ((fn-owner-history-config-journal state)
    (mv :configuration-journal-busy nil fn-allocation-turn-slots fn-page-read-pool state))
   ((not (and (eq (fn-owner-history-config-writer-gate state) :config-writer-current)
               (fn-owner-account-turn-current-bodyp :operation-select
                 (fn-prl-nth 2 holder) slot nonce fn-allocation-turn-slots
                 fn-page-read-pool state)))
    (mv :configuration-source-changed nil fn-allocation-turn-slots fn-page-read-pool state))
   (t
    (mv-let (source-word family)
      (fn-owner-runtime-operation-source :account-adoption-publish-c fn-page-read-pool state)
     (declare (ignore family))
     (if (not (eq source-word :runtime-operation-available))
         (mv :configuration-operation-unavailable nil fn-allocation-turn-slots fn-page-read-pool state)
      (mv-let (word record full plan canonical obligation next-source)
        (fn-owner-account-config-preparation-result state)
       (if (not (and (eq word :config-prepared)
                      (fn-cacm-recordp record) (eq (fn-cp-nth 0 full) :ok)
                      (fn-apr-widthp 6 plan) (eq (fn-prl-nth 1 plan) :C)
                      canonical next-source))
           (mv :configuration-semantic-pending nil fn-allocation-turn-slots fn-page-read-pool state)
        (let* ((token (fn-prl-nth 2 lease))
               (state (f-put-global 'fn-owner-history-config-journal
                        (list :history-config-journal-intent token lease) state))
               (encoded (fn-cacm-encode record))
               (name (fn-native-admin-config-name (fn-cfg-record-generation record)))
               ; Target absence is an actual pending I/O observation. No
               ; authority-true JPub state is manufactured before that probe.
               (job (list :history-config-journal token lease record
                          (fn-cp-nth 1 encoded) name nil :probe nil
                          (list full plan canonical obligation next-source)))
               (state (f-put-global 'fn-owner-history-config-journal job state)))
         (if (not (and (eq (fn-cp-nth 0 encoded) :ok) (stringp name)))
             (mv :recovery-required nil fn-allocation-turn-slots fn-page-read-pool state)
           (mv :configuration-journal-probe (list :config-target-probe token name)
               fn-allocation-turn-slots fn-page-read-pool state))))))))))

)
; The registered operation advances once per actual native observation.
; A final-state argument alone can never create a durable receipt.
(defun fn-owner-history-config-journal-step
 (token prior event slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (let* ((job (fn-owner-history-config-journal state))
        (holder (fn-owner-account-adoption-operation state))
        (registered (fn-prl-nth 6 job)))
  (if (not (and (fn-apr-widthp 10 job)
                 (eq (fn-prl-nth 0 job) :history-config-journal)
                 (eq (fn-prl-nth 7 job) :publishing)
                 (fn-cado-receipt-coordinatep token)
                 (fn-cado-receipt-coordinatep (fn-prl-nth 1 job))
                 (equal token (fn-prl-nth 1 job))
                 (fn-jpub-statep prior) (fn-jpub-statep registered)
                 (equal prior registered) (not (fn-jpub-terminalp registered))
                 (eq (fn-owner-history-config-writer-gate state) :config-writer-current)
                 (fn-owner-account-turn-current-bodyp :operation-select
                   (fn-prl-nth 2 holder) slot nonce fn-allocation-turn-slots
                   fn-page-read-pool state)))
      (mv :recovery-required nil fn-allocation-turn-slots fn-page-read-pool state)
   (let* ((state (f-put-global 'fn-owner-history-config-journal
                    (update-nth 7 :advancing job) state))
          (next (fn-jpub-step registered event))
          (state (f-put-global 'fn-owner-history-config-journal
                    (update-nth 7 :publishing (update-nth 6 next job)) state)))
    (mv :configuration-journal-stepped next fn-allocation-turn-slots
        fn-page-read-pool state)))))

(defun fn-owner-history-config-journal-observe
 (token event slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (let* ((job (fn-owner-history-config-journal state))
        (holder (fn-owner-account-adoption-operation state))
        (lease (fn-prl-nth 2 job)) (phase (fn-prl-nth 7 job))
        (publication (fn-cp-nth 1 event)))
  (cond
   ((not (and (fn-apr-widthp 10 job)
               (eq (fn-prl-nth 0 job) :history-config-journal)
               (fn-cado-receipt-coordinatep token)
               (fn-cado-receipt-coordinatep (fn-prl-nth 1 job))
               (equal token (fn-prl-nth 1 job))
               (eq (fn-owner-history-config-writer-gate state) :config-writer-current)
               (fn-owner-account-turn-current-bodyp :operation-select
                 (fn-prl-nth 2 holder) slot nonce fn-allocation-turn-slots
                 fn-page-read-pool state)))
    (mv :recovery-required nil fn-allocation-turn-slots fn-page-read-pool state))
   ((and (eq phase :probe) (eq (fn-cp-nth 0 event) :target-result)
          (eq publication :absent))
    (let* ((initial (fn-jpub-initial t))
           (next (update-nth 7 :publishing (update-nth 6 initial job)))
           (state (f-put-global 'fn-owner-history-config-journal next state)))
     (mv :configuration-journal-publish
         (list :config-journal-publish token initial (fn-prl-nth 5 job) (fn-prl-nth 4 job))
         fn-allocation-turn-slots fn-page-read-pool state)))
   ((and (eq phase :publishing) (eq (fn-cp-nth 0 event) :journal-result)
          (fn-jpub-statep publication) (fn-jpub-statep (fn-prl-nth 6 job))
          (equal publication (fn-prl-nth 6 job)) (fn-jpub-terminalp publication)
          (eq (fn-jpub-authorityp publication) t)
          (eq (fn-jpub-outcome publication) :durable))
    (let* ((receipt (list :history-config-completion (fn-prl-nth 1 lease)
                          (fn-prl-nth 7 lease) publication))
           (next (update-nth 8 receipt
                   (update-nth 7 :durable (update-nth 6 publication job))))
           (state (f-put-global 'fn-owner-history-config-journal next state)))
     (mv :configuration-journal-durable (fn-prl-nth 1 lease)
         fn-allocation-turn-slots fn-page-read-pool state)))
   ((or (and (eq phase :probe) (eq (fn-cp-nth 0 event) :target-result)
             (eq publication :present))
        (and (eq phase :publishing) (eq (fn-cp-nth 0 event) :journal-result)
             (fn-jpub-statep publication) (fn-jpub-statep (fn-prl-nth 6 job))
          (equal publication (fn-prl-nth 6 job)) (fn-jpub-terminalp publication)
             (eq (fn-jpub-outcome publication) :refused)))
    (let ((state (f-put-global 'fn-owner-history-config-journal
                    (update-nth 7 :refused job) state)))
     (mv :configuration-journal-refused nil fn-allocation-turn-slots fn-page-read-pool state)))
   (t
    ; Unknown/ambiguous result retains the original operation and aliases.
    (let ((state (f-put-global 'fn-owner-history-completion-fault
                    :configuration-journal-uncertain state)))
     (mv :recovery-required nil fn-allocation-turn-slots fn-page-read-pool state))))))
