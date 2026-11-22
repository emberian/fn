; One-shot client of a protected remote NNTP node. The owner activates a
; :taken row after recovery and transfers its booked account to this actor.
(in-package "ACL2")
(include-book "peer-pull-reply")
(include-book "xfnc-ops")

(defcost fn2-pull-connect :child fn2-issue-connect :descriptors 1 :answers t
 :tables (fn2-core-ops) :effects ((:acquire (:operation)))
 :doc "Connect to the operator-authorized concrete remote IP and port.")
(defcost fn2-pull-read-line :child fn2-peer-pull-line :bytes 2048
 :doc "Classify one externally framed NNTP status line in the held RX workspace.")
(defcost fn2-pull-reply-count :child fn2-peer-pull-reply-count :bytes 2048
 :doc "Classify the protected counted status and determine the exact allowed FNCT reply span.")
(defcost fn2-pull-command :child fn2-peer-pull-format-command :answers t :bytes 1024
 :tables (fn2-core-pool) :doc "Write STARTTLS or one protected authentication command into exclusive TX.")
(defcost fn2-pull-wipe :child fn2-peer-pull-wipe :answers t :bytes 1280
 :tables (fn2-core-pool) :doc "Overwrite the caller's secret-bearing bytes, then truncate its exclusive range.")
(make-event
 (value (cons 'progn
  (append (fn2-arms-op-face-events 'fn2-pull-connect 'fn2-issue-connect (w state))
          (fn2-arms-op-face-events 'fn2-pull-read-line 'fn2-peer-pull-line (w state))
          (fn2-arms-op-face-events 'fn2-pull-reply-count 'fn2-peer-pull-reply-count (w state))
          (fn2-arms-op-face-events 'fn2-pull-command 'fn2-peer-pull-format-command (w state))
          (fn2-arms-op-face-events 'fn2-pull-wipe 'fn2-peer-pull-wipe (w state))))))

(defmachine-arms fn2-peer-pull :declare
 :subarms
 ((terminate
   (:next :closing) (:charge :steps *fn2-work-transition* :runnable t))
  (wait-io
   (:if (fn2-xfnc-expired-p id) ((:goto terminate)) ((:charge :steps *fn2-work-empty*))))
  (receive
   (:let fill (fn2-conn-fill row-rx-slot))
   (:let cap (fn2-conn-cap row-rx-slot))
   (:if (<= cap fill) ((:goto terminate))
        ((:let len (min *fn2-conn-receive-bytes* (nfix (- cap fill))))
         (:issue (fn2-issue-receive row-cap-index row-cap-nonce row-rx-slot row-rx-gen len :principal row-principal-slot)
          :bind (issued sg)
          :ok ((:set (op issued) (op-gen sg)) (:wait :completion :bytes (+ 2048 len)))))))
  (next-command
   (:do (rc) (fn2-core-reset row-rx-slot row-rx-gen) :case ((:otherwise (:stop :machine-phase))))
   (:set (pos 0) (start 0) (tx-off 0))
   (:next :write-command) (:charge :bytes 2048 :steps *fn2-work-transition* :runnable t)))
 :arms
 ((:free (:idle))
  ;; The activating control op stages all credential spans on its take turn.
  ;; If it relinquishes the row before doing so there is no network authority.
  (:stage (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))
  (:connect
   (:cond ((equal row-timer 0)
           (:do (tc deadline) (fn2-xfnc-arm-timer id row-timeout-ms)
            :case (((:ok) (:set (timer 1)) (:charge :steps *fn2-work-transition* :runnable t))
                   (:otherwise (:goto terminate)))))
          ((fn2-xfnc-expired-p id) (:goto terminate))
          (t (:issue (fn2-pull-connect row-family row-port row-w0 row-w1 row-w2 row-w3 :principal row-principal-slot)
              :bind (issued sg)
              :ok ((:set (op issued) (op-gen sg)) (:next :connecting) (:wait :completion :bytes 0))))))
  (:connecting (:goto wait-io))
  (:line
   (:cond ((fn2-xfnc-expired-p id) (:goto terminate))
          ((posp row-pending) (:charge :steps *fn2-work-empty*))
          (t
           (:do (lc next code) (fn2-pull-read-line row-start row-pos row-rx-slot row-rx-gen
                                                  *fn2-peer-pull-kind* id row-generation))
           (:cond
            ((eq lc :need-more) (:set (pos next)) (:goto receive))
            ((eq lc :budget) (:set (pos next)) (:charge :bytes 2048 :steps *fn2-work-transition* :runnable t))
            ((not (eq lc :ok)) (:goto terminate))
            ((equal row-dialog *fn2-pull-dialog-starttls*)
             (:if (equal code 382)
                  ((:set (start next) (pos next)) (:next :upgrade)
                   (:charge :bytes 2048 :steps *fn2-work-transition* :runnable t))
                  ((:goto terminate))))
            ;; Other exchanges have exactly one request outstanding. No
            ;; later status may be prefabricated in an earlier response.
            ((not (equal next (fn2-conn-fill row-rx-slot))) (:goto terminate))
            ((and (equal row-dialog *fn2-pull-dialog-greeting*) (member-equal code '(200 201)))
             (:set (dialog *fn2-pull-dialog-starttls*)) (:goto next-command))
            ((and (equal row-protected 1) (equal row-dialog *fn2-pull-dialog-user*) (equal code 381))
             (:set (dialog *fn2-pull-dialog-pass*)) (:goto next-command))
            ((and (equal row-protected 1) (equal row-dialog *fn2-pull-dialog-pass*) (equal code 281))
             (:do (rc) (fn2-core-reset row-rx-slot row-rx-gen) :case ((:otherwise (:stop :machine-phase))))
             (:set (start 0) (pos 0))
             (:next :authenticated) (:charge :bytes 2048 :steps *fn2-work-transition* :runnable t))
            (t (:goto terminate))))))
  (:write-command
   (:if (fn2-xfnc-expired-p id) ((:goto terminate))
        ((:do (rc) (fn2-pull-command (cond ((equal row-dialog *fn2-pull-dialog-starttls*) :starttls)
                                           ((equal row-dialog *fn2-pull-dialog-user*) :user)
                                           ((equal row-dialog *fn2-pull-dialog-pass*) :pass) (t :none))
                                    row-protected row-secret-slot row-secret-gen row-stream-len row-user-len row-pass-len
                                    row-tx-slot row-tx-gen *fn2-peer-pull-kind* id row-generation)
          :case (((:ok) (:set (tx-off 0)) (:next :send) (:charge :bytes 1024 :steps *fn2-work-transition* :runnable t))
                 (:otherwise (:goto terminate)))))))
  (:send
   (:cond ((fn2-xfnc-expired-p id) (:goto terminate))
          ((posp row-pending) (:charge :steps *fn2-work-empty*))
          ((< row-tx-off (fn2-conn-fill row-tx-slot))
           (:let len (min *fn2-conn-send-bytes* (nfix (- (fn2-conn-fill row-tx-slot) row-tx-off))))
           (:issue (fn2-issue-send row-cap-index row-cap-nonce row-tx-slot row-tx-gen row-tx-off len 0
                                   :principal row-principal-slot)
            :bind (issued sg)
            :ok ((:set (op issued) (op-gen sg)) (:wait :completion :bytes len))))
          ((member-equal row-dialog (list *fn2-pull-dialog-register* *fn2-pull-dialog-read*))
           (:do (tc) (fn2-core-reset row-tx-slot row-tx-gen) :case ((:otherwise (:stop :machine-phase))))
           (:set (start 0) (pos 0)) (:next :reply-line) (:charge :steps *fn2-work-transition* :runnable t))
          (t
           (:do (tc) (fn2-pull-wipe row-tx-slot row-tx-gen 0 *fn2-nntp-line-cap* *fn2-peer-pull-kind* id row-generation)
            :case ((:otherwise (:stop :machine-phase))))
           (:if (equal row-dialog *fn2-pull-dialog-pass*)
                ((:do (sc) (fn2-pull-wipe row-secret-slot row-secret-gen row-stream-len
                                          (+ 250 (* 2 *fn2-nntp-line-cap*)) *fn2-peer-pull-kind* id row-generation)
                  :case ((:otherwise (:stop :machine-phase))))
                 (:set (user-len 0) (pass-len 0)) (:next :line)
                 (:charge :bytes 2048 :steps *fn2-work-transition* :runnable t))
                ((:next :line) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))))))
  (:upgrade
   (:if (fn2-xfnc-expired-p id) ((:goto terminate))
        ((:let retained (nfix (- (fn2-conn-fill row-rx-slot) row-start)))
         (:issue (fn2-issue-tls-start row-cap-index row-cap-nonce row-rx-slot row-rx-gen row-start retained
                                      :principal row-principal-slot)
          :bind (issued sg)
          :ok ((:set (op issued) (op-gen sg)) (:next :upgrading) (:wait :completion :bytes 0))))))
  (:upgrading
   (:cond ((fn2-xfnc-expired-p id) (:goto terminate))
          ((posp row-pending) (:charge :steps *fn2-work-empty*))
          ((equal row-protected 1)
           (:set (dialog *fn2-pull-dialog-user*)) (:goto next-command))
          (t (:goto terminate))))
  (:authenticated
   (:set (dialog *fn2-pull-dialog-register*)) (:next :request)
   (:charge :steps *fn2-work-transition* :runnable t))
  (:request
   (:if (fn2-xfnc-expired-p id) ((:goto terminate))
        ((:do (code) (fn2-peer-pull-request id row-generation)
          :case (((:ok) (:set (tx-off 0)) (:next :send) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                 (:otherwise (:goto terminate)))))))
  (:reply-line
   (:cond ((fn2-xfnc-expired-p id) (:goto terminate))
          ((posp row-pending) (:charge :steps *fn2-work-empty*))
          (t (:do (code after status length) (fn2-pull-reply-count row-start row-pos row-rx-slot row-rx-gen
                                                                   *fn2-peer-pull-kind* id row-generation))
             (:cond ((eq code :need-more) (:set (pos after)) (:goto receive))
                    ((eq code :budget) (:set (pos after)) (:charge :bytes 2048 :steps *fn2-work-transition* :runnable t))
                    ((and (eq code :ok) (<= (fn2-conn-fill row-rx-slot) (+ after length)))
                     (:set (start after) (pos after) (copied 0) (reply-status status) (frame-len length))
                     (:next :compact) (:charge :bytes 2048 :steps *fn2-work-transition* :runnable t))
                    (t (:goto terminate))))))
  (:compact
   (:if (fn2-xfnc-expired-p id) ((:goto terminate))
        ((:do (code copied) (fn2-core-drop-prefix row-rx-slot row-rx-gen row-start row-copied *fn2-conn-compact-bytes*)
          :case (((:more) (:set (copied copied)) (:charge :bytes *fn2-conn-compact-bytes* :steps *fn2-work-transition* :runnable t))
                 ((:ok) (:set (start 0) (pos 0) (copied 0)) (:next :frame-input)
                  (:charge :bytes *fn2-conn-compact-bytes* :steps *fn2-work-transition* :runnable t))
                 (:otherwise (:goto terminate)))))))
  (:frame-input
   (:cond ((fn2-xfnc-expired-p id) (:goto terminate))
          ((posp row-pending) (:charge :steps *fn2-work-empty*))
          ((equal row-frame-len (fn2-conn-fill row-rx-slot))
           (:next :frame-header) (:charge :steps *fn2-work-transition* :runnable t))
          ((< (fn2-conn-fill row-rx-slot) row-frame-len)
           (:let len (min *fn2-conn-receive-bytes* (nfix (- row-frame-len (fn2-conn-fill row-rx-slot)))))
           (:issue (fn2-issue-receive row-cap-index row-cap-nonce row-rx-slot row-rx-gen len :principal row-principal-slot)
            :bind (issued sg) :ok ((:set (op issued) (op-gen sg)) (:wait :completion :bytes len))))
          (t (:goto terminate))))
  (:frame-header
   (:do (code off end) (fn2-peer-pull-open-reply id row-generation)
    :case (((:ok) (:next :frame-hash) (:charge :bytes 32 :steps *fn2-work-transition* :runnable t))
           (:otherwise (:goto terminate)))))
  (:frame-hash
   (:do (code off end) (fn2-peer-pull-open-reply id row-generation)
    :case (((:ok) (:next :frame-trailer) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
           (:otherwise (:goto terminate)))))
  (:frame-trailer
   (:do (code off end) (fn2-peer-pull-open-reply id row-generation)
    :case (((:ok) (:next :frame-result) (:charge :bytes 32 :steps *fn2-work-transition* :runnable t))
           (:otherwise (:goto terminate)))))
  (:frame-result
   (:cond ((fn2-xfnc-expired-p id) (:goto terminate))
          (t (:do (code off end) (fn2-peer-pull-open-reply id row-generation)
              :case (((:ok) (:cond
                       ((equal row-dialog *fn2-pull-dialog-register*)
                        (:do (rc) (fn2-peer-pull-accept-registration id row-generation off end)
                         :case (((:ok) (:do (tc) (fn2-core-reset row-rx-slot row-rx-gen)
                                        :case ((:otherwise (:stop :machine-phase))))
                                (:set (dialog *fn2-pull-dialog-read*)) (:next :resume)
                                (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                               (:otherwise (:goto terminate)))))
                       ((equal row-dialog *fn2-pull-dialog-read*)
                        (:set (result-off off) (result-end end)) (:next :import)
                        (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                       (t (:goto terminate))))
                     (:otherwise (:goto terminate)))))))
  ;; The receiving checkpoint and C's item settlement own these turns. A
  ;; successful registration alone cannot select a receiver resume position.
  (:resume (:goto terminate))
  (:import (:goto terminate))
  (:closing
   (:cond ((and (posp row-pending) (equal row-cancel-issued 0))
           (:issue (fn2-issue-cancel row-op row-op-gen :principal row-principal-slot)
            :ok ((:set (cancel-issued 1)) (:wait :completion :bytes 0))))
          ((posp row-pending) (:charge :steps *fn2-work-empty*))
          ((equal row-connected 1)
           (:issue (fn2-issue-close row-cap-index row-cap-nonce :principal row-principal-slot)
            :ok ((:next :close-wait) (:wait :completion :bytes 0))))
          (t (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))))
  (:close-wait (:charge :steps *fn2-work-empty*))
  (:draining
   (:cond ((posp row-pending) (:charge :steps *fn2-work-empty*))
          ((equal row-timer 1)
           (:do (rc) (fn2-xfnc-clear-timer id) :case ((:otherwise (:stop :machine-phase))))
           (:set (timer 0)) (:charge :steps *fn2-work-transition* :runnable t))
          (t
         (:do (wc) (fn2-pull-wipe row-secret-slot row-secret-gen 0 (+ 250 (* 2 *fn2-nntp-line-cap*))
                                  *fn2-peer-pull-kind* id row-generation) :case ((:otherwise (:stop :machine-phase))))
         (:do (tc) (fn2-pull-wipe row-tx-slot row-tx-gen 0 *fn2-nntp-line-cap*
                                  *fn2-peer-pull-kind* id row-generation) :case ((:otherwise (:stop :machine-phase))))
         (:do (sc) (fn2-core-release row-secret-slot row-secret-gen) :effects ((:release (:tx-range))) :accept (:ok :retired)
          :why "generation exhaustion retires the released private range")
         (:do (xc) (fn2-core-release row-tx-slot row-tx-gen) :effects ((:release (:tx-range))) :accept (:ok :retired)
          :why "generation exhaustion retires the released TX range")
         (:do (rc) (fn2-core-release row-rx-slot row-rx-gen) :effects ((:release (:rx-range))) :accept (:ok :retired)
          :why "generation exhaustion retires the released RX range")
         (:do (ac) (fn2-account-unbook-ref row-account-ref) :case ((:otherwise (:stop :account))))
         (:let head (fn2-machine-free-head *fn2-peer-pull-admission-ordinal*))
         (:let retire (>= row-generation (fn2-machine-gen-limit)))
         (:set (generation (if retire row-generation (+ 1 row-generation))) (next-free head)
               (rx-slot *fn2-none*) (tx-slot *fn2-none*) (secret-slot *fn2-none*) (account-ref *fn2-none*)
               (ctl *fn2-none*) (op *fn2-none*) (timer 0) (user-len 0) (pass-len 0) (wait-reason *fn2-wait-none*))
         (:next (:if retire :retired :free))
         (:do () (fn2-machine-reclaim-fn2-peer-pull id retire))
         (:charge :bytes 2048 :steps *fn2-work-release*))))
  (:retired (:idle)))
 :observes
 ((:connect-result :from (:connecting :closing)
   (:cond ((equal outcome *fn2-outcome-done*)
           (:set (connected 1) (cap-index aux0) (cap-nonce aux1))
           (:if (equal row-phase *fn2-peer-pull-state-connecting*) ((:next :line) (:wake)) ((:wake))))
          (t (:next :closing) (:wake))))
  (:send-result :from (:send :closing)
   (:if (and (member-equal outcome (list *fn2-outcome-done* *fn2-outcome-short*))
             (natp count) (< 0 count) (equal aux0 0) (unsigned-byte-p 32 (+ row-tx-off count)))
        ((:do (qc) (fn2-account-charge-core row-principal-slot *fn2-account-charge-tx* count)
          :case ((:otherwise (:stop :account))))
         (:set (tx-off (+ row-tx-off count))) (:wake))
        ((:next :closing) (:wake))))
  (:receive-result :from (:line :reply-line :frame-input :closing)
   (:if (and (member-equal outcome (list *fn2-outcome-done* *fn2-outcome-short*)) (natp count) (< 0 count))
        ((:do (qc) (fn2-account-charge-core row-principal-slot *fn2-account-charge-rx* count)
          :case ((:otherwise (:stop :account))))
         (:wake))
        ((:next :closing) (:wake))))
  (:tls-result :from (:upgrading :closing)
   (:if (equal outcome *fn2-outcome-done*)
        ((:set (protected 1)) (:wake))
        ((:next :closing) (:wake))))
  (:cancel-result :from (:closing) (:wake))
  (:close-result :from (:close-wait)
   (:set (connected 0) (cap-index 0) (cap-nonce 0)) (:next :draining) (:wake))))
(defmachine-arms fn2-peer-pull)
(defmachine-run fn2-peer-pull)
