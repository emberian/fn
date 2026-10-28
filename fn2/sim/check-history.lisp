; Independent baseline-barrier checker. Lists here are test evidence, never a
; served representation. The producer must project actual issue/harvest/reply
; events and physical recovery observations; this book does not authenticate
; that producer or replace the pending B5 image reader.
(in-package "ACL2")
(include-book "../books/log-model")

; State: batch alist, operation alist, active fence token, refused records,
; all member records, all write identities, B1 state, reverse B1 trace.
; Batch row: batch, log identities, issued identities, done identities,
; uncertain, fence issued, durable, published, acknowledged.
; Operation row: batch number, role, identity, length, terminal.
(fn2-cm-defreaders fn2-history-state-batches
                   fn2-history-state-operations
                   fn2-history-state-fence
                   fn2-history-state-refused
                   fn2-history-state-members
                   fn2-history-state-identities
                   fn2-history-state-log-state
                   fn2-history-state-trace)
(fn2-cm-defreaders fn2-history-row-batch
                   fn2-history-row-logs
                   fn2-history-row-issued
                   fn2-history-row-done
                   fn2-history-row-uncertain
                   fn2-history-row-fence-issued
                   fn2-history-row-durable
                   fn2-history-row-published
                   fn2-history-row-acknowledged)
(fn2-cm-defreaders fn2-history-operation-batch-number
                   fn2-history-operation-role
                   fn2-history-operation-identity
                   fn2-history-operation-length
                   fn2-history-operation-terminal)

(fn2-cm-defreaders fn2-history-batch-event-tag
                   fn2-history-batch-event-batch
                   fn2-history-batch-event-logs)
(fn2-cm-defreaders fn2-history-write-event-tag
                   fn2-history-write-event-operation
                   fn2-history-write-event-batch
                   fn2-history-write-event-role
                   fn2-history-write-event-identity
                   fn2-history-write-event-length)
(fn2-cm-defreaders fn2-history-write-result-event-tag
                   fn2-history-write-result-event-operation
                   fn2-history-write-result-event-outcome
                   fn2-history-write-result-event-count)
(fn2-cm-defreaders fn2-history-fence-event-tag
                   fn2-history-fence-event-operation
                   fn2-history-fence-event-batch)
(fn2-cm-defreaders fn2-history-fence-result-event-tag
                   fn2-history-fence-result-event-operation
                   fn2-history-fence-result-event-outcome)

(defun fn2-history-get (key alist)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (assoc-equal key alist)))

(defun fn2-history-row (n s)
  (declare (xargs :guard t :verify-guards nil))
  (fn2-history-get n (fn2-history-state-batches s)))

(defun fn2-history-save (n row s)
  (declare (xargs :guard t :verify-guards nil))
  (update-fn2-history-state-batches (put-assoc-equal n row (fn2-history-state-batches s)) s))

(defun fn2-history-emit (event s)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn2-lm-event-allowedp event (fn2-history-state-log-state s))
      (mv :ok (update-fn2-history-state-trace (cons event (fn2-history-state-trace s))
                        (update-fn2-history-state-log-state (fn2-lm-step event (fn2-history-state-log-state s)) s)))
    (mv :log-model-refused s)))

(defun fn2-history-disjointp (a b)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp a)
      (and (not (member-equal (car a) b))
           (fn2-history-disjointp (cdr a) b))
    (null a)))

(defun fn2-history-batch (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((batch (fn2-history-batch-event-batch event)) (logs (fn2-history-batch-event-logs event))
         (n (fn2-lm-batch-number batch)) (records (fn2-lm-batch-records batch))
         (deps (fn2-lm-batch-dependencies batch))
         (ids (append (if (true-listp deps) deps nil)
                      (if (true-listp logs) logs nil))))
    (if (and (equal (len event) 3) (fn2-lm-batchp batch)
             (consp records) (no-duplicatesp-equal records)
             (true-listp logs) (consp logs) (no-duplicatesp-equal ids)
             (fn2-history-disjointp ids (fn2-history-state-identities s))
             (fn2-history-disjointp records (fn2-history-state-members s))
             (fn2-history-disjointp records (fn2-history-state-refused s)))
        (fn2-history-emit
         (list :submit-batch batch)
         (fn2-history-save
          n (list batch logs nil nil nil nil nil nil nil)
          (update-fn2-history-state-members (append records (fn2-history-state-members s))
                      (update-fn2-history-state-identities (append ids (fn2-history-state-identities s)) s))))
      (mv :bad-manifest s))))

(defun fn2-history-uncertainp (rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (or (fn2-history-row-uncertain (cdar rows)) (fn2-history-uncertainp (cdr rows)))
    nil))

(defun fn2-history-write (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((op (fn2-history-write-event-operation event)) (n (fn2-history-write-event-batch event))
         (role (fn2-history-write-event-role event)) (identity (fn2-history-write-event-identity event))
         (length (fn2-history-write-event-length event)) (row (fn2-history-row n s))
         (deps (fn2-lm-batch-dependencies (fn2-history-row-batch row))))
    (if (and (equal (len event) 6) op row (posp length)
             (not (assoc-equal op (fn2-history-state-operations s)))
             (not (fn2-history-uncertainp (fn2-history-state-batches s)))
             (not (fn2-history-row-fence-issued row))
             (not (member-equal identity (fn2-history-row-issued row)))
             (case role
               (:dependency (member-equal identity deps))
               (:log (and (member-equal identity (fn2-history-row-logs row))
                          (subsetp-equal deps (fn2-history-row-done row))))
               (otherwise nil)))
        (mv :ok
            (fn2-history-save
             n (update-fn2-history-row-issued (cons identity (fn2-history-row-issued row)) row)
             (update-fn2-history-state-operations
                         (put-assoc-equal op (list n role identity length nil)
                                          (fn2-history-state-operations s)) s)))
      (mv :bad-write s))))

(defun fn2-history-write-result (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((op (fn2-history-write-result-event-operation event)) (outcome (fn2-history-write-result-event-outcome event))
         (count (fn2-history-write-result-event-count event))
         (operation (fn2-history-get op (fn2-history-state-operations s)))
         (n (fn2-history-operation-batch-number operation)) (row (fn2-history-row n s))
         (identity (fn2-history-operation-identity operation))
         (length (fn2-history-operation-length operation)))
    (if (not (and (equal (len event) 4) operation
                  (member-eq (fn2-history-operation-role operation) '(:dependency :log))
                  (not (fn2-history-operation-terminal operation))
                  (member-eq outcome '(:done :short :failed :cancelled :eio :enospc))
                  (natp count) (<= count (nfix length))))
        (mv :stray-write-result s)
      (let* ((success (and (eq outcome :done) (equal count length)))
             (row (if success
                      (update-fn2-history-row-done (cons identity (fn2-history-row-done row)) row)
                    (update-fn2-history-row-uncertain t row)))
             (s (fn2-history-save
                 n row (update-fn2-history-state-operations
                                   (put-assoc-equal op (update-fn2-history-operation-terminal t operation)
                                                    (fn2-history-state-operations s)) s)))
             (deps (fn2-lm-batch-dependencies (fn2-history-row-batch row))))
        (if (and success
                 (subsetp-equal (append deps (fn2-history-row-logs row))
                                (fn2-history-row-done row)))
            (fn2-history-emit (list :batch-writes-complete n deps) s)
          (mv :ok s))))))

(defun fn2-history-fence (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((op (fn2-history-fence-event-operation event)) (n (fn2-history-fence-event-batch event))
         (row (fn2-history-row n s)))
    (if (and (equal (len event) 3) op row
             (not (assoc-equal op (fn2-history-state-operations s)))
             (not (fn2-history-state-fence s))
             (not (fn2-history-uncertainp (fn2-history-state-batches s)))
             (not (fn2-history-row-fence-issued row))
             (member-equal n (fn2-lm-state-completed (fn2-history-state-log-state s))))
        (mv :ok
            (fn2-history-save
             n (update-fn2-history-row-fence-issued t row)
             (update-fn2-history-state-fence op
                         (update-fn2-history-state-operations
                                     (put-assoc-equal op (list n :fence nil 0 nil)
                                                      (fn2-history-state-operations s)) s))))
      (mv :bad-fence s))))

(defun fn2-history-fence-result (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((op (fn2-history-fence-result-event-operation event)) (outcome (fn2-history-fence-result-event-outcome event))
         (operation (fn2-history-get op (fn2-history-state-operations s)))
         (n (fn2-history-operation-batch-number operation)) (row (fn2-history-row n s)))
    (if (not (and (equal (len event) 3) operation
                  (eq (fn2-history-operation-role operation) :fence)
                  (not (fn2-history-operation-terminal operation))
                  (equal op (fn2-history-state-fence s))
                  (member-eq outcome '(:done :failed :cancelled :eio :enospc))))
        (mv :stray-fence-result s)
      (let* ((success (eq outcome :done))
             ; A late physical success does not clear the uncertainty bit.
             (row (if success (update-fn2-history-row-durable t row) (update-fn2-history-row-uncertain t row)))
             (s (fn2-history-save
                 n row (update-fn2-history-state-fence nil
                                   (update-fn2-history-state-operations
                                               (put-assoc-equal op
                                                                (update-fn2-history-operation-terminal t operation)
                                                                (fn2-history-state-operations s)) s)))))
        (if success (fn2-history-emit (list :fence-ok n) s)
          (mv :ok s))))))

(defun fn2-history-visible (tag n s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((row (fn2-history-row n s))
         (prev (fn2-lm-batch-predecessor (fn2-history-row-batch row)))
         (prior (fn2-history-row prev s))
         (publishp (eq tag :publish)))
    (if (and row (fn2-history-row-durable row) (not (fn2-history-row-uncertain row))
             (not (if publishp (fn2-history-row-published row)
               (fn2-history-row-acknowledged row)))
             (or (equal prev 0)
                 (and (fn2-history-row-published prior) (not (fn2-history-row-uncertain prior))))
             (or (eq tag :publish) (fn2-history-row-published row)))
        (let ((s (fn2-history-save n (if publishp (update-fn2-history-row-published t row)
                                               (update-fn2-history-row-acknowledged t row)) s)))
          (if (eq tag :ack) (fn2-history-emit (list :acknowledge n) s)
            (mv :ok s)))
      (mv :unsafe-visibility s))))

(defun fn2-history-step (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tag (fn2-lm-event-tag event)) (arg (fn2-lm-event-argument event))
        (crashed (fn2-lm-state-crashed (fn2-history-state-log-state s))))
    (cond
     ((not (true-listp event)) (mv :malformed s))
     ((eq tag :crash)
      (if (equal (len event) 1) (fn2-history-emit event s) (mv :malformed s)))
     ((eq tag :evidence)
      (if (and crashed (equal (len event) 2)
               (member-eq (fn2-lm-event-tag arg)
                          '(:corrupt-required :bad-tail :rollback :present-frontier :survives)))
          (fn2-history-emit arg s)
        (mv :bad-evidence s)))
     (crashed (mv :after-crash s))
     ((eq tag :batch) (fn2-history-batch event s))
     ((eq tag :write) (fn2-history-write event s))
     ((eq tag :write-result) (fn2-history-write-result event s))
     ((eq tag :fence) (fn2-history-fence event s))
     ((eq tag :fence-result) (fn2-history-fence-result event s))
     ((member-eq tag '(:publish :ack))
      (if (equal (len event) 2) (fn2-history-visible tag arg s) (mv :malformed s)))
     ((eq tag :timeout)
      (let ((row (fn2-history-row arg s)))
        (if (and (equal (len event) 2) row (not (fn2-history-row-durable row)))
            (mv :ok (fn2-history-save arg (update-fn2-history-row-uncertain t row) s))
          (mv :bad-timeout s))))
     ((eq tag :refuse)
      (if (and (equal (len event) 2)
               (not (member-equal arg (fn2-history-state-members s)))
               (not (member-equal arg (fn2-history-state-refused s))))
          (mv :ok (update-fn2-history-state-refused (cons arg (fn2-history-state-refused s)) s))
        (mv :refused-member s)))
     (t (mv :unknown-event s)))))

(defun fn2-history-translate-loop (events s)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (mv-let (code next) (fn2-history-step (car events) s)
        (if (eq code :ok) (fn2-history-translate-loop (cdr events) next)
          (mv code nil)))
    (if (null events) (mv :ok (reverse (fn2-history-state-trace s)))
      (mv :malformed nil))))

(defun fn2-history-translate (events)
  (declare (xargs :guard t :verify-guards nil))
  (fn2-history-translate-loop
   events (list nil nil nil nil nil nil (fn2-lm-initial) nil)))

(defun fn2-check-history (events profile classification recovered-history)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (code trace) (fn2-history-translate events)
    (and (eq code :ok)
         (fn2-lm-recovery-allowedp trace profile classification recovered-history))))
