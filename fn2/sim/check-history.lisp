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
(defun fn2-history-get (key alist)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (assoc-equal key alist)))

(defun fn2-history-row (n s)
  (declare (xargs :guard t :verify-guards nil))
  (fn2-history-get n (fn2-lm-at 0 s)))

(defun fn2-history-save (n row s)
  (declare (xargs :guard t :verify-guards nil))
  (update-nth 0 (put-assoc-equal n row (fn2-lm-at 0 s)) s))

(defun fn2-history-emit (event s)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn2-lm-event-allowedp event (fn2-lm-at 6 s))
      (mv :ok (update-nth 7 (cons event (fn2-lm-at 7 s))
                        (update-nth 6 (fn2-lm-step event (fn2-lm-at 6 s)) s)))
    (mv :log-model-refused s)))

(defun fn2-history-disjointp (a b)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp a)
      (and (not (member-equal (car a) b))
           (fn2-history-disjointp (cdr a) b))
    (null a)))

(defun fn2-history-batch (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((batch (fn2-lm-at 1 event)) (logs (fn2-lm-at 2 event))
         (n (fn2-lm-at 0 batch)) (records (fn2-lm-at 2 batch))
         (deps (fn2-lm-at 3 batch))
         (ids (append (if (true-listp deps) deps nil)
                      (if (true-listp logs) logs nil))))
    (if (and (equal (len event) 3) (fn2-lm-batchp batch)
             (consp records) (no-duplicatesp-equal records)
             (true-listp logs) (consp logs) (no-duplicatesp-equal ids)
             (fn2-history-disjointp ids (fn2-lm-at 5 s))
             (fn2-history-disjointp records (fn2-lm-at 4 s))
             (fn2-history-disjointp records (fn2-lm-at 3 s)))
        (fn2-history-emit
         (list :submit-batch batch)
         (fn2-history-save
          n (list batch logs nil nil nil nil nil nil nil)
          (update-nth 4 (append records (fn2-lm-at 4 s))
                      (update-nth 5 (append ids (fn2-lm-at 5 s)) s))))
      (mv :bad-manifest s))))

(defun fn2-history-uncertainp (rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (or (fn2-lm-at 4 (cdar rows)) (fn2-history-uncertainp (cdr rows)))
    nil))

(defun fn2-history-write (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((op (fn2-lm-at 1 event)) (n (fn2-lm-at 2 event))
         (role (fn2-lm-at 3 event)) (identity (fn2-lm-at 4 event))
         (length (fn2-lm-at 5 event)) (row (fn2-history-row n s))
         (deps (fn2-lm-at 3 (fn2-lm-at 0 row))))
    (if (and (equal (len event) 6) op row (posp length)
             (not (assoc-equal op (fn2-lm-at 1 s)))
             (not (fn2-history-uncertainp (fn2-lm-at 0 s)))
             (not (fn2-lm-at 5 row))
             (not (member-equal identity (fn2-lm-at 2 row)))
             (case role
               (:dependency (member-equal identity deps))
               (:log (and (member-equal identity (fn2-lm-at 1 row))
                          (subsetp-equal deps (fn2-lm-at 3 row))))
               (otherwise nil)))
        (mv :ok
            (fn2-history-save
             n (update-nth 2 (cons identity (fn2-lm-at 2 row)) row)
             (update-nth 1
                         (put-assoc-equal op (list n role identity length nil)
                                          (fn2-lm-at 1 s)) s)))
      (mv :bad-write s))))

(defun fn2-history-write-result (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((op (fn2-lm-at 1 event)) (outcome (fn2-lm-at 2 event))
         (count (fn2-lm-at 3 event))
         (operation (fn2-history-get op (fn2-lm-at 1 s)))
         (n (fn2-lm-at 0 operation)) (row (fn2-history-row n s))
         (identity (fn2-lm-at 2 operation))
         (length (fn2-lm-at 3 operation)))
    (if (not (and (equal (len event) 4) operation
                  (member-eq (fn2-lm-at 1 operation) '(:dependency :log))
                  (not (fn2-lm-at 4 operation))
                  (member-eq outcome '(:done :short :failed :cancelled :eio :enospc))
                  (natp count) (<= count (nfix length))))
        (mv :stray-write-result s)
      (let* ((success (and (eq outcome :done) (equal count length)))
             (row (if success
                      (update-nth 3 (cons identity (fn2-lm-at 3 row)) row)
                    (update-nth 4 t row)))
             (s (fn2-history-save
                 n row (update-nth 1
                                   (put-assoc-equal op (update-nth 4 t operation)
                                                    (fn2-lm-at 1 s)) s)))
             (deps (fn2-lm-at 3 (fn2-lm-at 0 row))))
        (if (and success
                 (subsetp-equal (append deps (fn2-lm-at 1 row))
                                (fn2-lm-at 3 row)))
            (fn2-history-emit (list :batch-writes-complete n deps) s)
          (mv :ok s))))))

(defun fn2-history-fence (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((op (fn2-lm-at 1 event)) (n (fn2-lm-at 2 event))
         (row (fn2-history-row n s)))
    (if (and (equal (len event) 3) op row
             (not (assoc-equal op (fn2-lm-at 1 s)))
             (not (fn2-lm-at 2 s))
             (not (fn2-history-uncertainp (fn2-lm-at 0 s)))
             (not (fn2-lm-at 5 row))
             (member-equal n (fn2-lm-at 1 (fn2-lm-at 6 s))))
        (mv :ok
            (fn2-history-save
             n (update-nth 5 t row)
             (update-nth 2 op
                         (update-nth 1
                                     (put-assoc-equal op (list n :fence nil 0 nil)
                                                      (fn2-lm-at 1 s)) s))))
      (mv :bad-fence s))))

(defun fn2-history-fence-result (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((op (fn2-lm-at 1 event)) (outcome (fn2-lm-at 2 event))
         (operation (fn2-history-get op (fn2-lm-at 1 s)))
         (n (fn2-lm-at 0 operation)) (row (fn2-history-row n s)))
    (if (not (and (equal (len event) 3) operation
                  (eq (fn2-lm-at 1 operation) :fence)
                  (not (fn2-lm-at 4 operation))
                  (equal op (fn2-lm-at 2 s))
                  (member-eq outcome '(:done :failed :cancelled :eio :enospc))))
        (mv :stray-fence-result s)
      (let* ((success (eq outcome :done))
             ; A late physical success does not clear the uncertainty bit.
             (row (if success (update-nth 6 t row) (update-nth 4 t row)))
             (s (fn2-history-save
                 n row (update-nth 2 nil
                                   (update-nth 1
                                               (put-assoc-equal op
                                                                (update-nth 4 t operation)
                                                                (fn2-lm-at 1 s)) s)))))
        (if success (fn2-history-emit (list :fence-ok n) s)
          (mv :ok s))))))

(defun fn2-history-visible (tag n s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((row (fn2-history-row n s))
         (prev (fn2-lm-at 1 (fn2-lm-at 0 row)))
         (prior (fn2-history-row prev s))
         (field (if (eq tag :publish) 7 8)))
    (if (and row (fn2-lm-at 6 row) (not (fn2-lm-at 4 row))
             (not (fn2-lm-at field row))
             (or (equal prev 0)
                 (and (fn2-lm-at 7 prior) (not (fn2-lm-at 4 prior))))
             (or (eq tag :publish) (fn2-lm-at 7 row)))
        (let ((s (fn2-history-save n (update-nth field t row) s)))
          (if (eq tag :ack) (fn2-history-emit (list :acknowledge n) s)
            (mv :ok s)))
      (mv :unsafe-visibility s))))

(defun fn2-history-step (event s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tag (fn2-lm-at 0 event)) (arg (fn2-lm-at 1 event))
        (crashed (fn2-lm-at 4 (fn2-lm-at 6 s))))
    (cond
     ((not (true-listp event)) (mv :malformed s))
     ((eq tag :crash)
      (if (equal (len event) 1) (fn2-history-emit event s) (mv :malformed s)))
     ((eq tag :evidence)
      (if (and crashed (equal (len event) 2)
               (member-eq (fn2-lm-at 0 arg)
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
        (if (and (equal (len event) 2) row (not (fn2-lm-at 6 row)))
            (mv :ok (fn2-history-save arg (update-nth 4 t row) s))
          (mv :bad-timeout s))))
     ((eq tag :refuse)
      (if (and (equal (len event) 2)
               (not (member-equal arg (fn2-lm-at 4 s)))
               (not (member-equal arg (fn2-lm-at 3 s))))
          (mv :ok (update-nth 3 (cons arg (fn2-lm-at 3 s)) s))
        (mv :refused-member s)))
     (t (mv :unknown-event s)))))

(defun fn2-history-translate-loop (events s)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (mv-let (code next) (fn2-history-step (car events) s)
        (if (eq code :ok) (fn2-history-translate-loop (cdr events) next)
          (mv code nil)))
    (if (null events) (mv :ok (reverse (fn2-lm-at 7 s)))
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
