; fn: a replay that stops refuses the open BY NAME (lane snapshot-open-3,
; 2026-09-27).  Prefix `fn-sorr-'.
;
; The configured replay (books/config-physical-replay.lisp fn-cpr-loop)
; stops at the first history item it cannot apply and answers
; (:fault LAST-GOOD-NODE POSITION REASON).  The host printed every such stop
; as "ACL2 replay rejected committed transaction history or configuration
; history" -- the 1M synthesized store's first full replay ran 812 s and
; ended with exactly that line, and it took a hand-made hook to learn that
; the history held more article charge than the configured capacity
; (planning/evidence/snapshot-open-2-2026-09-27.md section 5; this lane's
; record, section M4).
;
; This book names the stop.  From the fault's own fields -- the last good
; node, the position and the reason -- and the history the fold ran over, it
; finds the item at the position (the event whose sequence plus the
; configuration records taken before it is the position: fn-cpr-loop takes
; a configuration record first when its txid is at most the event's)
; (fn-sorr-stop), and:
;   fn-sorr-refusal answers (:refused :capacity TXID MSGID CHARGE RESERVED
;     CAPACITY) when that item is an article (a held row, or a composite's)
;     whose charge does not fit the retention state of the last good node:
;     RESERVED + CHARGE > CAPACITY, exactly fn-retain-admissiblep's capacity
;     conjunct (books/retention.lisp).  That is a history this configuration
;     cannot hold, not damage: the open REFUSES, by name.  Otherwise nil
;     (and always nil when the replay did not stop).
;   fn-sorr-stop-text names any other stop (position, reason, txid) for the
;     host's fault line: a history the replay cannot apply stays a fault
;     (exit 4), now saying where.
;
; Host: host/store-node-host.lisp fn-store-sn-open-classified records the
; refusal (answering :refused) or the stop's text (answering :fault);
; fn-store-open-refusal-text and fn-store-open-stop-text render them;
; host/native/io.lisp prints the refusal as the open's ("open refused
; reason=capacity: ...") and appends the stop to the replay fault's line.
; The refusal replaces no accepted open (fn-sorr-refusal-only-on-a-stop), and
; the capacity it names is the retention state's
; (fn-sorr-capacity-names-the-retention-state).

(in-package "ACL2")
(include-book "store-open-pre-c1")
(local (include-book "arithmetic/top" :dir :system))

; The configuration records the fold takes before an event of txid TXID
; (fn-cpr-config-firstp: a record whose txid is at most the event's).
(defun fn-sorr-configs-before (configs txid)
  (declare (xargs :guard t))
  (if (consp configs)
      (+ (if (<= (nfix (fn-cfg-record-txid (car configs))) (nfix txid)) 1 0)
         (fn-sorr-configs-before (cdr configs) txid))
    0))

; The event of EVENTS (from index I) at which a fold stopping at POSITION
; stopped: its sequence I plus the configuration records before it.
(defun fn-sorr-event-at (events i configs position)
  (declare (xargs :guard (natp i)))
  (if (consp events)
      (let ((event (car events)))
        (if (equal (+ i (fn-sorr-configs-before configs (fn-store-event-txid event)))
                   position)
            event
          (fn-sorr-event-at (cdr events) (+ 1 i) configs position)))
    nil))

; The article an event applies, as fn-replay-apply-record reads it.
(defun fn-sorr-article (event)
  (declare (xargs :guard t))
  (let ((article (if (fn-hstxa-p event) (fn-replay-composite-held event) event)))
    (and (fn-held-p article) article)))

; The stop, described: (:stopped POSITION REASON EVENT ARTICLE RETENTION), or
; nil when the replay did not stop.
(defun fn-sorr-stop (replayed records configs)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (equal (fn-replay-result-kind replayed) :fault))
      nil
    (let* ((position (fn-replay-result-sequence replayed))
           (reason (fn-replay-result-reason replayed))
           (event (and (natp position)
                       (fn-sorr-event-at (true-list-fix records) 0 configs position))))
      (list :stopped position reason event
            (and (equal reason :event-refusal) (fn-sorr-article event))
            (fn-node-retention (fn-cnode-node (fn-replay-result-node replayed)))))))

; The open's refusal: the capacity stop, or nil.  A stop at an article whose
; charge does not fit the last good node's retention state is a history this
; configuration cannot hold -- a refusal the operator answers with a larger
; capacity, not damage.
(defun fn-sorr-refusal (replayed records configs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((stop (fn-sorr-stop replayed records configs)))
    (and stop
         (let* ((event (nth 3 stop)) (article (nth 4 stop)) (retention (nth 5 stop))
                (capacity (fn-retain-capacity retention))
                (reserved (fn-retain-reserved retention))
                (charge (and article (fn-record-charge article))))
           (and article (natp charge) (natp capacity) (natp reserved)
                (< capacity (+ reserved charge))
                (list :refused :capacity (fn-store-event-txid event) (fn-record-msgid article)
                      charge reserved capacity))))))

; The refusal is only ever the answer to a replay that stopped.
(defthm fn-sorr-refusal-only-on-a-stop
  (implies (fn-sorr-refusal replayed records configs)
           (equal (fn-replay-result-kind replayed) :fault)))

; A refusal names the last good node's retention state, and the charge it
; names does not fit it (fn-retain-admissiblep's capacity conjunct), at an
; article the fold refused.
(defthm fn-sorr-capacity-names-the-retention-state
  (let ((r (fn-sorr-refusal replayed records configs))
        (retention (fn-node-retention (fn-cnode-node (fn-replay-result-node replayed)))))
    (implies r
             (and (equal (cadr r) :capacity)
                  (equal (nth 6 r) (fn-retain-capacity retention))
                  (equal (nth 5 r) (fn-retain-reserved retention))
                  (natp (nth 4 r))
                  (< (nth 6 r) (+ (nth 5 r) (nth 4 r)))
                  (equal (fn-replay-result-reason replayed) :event-refusal)))))

(verify-guards fn-sorr-stop)
(verify-guards fn-sorr-refusal)

(defun fn-sorr-text-or-dash (x)
  (declare (xargs :guard t))
  (cond ((null x) "-")
        ((natp x) (fn-sopc-decimal x))
        ((stringp x) x)
        ((symbolp x) (string-downcase (symbol-name x)))
        (t "-")))

; The operator's line for the refusal (the host prints it as the open's
; refusal).
(defun fn-sorr-refusal-text (refusal)
  (declare (xargs :guard t))
  (if (and (true-listp refusal) (equal (len refusal) 7)
           (eq (car refusal) :refused) (eq (cadr refusal) :capacity))
      (concatenate 'string
                   "open refused reason=capacity: the history's article "
                   (fn-sorr-text-or-dash (nth 3 refusal))
                   " (txid " (fn-sorr-text-or-dash (nth 2 refusal))
                   ") is charged " (fn-sorr-text-or-dash (nth 4 refusal))
                   " units and the configured capacity "
                   (fn-sorr-text-or-dash (nth 6 refusal))
                   " already holds " (fn-sorr-text-or-dash (nth 5 refusal))
                   "; this history needs a larger capacity")
    nil))

; Any other stop stays the host's fault (a history the replay cannot apply
; is damage, exit 4), and names where it stopped: appended to the fault's
; line.
(defun fn-sorr-stop-text (replayed records configs)
  (declare (xargs :guard t))
  (let ((stop (fn-sorr-stop replayed records configs)))
    (if (and (true-listp stop) (equal (len stop) 6))
        (concatenate 'string
                     "stopped at history position "
                     (fn-sorr-text-or-dash (nth 1 stop))
                     " (" (fn-sorr-text-or-dash (nth 2 stop))
                     ", txid " (fn-sorr-text-or-dash
                                (and (nth 3 stop) (fn-store-event-txid (nth 3 stop))))
                     ")")
      nil)))
