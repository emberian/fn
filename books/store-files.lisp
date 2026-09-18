; Executable kernel for the immutable-file storage experiment.
;
; This book models allocator replacement, one-file transaction publication,
; crash choices, the completion gate, and recovery barriers.  It does not model
; POSIX calls or prove that a platform implements these events.  Candidate
; records are checked by the existing record predicate and replay engine; no
; second acceptance implementation is introduced here.

(in-package "ACL2")
(include-book "replay-invariants")

(defconst *fn-sf-max-uint* 4294967295)
(defconst *fn-sf-recovery-barrier-count* 5)

; State layout:
; (:store-files phase frontier frontier-candidate records record-candidate
;               completion-pair successes recovery-barriers)
(defun fn-sf-phase (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr s)) :exec (fn-ag-car (fn-ag-cdr s))))
(defun fn-sf-frontier (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr s)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))
(defun fn-sf-frontier-candidate (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr s))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))
(defun fn-sf-records (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr s)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))
(defun fn-sf-record-candidate (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr s))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                      (fn-ag-cdr (fn-ag-cdr s))))))))
(defun fn-sf-completion (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr s)))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                         (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))))
(defun fn-sf-successes (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr s))))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                         (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))))))
(defun fn-sf-barriers (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr s)))))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                         (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))))))

(defun fn-sf-make (phase frontier frontier-candidate records record-candidate
                         completion successes barriers)
  (declare (xargs :guard t :verify-guards nil))
  (list :store-files phase frontier frontier-candidate records record-candidate
        completion successes barriers))

(defun fn-sf-phasep (x)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal x
                '(:ready :reserved
                  :frontier-staged :frontier-data-durable :frontier-attempted
                  :record-staged :record-data-durable :aborting
                  :record-attempted :completing :completed
                  :replaying :recovering :fault
                  :fenced-frontier :fenced-reservation
                  :fenced-before-record :fenced-record
                  :fenced-core :fenced-recovery)))

(defun fn-sf-fencedp (s)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal (fn-sf-phase s)
                '(:fenced-frontier :fenced-reservation
                  :fenced-before-record :fenced-record
                  :fenced-core :fenced-recovery)))

(defun fn-sf-pairp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp x) (natp (car x)) (natp (cdr x))))

(defun fn-sf-record-pair (record)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cons (fn-record-sequence record) (fn-record-txid record))
       :exec (cons (fn-ag-car record)
                   (fn-ag-car (fn-ag-cdr record)))))

; Internal guard domain for the txid fold.  It adds no semantic validity rule;
; the stronger ordered record-list predicate remains the storage invariant.
(defun fn-sf-record-valuesp (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (and (fn-record-p (car records))
           (fn-sf-record-valuesp (cdr records)))
    (null records)))

(defun fn-sf-next-lower (records lower)
  (declare (xargs :guard (and (fn-sf-record-valuesp records)
                              (natp lower))
                  :verify-guards nil))
  (if (consp records)
      (fn-sf-next-lower (cdr records) (1+ (fn-record-txid (car records))))
    lower))

; Sequence numbers are contiguous.  Acceptance txids are strictly increasing,
; may have gaps, and are all below the durable allocator frontier.
(defun fn-sf-record-listp (records sequence lower frontier)
  (declare (xargs :guard (and (natp sequence) (natp lower) (natp frontier))
                  :verify-guards nil))
  (if (consp records)
      (let ((record (car records)))
        (and (fn-record-p record)
             (equal (fn-record-sequence record) sequence)
             (<= lower (fn-record-txid record))
             (< (fn-record-txid record) frontier)
             (equal (fn-record-generation record) (fn-record-txid record))
             (fn-sf-record-listp (cdr records) (1+ sequence)
                                 (1+ (fn-record-txid record)) frontier)))
    (null records)))

(defun fn-sf-candidatep (record records frontier)
  (declare (xargs :guard (and (fn-sf-record-valuesp records)
                              (natp frontier))
                  :verify-guards nil))
  (and (fn-record-p record)
       (equal (fn-record-sequence record) (len records))
       (equal (1+ (fn-record-txid record)) frontier)
       (<= (fn-sf-next-lower records 0) (fn-record-txid record))
       (equal (fn-record-generation record) (fn-record-txid record))))

(defun fn-sf-record-has-pairp (pair records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (or (equal pair (fn-sf-record-pair (car records)))
          (fn-sf-record-has-pairp pair (cdr records)))
    nil))

(defun fn-sf-success-listp (successes records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp successes)
      (and (fn-sf-pairp (car successes))
           (fn-sf-record-has-pairp (car successes) records)
           (fn-sf-success-listp (cdr successes) records))
    (null successes)))

(defun fn-sf-frontier-phasep (phase)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal phase
                '(:frontier-staged :frontier-data-durable
                  :frontier-attempted :fenced-frontier)))

(defun fn-sf-record-phasep (phase)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal phase
                '(:record-staged :record-data-durable :aborting
                  :record-attempted :fenced-before-record :fenced-record)))

(defun fn-sf-completion-phasep (phase)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal phase '(:completing :completed :fenced-core)))

(defun fn-sf-phase-shapep (s)
  (declare
   (xargs :guard
          (and (fn-sf-phasep (fn-sf-phase s))
               (fn-record-uint32p (fn-sf-frontier s))
               (fn-sf-record-listp (fn-sf-records s) 0 0
                                   (fn-sf-frontier s))
               (natp (fn-sf-barriers s)))
          :verify-guards nil))
  (let ((phase (fn-sf-phase s))
        (fc (fn-sf-frontier-candidate s))
        (rc (fn-sf-record-candidate s))
        (completion (fn-sf-completion s))
        (barriers (fn-sf-barriers s)))
    (cond
     ((equal phase :ready)
      (and (null fc) (null rc) (null completion)
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((equal phase :reserved)
      (and (null fc) (null rc) (null completion)
           (posp (fn-sf-frontier s))
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((fn-sf-frontier-phasep phase)
      (and (fn-record-uint32p fc)
           (equal fc (1+ (fn-sf-frontier s)))
           (null rc) (null completion)
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((fn-sf-record-phasep phase)
      (and (null fc) (fn-sf-candidatep rc (fn-sf-records s)
                                         (fn-sf-frontier s))
           (null completion)
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((fn-sf-completion-phasep phase)
      (and (null fc) (null rc) (fn-sf-pairp completion)
           (fn-sf-record-has-pairp completion (fn-sf-records s))
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((equal phase :replaying)
      (and (null fc) (null rc) (null completion) (equal barriers 0)))
     ((equal phase :recovering)
      (and (null fc) (null rc) (null completion)
           (< barriers *fn-sf-recovery-barrier-count*)))
     ((equal phase :fenced-recovery)
      (and (null fc) (null rc) (null completion)
           (< barriers *fn-sf-recovery-barrier-count*)))
     ((equal phase :fenced-reservation)
      (and (null fc) (null rc) (null completion)
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((equal phase :fault)
      (and (null fc) (null rc) (null completion)))
     (t nil))))

(defun fn-sf-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp s) (equal (len s) 9) (equal (car s) :store-files)
       (fn-sf-phasep (fn-sf-phase s))
       (fn-record-uint32p (fn-sf-frontier s))
       (fn-sf-record-listp (fn-sf-records s) 0 0 (fn-sf-frontier s))
       (fn-sf-success-listp (fn-sf-successes s) (fn-sf-records s))
       (natp (fn-sf-barriers s))
       (<= (fn-sf-barriers s) *fn-sf-recovery-barrier-count*)
       (fn-sf-phase-shapep s)))

(defun fn-sf-initial-state ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-sf-make :ready 0 nil nil nil nil nil
              *fn-sf-recovery-barrier-count*))

; -----------------------------------------------------------------------------
; Durable allocator replacement.

(defun fn-sf-start-frontier (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :ready)
           (< (fn-sf-frontier s) *fn-sf-max-uint*))
      (fn-sf-make :frontier-staged (fn-sf-frontier s)
                  (1+ (fn-sf-frontier s)) (fn-sf-records s) nil nil
                  (fn-sf-successes s) (fn-sf-barriers s))
    s))

(defun fn-sf-frontier-file-result (s result)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :frontier-staged))
      (cond
       ((equal result :ok)
        (fn-sf-make :frontier-data-durable (fn-sf-frontier s)
                    (fn-sf-frontier-candidate s) (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       ((equal result :known-fail)
        (fn-sf-make :ready (fn-sf-frontier s) nil (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

(defun fn-sf-frontier-replace-result (s result)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s)
           (equal (fn-sf-phase s) :frontier-data-durable))
      (cond
       ((equal result :ok)
        (fn-sf-make :frontier-attempted (fn-sf-frontier s)
                    (fn-sf-frontier-candidate s) (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       ((equal result :error)
        (fn-sf-make :fenced-frontier (fn-sf-frontier s)
                    (fn-sf-frontier-candidate s) (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

(defun fn-sf-frontier-dir-result (s result)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :frontier-attempted))
      (cond
       ((equal result :ok)
        (fn-sf-make :reserved (fn-sf-frontier-candidate s) nil
                    (fn-sf-records s) nil nil (fn-sf-successes s)
                    (fn-sf-barriers s)))
       ((equal result :error)
        (fn-sf-make :fenced-frontier (fn-sf-frontier s)
                    (fn-sf-frontier-candidate s) (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

; -----------------------------------------------------------------------------
; Whole-record publication.  Replay is the semantic admission check.

(defun fn-sf-replay-node (groups capacity records frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((answer (fn-replay groups capacity records)))
    (if (and (fn-replay-okp answer)
             (fn-replay-advance-okp (fn-replay-result-node answer) frontier))
        (fn-replay-advance-txid (fn-replay-result-node answer) frontier)
      nil)))

(defun fn-sf-history-recoverablep (groups capacity records frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((node (fn-sf-replay-node groups capacity records frontier)))
    (and (consp node) (fn-node-statep node)
         (equal (fn-state-next-txid (fn-node-acceptance node)) frontier))))

; A synchronous semantic refusal consumes the already durable reservation but
; publishes no record.  Invalid or mismatched events are no-ops.  An uncertain
; reply fences; crash/recovery will use the durable frontier without restoring a
; reservation token.
(defun fn-sf-refuse-reservation (s txid result)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :reserved)
           (natp txid) (equal (1+ txid) (fn-sf-frontier s)))
      (cond
       ((equal result :refused)
        (fn-sf-make :ready (fn-sf-frontier s) nil (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       ((equal result :uncertain)
        (fn-sf-make :fenced-reservation (fn-sf-frontier s) nil
                    (fn-sf-records s) nil nil (fn-sf-successes s)
                    (fn-sf-barriers s)))
       (t s))
    s))

(defun fn-sf-prepare-record (s record groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :reserved)
           (fn-sf-candidatep record (fn-sf-records s) (fn-sf-frontier s))
           (fn-sf-history-recoverablep
            groups capacity (append (fn-sf-records s) (list record))
            (fn-sf-frontier s)))
      (fn-sf-make :record-staged (fn-sf-frontier s) nil (fn-sf-records s)
                  record nil (fn-sf-successes s) (fn-sf-barriers s))
    s))

(defun fn-sf-record-file-result (s result)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :record-staged))
      (cond
       ((equal result :ok)
        (fn-sf-make :record-data-durable (fn-sf-frontier s) nil
                    (fn-sf-records s) (fn-sf-record-candidate s) nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       ((equal result :known-fail)
        (fn-sf-make :aborting (fn-sf-frontier s) nil (fn-sf-records s)
                    (fn-sf-record-candidate s) nil (fn-sf-successes s)
                    (fn-sf-barriers s)))
       (t s))
    s))

(defun fn-sf-prepublish-abort (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s)
           (equal (fn-sf-phase s) :record-data-durable))
      (fn-sf-make :aborting (fn-sf-frontier s) nil (fn-sf-records s)
                  (fn-sf-record-candidate s) nil (fn-sf-successes s)
                  (fn-sf-barriers s))
    s))

(defun fn-sf-abort-completion (s sequence txid result)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :aborting)
           (equal (cons sequence txid)
                  (fn-sf-record-pair (fn-sf-record-candidate s))))
      (cond
       ((equal result :matching)
        (fn-sf-make :ready (fn-sf-frontier s) nil (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       ((or (equal result :lost) (equal result :rejected))
        (fn-sf-make :fenced-before-record (fn-sf-frontier s) nil
                    (fn-sf-records s) (fn-sf-record-candidate s) nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

(defun fn-sf-record-link-result (s result)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s)
           (equal (fn-sf-phase s) :record-data-durable))
      (cond
       ((equal result :ok)
        (fn-sf-make :record-attempted (fn-sf-frontier s) nil
                    (fn-sf-records s) (fn-sf-record-candidate s) nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       ((equal result :error)
        (fn-sf-make :fenced-record (fn-sf-frontier s) nil
                    (fn-sf-records s) (fn-sf-record-candidate s) nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

(defun fn-sf-record-dir-result (s result)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :record-attempted))
      (cond
       ((equal result :ok)
        (let ((record (fn-sf-record-candidate s)))
          (fn-sf-make :completing (fn-sf-frontier s) nil
                      (append (fn-sf-records s) (list record)) nil
                      (fn-sf-record-pair record) (fn-sf-successes s)
                      (fn-sf-barriers s))))
       ((equal result :error)
        (fn-sf-make :fenced-record (fn-sf-frontier s) nil
                    (fn-sf-records s) (fn-sf-record-candidate s) nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

; The adapter's mutation gate is already closed in :completing.  Only the exact
; matching reply opens an acknowledgement decision; lost/rejected replies fence.
(defun fn-sf-core-completion (s sequence txid result)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :completing)
           (equal (cons sequence txid) (fn-sf-completion s)))
      (cond
       ((equal result :matching)
        (fn-sf-make :completed (fn-sf-frontier s) nil (fn-sf-records s) nil
                    (fn-sf-completion s) (fn-sf-successes s)
                    (fn-sf-barriers s)))
       ((or (equal result :lost) (equal result :rejected))
        (fn-sf-make :fenced-core (fn-sf-frontier s) nil (fn-sf-records s) nil
                    (fn-sf-completion s) (fn-sf-successes s)
                    (fn-sf-barriers s)))
       (t s))
    s))

(defun fn-sf-emit-success (s sequence txid)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :completed)
           (equal (cons sequence txid) (fn-sf-completion s)))
      (fn-sf-make :ready (fn-sf-frontier s) nil (fn-sf-records s) nil nil
                  (append (fn-sf-successes s) (list (cons sequence txid)))
                  (fn-sf-barriers s))
    s))

(defun fn-sf-lose-success (s sequence txid)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :completed)
           (equal (cons sequence txid) (fn-sf-completion s)))
      (fn-sf-make :ready (fn-sf-frontier s) nil (fn-sf-records s) nil nil
                  (fn-sf-successes s) (fn-sf-barriers s))
    s))

; -----------------------------------------------------------------------------
; Crash selection and recovery.  Choices describe namespace observations under
; the assumed atomic old/new replacement and absent/exact-link publication.

(defun fn-sf-crash-choicep (frontier-choice record-choice)
  (declare (xargs :guard t :verify-guards nil))
  (and (or (equal frontier-choice :old) (equal frontier-choice :new))
       (or (equal record-choice :absent) (equal record-choice :present))))

(defun fn-sf-frontier-new-visiblep (s)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal (fn-sf-phase s) '(:frontier-attempted :fenced-frontier)))

(defun fn-sf-record-present-visiblep (s)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal (fn-sf-phase s) '(:record-attempted :fenced-record)))

(defun fn-sf-crash (s frontier-choice record-choice)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s)
           (fn-sf-crash-choicep frontier-choice record-choice))
      (let* ((frontier
              (if (and (fn-sf-frontier-new-visiblep s)
                       (equal frontier-choice :new))
                  (fn-sf-frontier-candidate s)
                (fn-sf-frontier s)))
             (records
              (if (and (fn-sf-record-present-visiblep s)
                       (equal record-choice :present))
                  (append (fn-sf-records s)
                          (list (fn-sf-record-candidate s)))
                (fn-sf-records s))))
        (fn-sf-make :replaying frontier nil records nil nil
                    (fn-sf-successes s) 0))
    s))

; Recovery uses the observed frontier in the crash image.  No process-cached
; pre-error frontier is an argument to replay.
(defun fn-sf-recover (s groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :replaying))
      (if (fn-sf-history-recoverablep groups capacity (fn-sf-records s)
                                      (fn-sf-frontier s))
          (fn-sf-make :recovering (fn-sf-frontier s) nil (fn-sf-records s)
                      nil nil (fn-sf-successes s) 0)
        (fn-sf-make :fault (fn-sf-frontier s) nil (fn-sf-records s)
                    nil nil (fn-sf-successes s) 0))
    s))

(defun fn-sf-recovery-barrier (s result)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :recovering))
      (cond
       ((equal result :ok)
        (let ((next (1+ (fn-sf-barriers s))))
          (fn-sf-make
           (if (equal next *fn-sf-recovery-barrier-count*) :ready :recovering)
           (fn-sf-frontier s) nil (fn-sf-records s) nil nil
           (fn-sf-successes s) next)))
       ((equal result :uncertain)
        (fn-sf-make :fenced-recovery (fn-sf-frontier s) nil
                    (fn-sf-records s) nil nil (fn-sf-successes s)
                    (fn-sf-barriers s)))
       (t s))
    s))

; Guard-only list facts expose the domains already established by the storage
; recognizer.  They add no transition precondition or executable filter.
(local
 (defthm fn-sfg-record-values-are-a-true-list
   (implies (fn-sf-record-valuesp records)
            (true-listp records))))

(local
 (defthm fn-sfg-record-list-implies-values
   (implies (fn-sf-record-listp records sequence lower frontier)
            (fn-sf-record-valuesp records))
   :hints (("Goal" :induct (fn-sf-record-listp
                             records sequence lower frontier)))))

(local
 (defthm fn-sfg-success-list-is-a-true-list
   (implies (fn-sf-success-listp successes records)
            (true-listp successes))))

(local
 (defthm fn-sfg-state-records-have-guard-domain
   (implies (fn-sf-statep s)
            (and (fn-sf-record-valuesp (fn-sf-records s))
                 (true-listp (fn-sf-records s))
                 (true-listp (fn-sf-successes s))))
   :hints (("Goal" :in-theory (enable fn-sf-statep)))))

; The complete executable file kernel is guard verified.  Selectors preserve
; their original total ACL2 semantics through the guarded acceptance helpers.
(verify-guards fn-sf-phase)
(verify-guards fn-sf-frontier)
(verify-guards fn-sf-frontier-candidate)
(verify-guards fn-sf-records)
(verify-guards fn-sf-record-candidate)
(verify-guards fn-sf-completion)
(verify-guards fn-sf-successes)
(verify-guards fn-sf-barriers)
(verify-guards fn-sf-make)
(verify-guards fn-sf-phasep)
(verify-guards fn-sf-fencedp)
(verify-guards fn-sf-pairp)
(verify-guards fn-sf-record-pair)
(verify-guards fn-sf-record-valuesp)
(verify-guards fn-sf-next-lower)
(verify-guards fn-sf-record-listp)
(verify-guards fn-sf-candidatep
 :hints (("Goal" :use fn-sfg-record-values-are-a-true-list)))
(verify-guards fn-sf-record-has-pairp)
(verify-guards fn-sf-success-listp)
(verify-guards fn-sf-frontier-phasep)
(verify-guards fn-sf-record-phasep)
(verify-guards fn-sf-completion-phasep)
(verify-guards fn-sf-phase-shapep
 :hints (("Goal" :use fn-sfg-record-list-implies-values)))
(verify-guards fn-sf-statep
 :hints (("Goal" :use fn-sfg-record-list-implies-values)))
(verify-guards fn-sf-initial-state)
(verify-guards fn-sf-start-frontier)
(verify-guards fn-sf-frontier-file-result)
(verify-guards fn-sf-frontier-replace-result)
(verify-guards fn-sf-frontier-dir-result)
(verify-guards fn-sf-replay-node)
(verify-guards fn-sf-history-recoverablep)
(verify-guards fn-sf-refuse-reservation)
(verify-guards fn-sf-prepare-record
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-record-file-result)
(verify-guards fn-sf-prepublish-abort)
(verify-guards fn-sf-abort-completion)
(verify-guards fn-sf-record-link-result)
(verify-guards fn-sf-record-dir-result
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-core-completion)
(verify-guards fn-sf-emit-success
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-lose-success)
(verify-guards fn-sf-crash-choicep)
(verify-guards fn-sf-frontier-new-visiblep)
(verify-guards fn-sf-record-present-visiblep)
(verify-guards fn-sf-crash
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-recover)
(verify-guards fn-sf-recovery-barrier)

; -----------------------------------------------------------------------------
; Initial general facts for the kernel.

(defthm fn-sf-initial-state-is-state
  (fn-sf-statep (fn-sf-initial-state)))

(defthm fn-sf-start-frontier-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-start-frontier s))))

(defthm fn-sf-fenced-rejects-frontier-start
  (implies (and (fn-sf-statep s) (fn-sf-fencedp s))
           (equal (fn-sf-start-frontier s) s)))

(defthm fn-sf-fenced-rejects-record-prepare
  (implies (and (fn-sf-statep s) (fn-sf-fencedp s))
           (equal (fn-sf-prepare-record s record groups capacity) s)))

(defthm fn-sf-success-requires-matching-completion
  (implies (not (and (equal (fn-sf-phase s) :completed)
                     (equal (cons sequence txid) (fn-sf-completion s))))
           (equal (fn-sf-emit-success s sequence txid) s)))

(defthm fn-sf-incomplete-recovery-barrier-is-not-ready
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :recovering)
                (< (fn-sf-barriers s) 4))
           (not (equal (fn-sf-phase (fn-sf-recovery-barrier s :ok))
                       :ready))))

(defthm fn-sf-fenced-rejects-success
  (implies (and (fn-sf-statep s) (fn-sf-fencedp s))
           (equal (fn-sf-emit-success s sequence txid) s)))

(defthm fn-sf-frontier-replace-error-fences
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :frontier-data-durable))
           (fn-sf-fencedp (fn-sf-frontier-replace-result s :error))))

(defthm fn-sf-lost-core-completion-fences
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :completing)
                (equal (cons sequence txid) (fn-sf-completion s)))
           (fn-sf-fencedp
            (fn-sf-core-completion s sequence txid :lost))))
