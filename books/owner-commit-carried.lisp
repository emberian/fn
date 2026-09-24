;; fn: the owner's commit the host calls, with the history's shape carried.
;
; fn-own-finish (books/owner-served-invariants.lisp) reads the store's
; completion record through fn-sn-completion-record, which is
; fn-sn-find-record: a walk of the whole durable history that computes
; fn-sf-record-pair of every record, and that pair dispatches on the event
; kind through fn-record-p (books/store-events.lisp fn-store-event-sequence,
; fn-store-event-txid), which walks each record's octets.  One commit reached
; it ten times (core gate twice, completion gate twice, the finish once, all
; of it again inside fn-own-complete, and the submission check once):
; O(N * L) per POST for N records of L octets, 60 percent of commit CPU at
; N = 120 (planning/evidence/served-path-cost-2026-09-24.md).
;
; The history's shape is already carried.  fn-sn-statep conjoins
; fn-sf-statep, which conjoins (fn-sf-record-listp records 0 0 frontier):
; every record is a store event and the record at position i has sequence
; number i.  It is fn-own-finish's own guard; fn-own-relation (through
; fn-snt-relation) and fn-ocl-relation (through fn-cst-relation) carry it
; from open, and fn-sn-finish-preserves-state keeps it across every commit.
; Under it the record whose pair is P can only sit at position (car P), so
; fn-ccar-seek steps (car P) conses without looking at them and computes one
; pair.  Every definition below is its reference with fn-sn-completion-record
; replaced by fn-ccar-completion-record, and is proved equal to it under
; fn-sn-statep of the store.  host/owner-host.lisp fn-owner-finish-submission
; calls fn-ccar-own-finish.

(in-package "ACL2")
(include-book "owner-served-invariants")
(include-book "owner-invariants")
(include-book "config-owner-live")

; -----------------------------------------------------------------------------
; The lookup.

; SEQ is the sequence number the first of RECORDS carries.  While it is below
; the pair's sequence the record cannot be the one, and it is skipped
; without computing its pair; at the first record that could be, the pair is
; compared once and the walk stops.
(defun fn-ccar-seek (pair records seq)
  (declare (xargs :guard (natp seq)))
  (if (consp records)
      (if (and (consp pair) (natp (car pair)) (< seq (car pair)))
          (fn-ccar-seek pair (cdr records) (1+ seq))
        (if (equal pair (fn-sf-record-pair (car records)))
            (car records)
          nil))
    nil))

(local
 (defthm fn-ccar-find-record-past-sequence-is-nil
  (implies (and (fn-sf-record-listp records seq lower frontier)
                (or (not (consp pair))
                    (not (natp (car pair)))
                    (< (car pair) seq)))
           (equal (fn-sn-find-record pair records) nil))
  :hints (("Goal" :in-theory (enable fn-sf-record-pair)))))

; KEYSTONE (lookup).  On a history of contiguous sequence numbers starting at
; SEQ, the seek is the whole-history search, for every pair.  Nothing about
; txids is used: the sequence numbers alone place each record.
(defthm fn-ccar-seek-is-find-record
  (implies (fn-sf-record-listp records seq lower frontier)
           (equal (fn-ccar-seek pair records seq)
                  (fn-sn-find-record pair records)))
  :hints (("Goal" :in-theory (enable fn-sf-record-pair)
           :induct (fn-sf-record-listp records seq lower frontier))))

(defun fn-ccar-completion-record (s)
  (declare (xargs :guard t))
  (fn-ccar-seek (fn-sf-completion (fn-sn-files s))
                (fn-sf-records (fn-sn-files s)) 0))

(defthm fn-ccar-completion-record-is-completion-record
  (implies (fn-sn-statep s)
           (equal (fn-ccar-completion-record s)
                  (fn-sn-completion-record s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-sf-statep
                                   fn-sn-completion-record)
                                  (fn-node-statep fn-ccar-seek
                                   fn-sn-find-record)))))

(in-theory (disable fn-ccar-completion-record))

; -----------------------------------------------------------------------------
; The store's completion gates and finish (books/store-node.lisp), carried.

(defun fn-ccar-completion-core-enabledp (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (let ((record (fn-ccar-completion-record s)))
         (and (cond ((fn-store-retention-event-p record)
                (consp (fn-replay-apply-retention-event (fn-sn-node s) record)))
               ((or (fn-stxe-p record) (fn-stxk-p record) (fn-stxa-p record))
                (and (consp (fn-replay-apply-record (fn-sn-node s) record))
                     (equal (fn-stxk-context-kind
                             (fn-replay-identity-step
                              (fn-sn-identity-context s) record)) :ok)))
               ((or (fn-cpe-eventp record) (fn-th-topic-eventp record))
                (consp (fn-replay-apply-record (fn-sn-node s) record)))
               (t (fn-sn-record-bindsp (fn-sn-node s) record)))
              (equal (fn-sf-completion (fn-sn-files s))
                     (fn-sf-record-pair record))))))

(defthm fn-ccar-completion-core-enabledp-is-reference
  (equal (fn-ccar-completion-core-enabledp s)
         (fn-sn-completion-core-enabledp s))
  :hints (("Goal" :cases ((fn-sn-statep s))
           :in-theory (e/d (fn-ccar-completion-core-enabledp
                                   fn-sn-completion-core-enabledp)
                                  (fn-sn-statep fn-sf-statep fn-node-statep
                                   fn-sn-completion-record
                                   fn-record-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-cpe-eventp fn-th-topic-eventp)))))

(verify-guards fn-ccar-completion-core-enabledp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep)
                                  (fn-sf-statep fn-node-statep
                                   fn-record-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-cpe-eventp fn-th-topic-eventp)))))

(in-theory (disable fn-ccar-completion-core-enabledp))

(defun fn-ccar-completion-enabledp (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (fn-ccar-completion-core-enabledp s)
       (let ((record (fn-ccar-completion-record s)))
         (and (eq (car (fn-cpe-projection-step
                        (fn-sn-consumer s) record (fn-sn-identity-next s))) :ok)
              (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) record)) :ok)))))

(defthm fn-ccar-completion-enabledp-is-reference
  (equal (fn-ccar-completion-enabledp s)
         (fn-sn-completion-enabledp s))
  :hints (("Goal" :cases ((fn-sn-statep s))
           :in-theory (e/d (fn-ccar-completion-enabledp
                            fn-sn-completion-enabledp)
                           (fn-sn-statep fn-sn-completion-record
                            fn-cpe-projection-step fn-th-prefix-step))
           :use ((:instance fn-sn-completion-core-enabledp)))))

(verify-guards fn-ccar-completion-enabledp)

(in-theory (disable fn-ccar-completion-enabledp))

; fn-sn-finish with the carried record.  The body is the reference's.
(defun fn-ccar-sn-finish (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (fn-ccar-completion-enabledp s)
      (let* ((record (fn-ccar-completion-record s))
             (retentionp (fn-store-retention-event-p record))
             (consumerp (fn-cpe-eventp record))
             (topicp (fn-th-topic-eventp record))
             (identityp (or (fn-stxe-p record) (fn-stxk-p record)
                            (fn-stxa-p record)))
             (projection (fn-cpe-projection-step
                          (fn-sn-consumer s) record (fn-sn-identity-next s)))
             (topic-projection (fn-th-prefix-step (fn-sn-topic s) record))
             (node (cond (retentionp
                          (fn-replay-apply-retention-event (fn-sn-node s) record))
                         ((or identityp consumerp topicp)
                          (fn-replay-apply-record (fn-sn-node s) record))
                         (t
                          (fn-node-complete (fn-sn-node s) (fn-record-txid record)
                                            (fn-record-generation record) :durable))))
             (files (fn-sf-core-completion
                     (fn-sn-files s) (fn-store-event-sequence record)
                     (fn-store-event-txid record))))
        (fn-sn-with-topic
         (fn-sn-with-consumer
          (if (or retentionp consumerp topicp)
            (fn-sn-advance-identity-next
             (fn-sn-update-indexed
              s (fn-sf-emit-success files (fn-store-event-sequence record)
                                    (fn-store-event-txid record))
              node (fn-sn-index s)))
          (if identityp
              (fn-sn-finish-identity
               s (fn-sf-emit-success files (fn-store-event-sequence record)
                                     (fn-store-event-txid record))
               record node)
            (fn-sn-advance-identity-next
             (fn-sn-update-accepted
              s (fn-sf-emit-success files (fn-store-event-sequence record)
                                    (fn-store-event-txid record))
              node
              (fn-stx-index-add (fn-sn-index s) (fn-sn-accepted-delta s))
              (fn-record-msgid record)
              (fn-stx-verdict-of-octets
               (fn-record-payload record)
               (fn-sn-keyring s) (fn-sn-keyring-generation s))))))
          (fn-cp-nth 1 projection))
         topic-projection))
    s))

(defthm fn-ccar-sn-finish-is-sn-finish
  (equal (fn-ccar-sn-finish s) (fn-sn-finish s))
  :hints (("Goal" :cases ((fn-sn-statep s))
           :in-theory (union-theories
                       '(fn-ccar-sn-finish fn-sn-finish
                         fn-ccar-completion-enabledp-is-reference
                         fn-ccar-completion-record-is-completion-record)
                       (theory 'minimal-theory))
           :use ((:instance fn-sn-completion-enabledp)
                 (:instance fn-sn-completion-core-enabledp)))))

(verify-guards fn-ccar-sn-finish
  :hints (("Goal" :in-theory
           (e/d (fn-sn-statep fn-ccar-completion-enabledp-is-reference
                 fn-ccar-completion-record-is-completion-record)
                (fn-sf-statep fn-node-statep fn-sn-completion-record
                 fn-node-pending-matchesp fn-sn-pending-record
                 fn-sn-prepare-node fn-sf-core-completion
                 fn-sn-accepted-delta
                 fn-sn-completion-enabledp fn-sn-record-bindsp
                 fn-sn-identity-context fn-replay-identity-step
                 fn-replay-apply-retention-event fn-replay-apply-record
                 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-record-record-vocabulary fn-record-shape-vocabulary)))))

(in-theory (disable fn-ccar-sn-finish))

; -----------------------------------------------------------------------------
; The owner's completion and commit (books/owner.lisp fn-own-complete,
; books/owner-served-invariants.lisp fn-own-finish), carried.

(defun fn-ccar-own-complete (o)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (let ((s (fn-own-store o)))
    (if (fn-ccar-completion-enabledp s)
        (fn-own-refresh
         (fn-own-make (fn-ccar-sn-finish s) (fn-own-view o) (fn-own-conns o)
                      (fn-own-next-id o) (fn-own-max-conns o) nil
                      (fn-ag-append (fn-own-ledger o)
                                    (list (fn-sf-completion (fn-sn-files s))))
                      (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                      (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)))
      o)))

(defthm fn-ccar-own-complete-is-own-complete
  (equal (fn-ccar-own-complete o) (fn-own-complete o))
  :hints (("Goal" :in-theory (e/d (fn-ccar-own-complete fn-own-complete)
                                  (fn-sn-statep fn-sn-finish
                                   fn-sn-completion-enabledp fn-own-refresh)))))

(defun fn-ccar-completion-names-submission-p (o cfg)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (let ((sub (fn-own-inflight o))
        (record (fn-ccar-completion-record (fn-own-store o))))
    (and sub
         (fn-record-p record)
         (equal (fn-record-msgid record)
                (fn-record-octets-string (fn-own-sub-msgid sub)))
         (equal (fn-record-payload record) (fn-own-sub-stored-octets cfg sub))
         t)))

(defthm fn-ccar-completion-names-submission-p-is-reference
  (implies (fn-sn-statep (fn-own-store o))
           (equal (fn-ccar-completion-names-submission-p o cfg)
                  (fn-own-completion-names-submission-p o cfg)))
  :hints (("Goal" :in-theory (e/d (fn-ccar-completion-names-submission-p
                                   fn-own-completion-names-submission-p)
                                  (fn-sn-statep fn-sn-completion-record
                                   fn-record-p)))))

; The function host/owner-host.lisp fn-owner-finish-submission calls.
(defun fn-ccar-own-finish (o cfg)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (cons (if (and (fn-ccar-completion-enabledp (fn-own-store o))
                 (fn-ccar-completion-names-submission-p o cfg))
            :durable
          :fault)
        (fn-ccar-own-complete o)))

; KEYSTONE for the host line: the carried commit is the reference commit,
; word and owner, for every owner and every configuration.  No hypothesis:
; both completion gates conjoin (mbe :logic (fn-sn-statep s) :exec t), so
; off the premise both refuse in the logic, and on it the record found is
; the same.  What the premise buys is the executed code: the raw function
; drops that conjunct and runs the seek, and guard verification (the guard
; is fn-own-finish's own, fn-sn-statep of the store) is what equates the raw
; function with this logical one on every owner whose store satisfies it.
(defthm fn-ccar-own-finish-is-own-finish
  (equal (fn-ccar-own-finish o cfg) (fn-own-finish o cfg))
  :hints (("Goal" :cases ((fn-sn-statep (fn-own-store o)))
           :in-theory (e/d (fn-ccar-own-finish fn-own-finish)
                           (fn-sn-statep fn-own-complete
                            fn-ccar-own-complete
                            fn-own-completion-names-submission-p
                            fn-ccar-completion-names-submission-p))
           :use ((:instance fn-sn-completion-enabledp (s (fn-own-store o)))
                 (:instance fn-sn-completion-core-enabledp
                            (s (fn-own-store o)))))))

(in-theory (disable fn-ccar-own-complete fn-ccar-completion-names-submission-p
                    fn-ccar-own-finish))

; -----------------------------------------------------------------------------
; The premise is carried, not evaluated.

; Both owner relations conjoin it: fn-own-relation through fn-snt-relation,
; fn-ocl-relation through fn-cst-relation.
(defthm fn-ccar-relation-carries-sn-statep
  (implies (fn-own-relation o)
           (fn-sn-statep (fn-own-store o)))
  :hints (("Goal" :in-theory (e/d (fn-own-relation
                                   fn-snt-relation-implies-structural-state)
                                  (fn-sn-statep fn-snt-relation)))))

(defthm fn-ccar-ocl-relation-carries-sn-statep
  (implies (fn-ocl-relation oc)
           (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation fn-cst-relation)
                                  (fn-sn-statep)))))

; Preservation.  The owner after the carried commit satisfies the owner
; relation again (fn-own-complete-preserves-relation over the reference).
(defthm fn-ccar-own-finish-preserves-relation
  (implies (fn-own-relation o)
           (fn-own-relation (cdr (fn-ccar-own-finish o cfg))))
  :hints (("Goal" :in-theory (e/d (fn-own-finish)
                                  (fn-own-relation fn-own-complete)))))

; And the premise itself survives the commit with nothing else assumed:
; the new store is fn-sn-finish of the old or the old
; (fn-sn-finish-preserves-state), and fn-own-refresh keeps the store.
(defthm fn-ccar-own-finish-preserves-sn-statep
  (implies (fn-sn-statep (fn-own-store o))
           (fn-sn-statep (fn-own-store (cdr (fn-ccar-own-finish o cfg)))))
  :hints (("Goal" :in-theory (e/d (fn-own-finish fn-own-complete
                                   fn-own-refresh-keeps-fields)
                                  (fn-sn-statep fn-sn-finish fn-own-refresh
                                   fn-sn-completion-enabledp)))))

(in-theory (disable fn-ccar-seek))
