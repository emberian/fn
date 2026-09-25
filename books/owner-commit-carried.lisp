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
;
; The kind is carried too (lane carry-kind, 2026-09-25).  Every record of
; the history is a Store event under fn-sn-statep (fn-sf-record-valuesp), so
; the record the seek finds is one, and its pair, sequence, txid and kind are
; read through the carried accessors of books/store-events-carried.lisp,
; whose guard is that fact, instead of the dispatchers that re-run
; fn-record-p and fn-stxa-p over the record's octets on every read.  The
; completion gate is evaluated once per commit (it was three times: the
; commit's word, the owner's completion and the store's finish), and
; fn-ccar-ocfg-complete (equal to fn-ocfg-step of (:complete), no
; hypothesis) is the completion host/owner-host.lisp fn-owner-finish installs
; for identity, retention, consumer and topic events, which used to go through
; the unverified fn-ocfg-step and the whole-history fn-sn-find-record.

(in-package "ACL2")
(include-book "owner-served-invariants")
(include-book "owner-invariants")
(include-book "config-owner-live")
(include-book "records-concrete")
(include-book "store-events-carried")

; -----------------------------------------------------------------------------
; The lookup.

; SEQ is the sequence number the first of RECORDS carries.  While it is below
; the pair's sequence the record cannot be the one, and it is skipped
; without computing its pair; at the first record that could be, the pair is
; compared once and the walk stops.
(defun fn-ccar-seek (pair records seq)
  (declare (xargs :guard (and (natp seq) (fn-sf-record-valuesp records))))
  (if (consp records)
      (if (and (consp pair) (natp (car pair)) (< seq (car pair)))
          (fn-ccar-seek pair (cdr records) (1+ seq))
        (if (equal pair (cons (fn-evc-sequence (car records))
                              (fn-evc-txid (car records))))
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
  :hints (("Goal" :in-theory (enable fn-sf-record-pair fn-evc-carried-definitions)
           :induct (fn-sf-record-listp records seq lower frontier))))

(local
 (defthm fn-ccar-record-list-implies-values
   (implies (fn-sf-record-listp records sequence lower frontier)
            (fn-sf-record-valuesp records))
   :hints (("Goal" :induct (fn-sf-record-listp
                             records sequence lower frontier)
            :in-theory (disable fn-store-event-p)))))

(defthm fn-ccar-sn-statep-carries-record-values
  (implies (fn-sn-statep s)
           (fn-sf-record-valuesp (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep fn-sf-statep)
                                  (fn-node-statep fn-store-event-p)))))

; What the seek finds is a record of the history, so a Store event.
(defthm fn-ccar-seek-finds-a-store-event
  (implies (and (fn-sf-record-valuesp records)
                (fn-ccar-seek pair records seq))
           (fn-store-event-p (fn-ccar-seek pair records seq)))
  :hints (("Goal" :induct (fn-ccar-seek pair records seq)
           :in-theory (disable fn-store-event-p))))

(defun fn-ccar-completion-record (s)
  (declare (xargs :guard (fn-sn-statep s)))
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

(defthm fn-ccar-completion-record-is-a-store-event
  (implies (and (fn-sn-statep s) (fn-ccar-completion-record s))
           (fn-store-event-p (fn-ccar-completion-record s)))
  :hints (("Goal" :in-theory '(fn-ccar-completion-record
                               fn-ccar-seek-finds-a-store-event
                               fn-ccar-sn-statep-carries-record-values))))

(in-theory (disable fn-ccar-completion-record))

; -----------------------------------------------------------------------------
; The two projection steps the completion gate runs, carried: their
; references (books/consumer-store-projection.lisp, topic-history-prefix.lisp)
; recognize the event as a Store event and then dispatch on its kind; with
; the recognition carried (the guard), the test is t and the dispatch reads
; the shape.  Each equals its reference with no hypothesis.

(defun fn-ccar-cpe-projection-step (s event expected)
  (declare (xargs :guard (fn-store-event-p event) :verify-guards nil))
  (if (or (not (mbe :logic (if (fn-store-event-p event) t nil) :exec t))
          (not (fn-cp-uintp expected))
          (equal expected *fn-cbor-max-uint*)
          (not (equal (fn-evc-sequence event) expected)))
      (list :refused :sequence)
    (if (not (fn-evc-consumerp event))
        (if (null s) (list :ok nil)
          (if (equal (fn-cp-nth 3 s) expected)
              (list :ok (fn-cpe-projection-advance s (1+ expected)))
            (list :refused :frontier)))
      (let* ((op (fn-cpe-operation event))
             (kind (fn-cp-nth 0 op)))
        (cond
         ((eq kind :bootstrap)
          (if (null s)
              (list :ok (fn-cp-initial (fn-cp-nth 1 op)
                                       (fn-cp-nth 2 op) (1+ expected)))
            (list :refused :duplicate-bootstrap)))
         ((null s) (list :refused :unbootstrapped))
         ((not (equal (fn-cp-nth 3 s) expected))
          (list :refused :frontier))
         ((eq kind :rollover)
          (if (equal (fn-cp-nth 1 op) (fn-cp-nth 2 s))
              (list :refused :same-incarnation)
            (list :ok
                  (fn-cp-state (fn-cp-nth 1 s) (fn-cp-nth 1 op)
                               (1+ expected) (fn-cp-nth 4 s) nil))))
         ((equal (fn-cpe-projection-decision s op) (list :write op))
          (list :ok (fn-cpe-projection-advance (fn-cp-apply s op)
                                                 (1+ expected))))
         (t (list :refused :operation)))))))

(defthm fn-ccar-cpe-projection-step-is-cpe-projection-step
  (equal (fn-ccar-cpe-projection-step s event expected)
         (fn-cpe-projection-step s event expected))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-ccar-cpe-projection-step fn-cpe-projection-step
                                fn-evc-carried-definitions)
                              (theory 'minimal-theory)))))

(verify-guards fn-ccar-cpe-projection-step
  :hints (("Goal" :use ((:guard-theorem fn-rcon-cpe-projection-step))
           :in-theory (e/d (fn-evc-carried-definitions
                            fn-rcon-store-event-sequence-is-store-event-sequence)
                           (fn-store-event-p fn-cpe-eventp)))))

(defthm fn-ccar-cpe-projection-step-is-a-cons
  (consp (fn-ccar-cpe-projection-step s event expected))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-ccar-cpe-projection-step))))

(in-theory (disable fn-ccar-cpe-projection-step))

(defun fn-ccar-th-prefix-step (projection event)
  (declare (xargs :guard (fn-store-event-p event) :verify-guards nil))
  (let ((status (fn-th-at 0 projection))
        (next (fn-th-at 1 projection))
        (snapshots (fn-th-at 2 projection))
        (accepted (fn-th-at 3 projection))
        (anchors (fn-th-at 4 projection))
        (installed (fn-th-at 5 projection)))
    (cond
     ((not (equal status :ok)) projection)
     ((or (not (mbe :logic (if (fn-store-event-p event) t nil) :exec t))
          (not (equal next (fn-evc-sequence event))))
      (fn-th-prefix-state :fault next snapshots accepted anchors installed
                          :sequence))
     ((fn-evc-stxkp event)
      (fn-th-prefix-state :ok (1+ (nfix next)) (cons event snapshots)
                          accepted anchors installed nil))
     ((fn-evc-stxap event)
      (fn-th-prefix-state :ok (1+ (nfix next)) snapshots
                          (cons event accepted) anchors installed nil))
     ((fn-th-local-admin-eventp event)
      (let ((updated (fn-th-local-admin-commit event installed)))
        (if (fn-stmt-okp updated)
            (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted
                                anchors (fn-stmt-value updated) nil)
          (fn-th-prefix-state :fault next snapshots accepted anchors installed
                              :administrator-install))))
     ((fn-evc-topicp event)
      (let* ((ref (if (eq (fn-th-at 0 event) :topic-anchor)
                      (fn-th-at 5 event) (fn-th-at 7 event)))
             (source (fn-th-prefix-find-ref ref accepted))
             (snapshot (and source
                            (fn-stxk-find (fn-stxa-keyring-generation source)
                                          snapshots)))
             (updated
              (if (and source snapshot)
                  (if (eq (fn-th-at 0 event) :topic-anchor)
                      (if (fn-th-topic-v1-anchorp event)
                          (fn-th-commit-anchor event source snapshot
                                               (fn-th-at 5 installed) anchors)
                        (fn-th-commit-anchor-installed-v2
                         event source snapshot installed anchors))
                    (fn-th-commit-report event source snapshot anchors))
                (fn-stmt-error :missing-historical-authorship))))
        (if (fn-stmt-okp updated)
            (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted
                                (fn-stmt-value updated) installed nil)
          (fn-th-prefix-state :fault next snapshots accepted anchors installed
                              (fn-stmt-value updated)))))
     (t (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted anchors
                            installed nil)))))

(defthm fn-ccar-th-prefix-step-is-th-prefix-step
  (equal (fn-ccar-th-prefix-step projection event)
         (fn-th-prefix-step projection event))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-ccar-th-prefix-step fn-th-prefix-step
                                fn-evc-carried-definitions)
                              (theory 'minimal-theory)))))

(verify-guards fn-ccar-th-prefix-step
  :hints (("Goal" :use ((:guard-theorem fn-rcon-th-prefix-step))
           :in-theory (e/d (fn-evc-carried-definitions
                            fn-rcon-store-event-sequence-is-store-event-sequence)
                           (fn-store-event-p fn-stxk-p fn-stxa-p
                            fn-th-topic-eventp fn-th-local-admin-eventp)))))

(in-theory (disable fn-ccar-th-prefix-step))

; -----------------------------------------------------------------------------
; The store's completion gates and finish (books/store-node.lisp), carried.

; The binding test of an article record (books/store-node.lisp
; fn-sn-record-bindsp), with the record's recognition carried.
(defun fn-ccar-sn-record-bindsp (node record)
  (declare (xargs :guard (and (fn-node-statep node) (fn-store-event-p record))
                  :verify-guards nil))
  (and (fn-evc-recordp record)
       (fn-node-pending-matchesp node (fn-record-txid record)
                                (fn-record-generation record))
       (equal record (fn-sn-pending-record node (fn-record-sequence record)))))

(defthm fn-ccar-sn-record-bindsp-is-sn-record-bindsp
  (equal (fn-ccar-sn-record-bindsp node record) (fn-sn-record-bindsp node record))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-ccar-sn-record-bindsp fn-sn-record-bindsp
                                fn-evc-carried-definitions)
                              (theory 'minimal-theory)))))

(verify-guards fn-ccar-sn-record-bindsp
  :hints (("Goal" :use ((:guard-theorem fn-rcon-sn-record-bindsp))
                  :in-theory (e/d (fn-evc-carried-definitions
                                   fn-rcon-record-p-is-record-p)
                                  (fn-store-event-p fn-node-statep
                                   fn-node-pending-matchesp fn-sn-pending-record)))))

(in-theory (disable fn-ccar-sn-record-bindsp))

; The gate reads the found record's kind once it is known to be a record of
; the history; `record' is the nil test the reference's recognizers made.
(defun fn-ccar-completion-core-enabledp (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (let ((record (fn-ccar-completion-record s)))
         (and record
              (cond ((fn-evc-retentionp record)
                     (consp (fn-replay-apply-retention-event (fn-sn-node s) record)))
                    ((or (fn-evc-stxep record) (fn-evc-stxkp record)
                         (fn-evc-stxap record))
                     (and (consp (fn-replay-apply-record (fn-sn-node s) record))
                          (equal (fn-stxk-context-kind
                                  (fn-replay-identity-step
                                   (fn-sn-identity-context s) record)) :ok)))
                    ((or (fn-evc-consumerp record) (fn-evc-topicp record))
                     (consp (fn-replay-apply-record (fn-sn-node s) record)))
                    (t (fn-ccar-sn-record-bindsp (fn-sn-node s) record)))
              (equal (fn-sf-completion (fn-sn-files s))
                     (cons (fn-evc-sequence record) (fn-evc-txid record)))))))

; The reference's recognizers refuse nil; so does its binding test.
(local
 (defthm fn-ccar-no-record-binds
   (not (fn-sn-record-bindsp node nil))
   :hints (("Goal" :in-theory '(fn-sn-record-bindsp
                                (:executable-counterpart fn-record-p))))))

(defthm fn-ccar-completion-core-enabledp-is-reference
  (equal (fn-ccar-completion-core-enabledp s)
         (fn-sn-completion-core-enabledp s))
  :hints (("Goal" :cases ((fn-sn-statep s))
           :in-theory (e/d (fn-ccar-completion-core-enabledp
                            fn-sn-completion-core-enabledp
                            fn-evc-carried-definitions
                            fn-ccar-sn-record-bindsp-is-sn-record-bindsp
                            fn-ccar-no-record-binds fn-sf-record-pair)
                           (fn-sn-statep fn-sf-statep fn-node-statep
                            fn-sn-completion-record fn-ccar-completion-record
                            fn-record-p fn-store-retention-event-p
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-cpe-eventp fn-th-topic-eventp
                            fn-store-event-sequence fn-store-event-txid
                            fn-replay-apply-record fn-replay-identity-step
                            fn-replay-apply-retention-event
                            fn-sn-record-bindsp)))))

; An enabled gate found a record of the history.
(defthm fn-ccar-core-enabled-finds-a-store-event
  (implies (fn-ccar-completion-core-enabledp s)
           (and (fn-sn-statep s)
                (fn-store-event-p (fn-ccar-completion-record s))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory '(fn-ccar-completion-core-enabledp
                               fn-ccar-completion-record-is-a-store-event))))

(verify-guards fn-ccar-completion-core-enabledp
  :hints (("Goal" :use ((:instance fn-ccar-completion-record-is-a-store-event))
                  :in-theory (e/d (fn-sn-statep fn-evc-carried-definitions)
                                  (fn-ccar-completion-record-is-completion-record
                                   fn-ccar-completion-record-is-a-store-event
                                   fn-sf-statep fn-node-statep
                                   fn-record-p fn-store-retention-event-p
                                   fn-stxe-p fn-stxk-p fn-stxa-p fn-store-event-p
                                   fn-cpe-eventp fn-th-topic-eventp)))))

(in-theory (disable fn-ccar-completion-core-enabledp))

(defun fn-ccar-completion-enabledp (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (fn-ccar-completion-core-enabledp s)
       (let ((record (fn-ccar-completion-record s)))
         (and (eq (car (fn-ccar-cpe-projection-step
                        (fn-sn-consumer s) record (fn-sn-identity-next s))) :ok)
              (eq (fn-th-at 0 (fn-ccar-th-prefix-step (fn-sn-topic s) record)) :ok)))))

(defthm fn-ccar-completion-enabledp-is-reference
  (equal (fn-ccar-completion-enabledp s)
         (fn-sn-completion-enabledp s))
  :hints (("Goal" :cases ((fn-sn-statep s))
           :in-theory (e/d (fn-ccar-completion-enabledp
                            fn-sn-completion-enabledp
                            fn-ccar-cpe-projection-step-is-cpe-projection-step
                            fn-ccar-th-prefix-step-is-th-prefix-step)
                           (fn-sn-statep fn-sn-completion-record
                            fn-cpe-projection-step fn-th-prefix-step))
           :use ((:instance fn-sn-completion-core-enabledp)))))

(defthm fn-ccar-enabled-finds-a-store-event
  (implies (fn-ccar-completion-enabledp s)
           (and (fn-sn-statep s)
                (fn-ccar-completion-core-enabledp s)
                (fn-store-event-p (fn-ccar-completion-record s))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory '(fn-ccar-completion-enabledp
                               fn-ccar-core-enabled-finds-a-store-event))))

(verify-guards fn-ccar-completion-enabledp
  :hints (("Goal" :in-theory (union-theories
                              '(fn-ccar-core-enabled-finds-a-store-event
                                fn-ccar-cpe-projection-step-is-a-cons)
                              (theory 'ground-zero)))))

(in-theory (disable fn-ccar-completion-enabledp))

; fn-sn-finish's enabled branch with the carried record and kind.  The gate
; is its caller's: the guard says it holds, so it is not evaluated again.
(defun fn-ccar-sn-finish-enabled (s)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-ccar-completion-enabledp s))
                  :verify-guards nil))
  (let* ((record (fn-ccar-completion-record s))
         (retentionp (fn-evc-retentionp record))
         (consumerp (fn-evc-consumerp record))
         (topicp (fn-evc-topicp record))
         (identityp (or (fn-evc-stxep record) (fn-evc-stxkp record)
                        (fn-evc-stxap record)))
         (sequence (fn-evc-sequence record))
         (txid (fn-evc-txid record))
         (projection (fn-ccar-cpe-projection-step
                      (fn-sn-consumer s) record (fn-sn-identity-next s)))
         (topic-projection (fn-ccar-th-prefix-step (fn-sn-topic s) record))
         (node (cond (retentionp
                      (fn-replay-apply-retention-event (fn-sn-node s) record))
                     ((or identityp consumerp topicp)
                      (fn-replay-apply-record (fn-sn-node s) record))
                     (t
                      (fn-node-complete (fn-sn-node s) (fn-record-txid record)
                                        (fn-record-generation record) :durable))))
         (files (fn-sf-core-completion (fn-sn-files s) sequence txid)))
    (fn-sn-with-topic
     (fn-sn-with-consumer
      (if (or retentionp consumerp topicp)
          (fn-sn-advance-identity-next
           (fn-sn-update-indexed
            s (fn-sf-emit-success files sequence txid)
            node (fn-sn-index s)))
        (if identityp
            (fn-sn-finish-identity
             s (fn-sf-emit-success files sequence txid)
             record node)
          (fn-sn-advance-identity-next
           (fn-sn-update-accepted
            s (fn-sf-emit-success files sequence txid)
            node
            (fn-stx-index-add (fn-sn-index s) (fn-sn-accepted-delta s))
            (fn-record-msgid record)
            (fn-stx-verdict-of-octets
             (fn-record-payload record)
             (fn-sn-keyring s) (fn-sn-keyring-generation s))))))
      (fn-cp-nth 1 projection))
     topic-projection)))

(defun fn-ccar-sn-finish (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (fn-ccar-completion-enabledp s)
      (fn-ccar-sn-finish-enabled s)
    s))

(defthm fn-ccar-sn-finish-is-sn-finish
  (equal (fn-ccar-sn-finish s) (fn-sn-finish s))
  :hints (("Goal" :cases ((fn-sn-statep s))
           :in-theory (union-theories
                       '(fn-ccar-sn-finish fn-ccar-sn-finish-enabled fn-sn-finish
                         fn-evc-carried-definitions
                         fn-ccar-completion-enabledp-is-reference
                         fn-ccar-completion-record-is-completion-record
                         fn-ccar-cpe-projection-step-is-cpe-projection-step
                         fn-ccar-th-prefix-step-is-th-prefix-step)
                       (theory 'minimal-theory))
           :use ((:instance fn-sn-completion-enabledp)
                 (:instance fn-sn-completion-core-enabledp)))))

(verify-guards fn-ccar-sn-finish-enabled
  :hints (("Goal" :use ((:guard-theorem fn-sn-finish)
                        (:instance fn-ccar-enabled-finds-a-store-event))
           :in-theory
           (e/d (fn-sn-statep fn-evc-carried-definitions
                 fn-ccar-completion-enabledp-is-reference
                 fn-ccar-completion-record-is-completion-record)
                (fn-sf-statep fn-node-statep fn-sn-completion-record
                 fn-node-pending-matchesp fn-sn-pending-record
                 fn-sn-prepare-node fn-sf-core-completion
                 fn-sn-accepted-delta fn-store-event-p
                 fn-sn-completion-enabledp fn-sn-record-bindsp
                 fn-sn-identity-context fn-replay-identity-step
                 fn-replay-apply-retention-event fn-replay-apply-record
                 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-record-record-vocabulary fn-record-shape-vocabulary)))))

(verify-guards fn-ccar-sn-finish)

(in-theory (disable fn-ccar-sn-finish-enabled fn-ccar-sn-finish))

; -----------------------------------------------------------------------------
; The owner's completion and commit (books/owner.lisp fn-own-complete,
; books/owner-served-invariants.lisp fn-own-finish), carried, with the gate
; evaluated once.

(defun fn-ccar-own-complete-enabled (o)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store o))
                              (fn-ccar-completion-enabledp (fn-own-store o)))))
  (let ((s (fn-own-store o)))
    (fn-own-refresh
     (fn-own-make (fn-ccar-sn-finish-enabled s) (fn-own-view o) (fn-own-conns o)
                  (fn-own-next-id o) (fn-own-max-conns o) nil
                  (fn-ag-append (fn-own-ledger o)
                                (list (fn-sf-completion (fn-sn-files s))))
                  (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                  (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)))))

(defun fn-ccar-own-complete (o)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (if (fn-ccar-completion-enabledp (fn-own-store o))
      (fn-ccar-own-complete-enabled o)
    o))

(defthm fn-ccar-own-complete-is-own-complete
  (equal (fn-ccar-own-complete o) (fn-own-complete o))
  :hints (("Goal" :use ((:instance fn-ccar-sn-finish-is-sn-finish
                                   (s (fn-own-store o))))
           :in-theory (e/d (fn-ccar-own-complete fn-ccar-own-complete-enabled
                            fn-own-complete fn-ccar-sn-finish
                            fn-ccar-completion-enabledp-is-reference)
                           (fn-sn-statep fn-sn-finish fn-ccar-sn-finish-is-sn-finish
                            fn-sn-completion-enabledp fn-own-refresh)))))

(defun fn-ccar-completion-names-submission-p (o cfg)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))
                  :guard-hints
                  (("Goal" :in-theory
                    (disable fn-ccar-completion-record-is-completion-record)))))
  (let ((sub (fn-own-inflight o))
        (record (fn-ccar-completion-record (fn-own-store o))))
    (and sub
         record
         (fn-evc-recordp record)
         (equal (fn-record-msgid record)
                (fn-record-octets-string (fn-own-sub-msgid sub)))
         (equal (fn-record-payload record) (fn-own-sub-stored-octets cfg sub))
         t)))

(defthm fn-ccar-completion-names-submission-p-is-reference
  (implies (fn-sn-statep (fn-own-store o))
           (equal (fn-ccar-completion-names-submission-p o cfg)
                  (fn-own-completion-names-submission-p o cfg)))
  :hints (("Goal" :in-theory (e/d (fn-ccar-completion-names-submission-p
                                   fn-own-completion-names-submission-p
                                   fn-evc-carried-definitions)
                                  (fn-sn-statep fn-sn-completion-record
                                   fn-record-p)))))

; The function host/owner-host.lisp fn-owner-finish-submission calls.  The
; gate is evaluated once; the record is found at its sequence position and
; its kind and fields are read by shape (books/store-events-carried.lisp).
(defun fn-ccar-own-finish (o cfg)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (if (fn-ccar-completion-enabledp (fn-own-store o))
      (cons (if (fn-ccar-completion-names-submission-p o cfg) :durable :fault)
            (fn-ccar-own-complete-enabled o))
    (cons :fault o)))

; The completion gate is closed off the premise (its core conjoins
; fn-sn-statep in the logic).  Stated so the keystone below needs neither
; gate opened: with them open that proof took 208 s.
(defthm fn-ccar-completion-enabled-implies-statep
  (implies (fn-sn-completion-enabledp s) (fn-sn-statep s))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory '(fn-sn-completion-enabledp
                               fn-sn-completion-core-enabledp))))

; The reference completion, split at its gate.
(local
 (defthm fn-ccar-own-complete-split-at-its-gate
   (equal (fn-own-complete o)
          (if (fn-sn-completion-enabledp (fn-own-store o))
              (fn-ccar-own-complete-enabled o)
            o))
   :hints (("Goal" :use fn-ccar-own-complete-is-own-complete
            :in-theory (union-theories
                        '(fn-ccar-own-complete
                          fn-ccar-completion-enabledp-is-reference)
                        (theory 'ground-zero))))))

; KEYSTONE for the host line: the carried commit is the reference commit,
; word and owner, for every owner and every configuration.  No hypothesis:
; both completion gates conjoin (mbe :logic (fn-sn-statep s) :exec t), so
; off the premise both refuse in the logic, and on it the record found is
; the same.  What the premise buys is the executed code: the raw function
; drops that conjunct, runs the seek and reads the record by shape, and
; guard verification (the guard is fn-own-finish's own, fn-sn-statep of the
; store) is what equates the raw function with this logical one on every
; owner whose store satisfies it.
(defthm fn-ccar-own-finish-is-own-finish
  (equal (fn-ccar-own-finish o cfg) (fn-own-finish o cfg))
  :hints (("Goal" :in-theory '(fn-ccar-own-finish fn-own-finish
                               fn-ccar-own-complete-split-at-its-gate
                               fn-ccar-completion-enabledp-is-reference
                               fn-ccar-completion-names-submission-p-is-reference
                               fn-ccar-completion-enabled-implies-statep))))

(in-theory (disable fn-ccar-own-complete-enabled fn-ccar-own-complete
                    fn-ccar-completion-names-submission-p fn-ccar-own-finish))
(local (in-theory (disable fn-ccar-own-complete-split-at-its-gate)))

; -----------------------------------------------------------------------------
; The completion host/owner-host.lisp fn-owner-finish installs: the
; configured owner's (:complete) (books/owner-config.lisp fn-ocfg-complete),
; with the owner's completion carried.  A staged configuration record is
; published as before; otherwise the owner completes through
; fn-ccar-own-complete.  Identity, retention, consumer and topic events are
; completed here; before, the host reached them through fn-ocfg-step, whose
; guards are not verified.

(defun fn-ccar-ocfg-complete (oc)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (let ((record (fn-ocfg-staged oc)))
    (if record
        (fn-ocfg-make
         (fn-ocfg-owner oc)
         (fn-ocfg-published-config (fn-ocfg-config oc) record)
         (fn-ocfg-pins oc) nil)
      (fn-ocfg-make (fn-ccar-own-complete (fn-ocfg-owner oc))
                    (fn-ocfg-config oc) (fn-ocfg-pins oc) nil))))

; KEYSTONE for the host line: equal to the owner event the host used to
; issue, for every configured owner.  No hypothesis.
(defthm fn-ccar-ocfg-complete-is-ocfg-step-complete
  (equal (fn-ccar-ocfg-complete oc) (fn-ocfg-step oc '(:complete)))
  :hints (("Goal" :in-theory '(fn-ccar-ocfg-complete fn-ocfg-step
                               fn-ocfg-complete
                               fn-ccar-own-complete-is-own-complete
                               (:executable-counterpart car)))))

(in-theory (disable fn-ccar-ocfg-complete))

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
