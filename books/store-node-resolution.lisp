; fn: synchronous refusal and known prepublication abort for the live store.
(in-package "ACL2")
(include-book "store-node-traces")

; A semantic refusal consumes the durable file reservation and advances the
; actual idle node over the same txid.  The host supplies only the reservation
; identity; it cannot supply either component's resolution result.
(defun fn-sn-refuse-reservation-enabledp (s txid)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sn-statep s)
       (equal (fn-sf-phase (fn-sn-files s)) :reserved)
       (natp txid)
       (equal (1+ txid) (fn-sf-frontier (fn-sn-files s)))
       (fn-replay-advance-okp
        (fn-sn-node s) (fn-sf-frontier (fn-sn-files s)))))

(verify-guards fn-sn-refuse-reservation-enabledp)

(defun fn-sn-refuse-reservation (s txid)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sn-refuse-reservation-enabledp s txid)
      (fn-sn-update
       s
       (fn-sf-refuse-reservation (fn-sn-files s) txid)
       (fn-replay-advance-txid
        (fn-sn-node s) (fn-sf-frontier (fn-sn-files s))))
    s))

(verify-guards fn-sn-refuse-reservation)

; Only a proposal whose immutable publication has not been attempted has a
; known-absent resolution.  Exact sequence, txid, generation, and record data
; come from the bound candidate rather than from a host completion claim.
(defun fn-sn-known-abort-enabledp (s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((files (fn-sn-files s)))
    (and (fn-sn-statep s)
         (or (equal (fn-sf-phase files) :record-staged)
             (equal (fn-sf-phase files) :record-data-durable))
         (fn-sn-record-bindsp
          (fn-sn-node s) (fn-sf-record-candidate files)))))

(verify-guards fn-sn-known-abort-enabledp)

(defun fn-sn-known-abort-file-start (files)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (fn-sf-phase files) :record-staged)
      (fn-sf-record-file-result files :known-fail)
    (fn-sf-prepublish-abort files)))

(verify-guards fn-sn-known-abort-file-start)

; The public known-abort gate establishes a valid record candidate before
; calling this helper; its guard requires only the proper-list representation.
(defun fn-sn-known-abort-files (files)
  (declare (xargs :guard (true-listp (fn-sf-record-candidate files)) :verify-guards nil))
  (let* ((record (fn-sf-record-candidate files))
         (aborting (fn-sn-known-abort-file-start files)))
    (fn-sf-abort-completion
     aborting (fn-record-sequence record) (fn-record-txid record))))

(verify-guards fn-sn-known-abort-files)

(defun fn-sn-known-abort (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sn-known-abort-enabledp s)
      (let* ((files (fn-sn-files s))
             (record (fn-sf-record-candidate files))
             (node (fn-node-complete
                    (fn-sn-node s) (fn-record-txid record)
                    (fn-record-generation record) :aborted)))
        (fn-sn-update s (fn-sn-known-abort-files files) node))
    s))

(verify-guards fn-sn-known-abort
  :hints (("Goal" :in-theory
           (disable fn-sn-statep fn-sf-statep fn-node-statep
                    fn-node-pending-matchesp fn-sn-pending-record))))

(local (in-theory
        (disable fn-sn-statep fn-sf-statep fn-node-statep fn-record-p
                 fn-sn-record-bindsp fn-snt-relation fn-snt-pending-linkp
                 fn-sf-history-recoverablep fn-sf-replay-node
                 fn-sn-refuse-reservation-enabledp fn-sn-refuse-reservation
                 fn-sn-known-abort-enabledp fn-sn-known-abort-file-start
                 fn-sn-known-abort-files fn-sn-known-abort
                 fn-sf-refuse-reservation
                 fn-sf-record-file-result fn-sf-prepublish-abort
                 fn-sf-abort-completion fn-replay-advance-txid
                 fn-node-complete fn-node-prepare fn-replay fn-replay-loop)))

(defthm fn-sn-refuse-reservation-disabled-is-no-op
  (implies (not (fn-sn-refuse-reservation-enabledp s txid))
           (equal (fn-sn-refuse-reservation s txid) s))
  :hints (("Goal" :in-theory (enable fn-sn-refuse-reservation))))

(defthm fn-sn-known-abort-disabled-is-no-op
  (implies (not (fn-sn-known-abort-enabledp s))
           (equal (fn-sn-known-abort s) s))
  :hints (("Goal" :in-theory (enable fn-sn-known-abort))))

(defthm fn-sn-refuse-reservation-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :cases ((fn-sn-refuse-reservation-enabledp s txid))
           :use ((:instance fn-sf-refuse-reservation-preserves-state
                            (s (fn-sn-files s)))
                 (:instance fn-replay-advance-preserves-node-statep
                            (node (fn-sn-node s))
                            (recorded-txid
                             (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (e/d (fn-sn-refuse-reservation fn-sn-update fn-sn-statep)
                           (fn-sf-refuse-reservation
                            fn-replay-advance-txid)))))

(defthm fn-sn-known-abort-file-start-preserves-state
  (implies (fn-sf-statep files)
           (fn-sf-statep (fn-sn-known-abort-file-start files)))
  :hints (("Goal"
           :in-theory (enable fn-sn-known-abort-file-start))))

(defthm fn-sn-known-abort-files-preserves-state
  (implies (fn-sf-statep files)
           (fn-sf-statep (fn-sn-known-abort-files files)))
  :hints (("Goal"
           :use ((:instance fn-sn-known-abort-file-start-preserves-state)
                 (:instance fn-sf-abort-completion-preserves-state
                            (s (fn-sn-known-abort-file-start files))
                            (sequence (fn-record-sequence
                                       (fn-sf-record-candidate files)))
                            (txid (fn-record-txid
                                   (fn-sf-record-candidate files)))))
           :in-theory (enable fn-sn-known-abort-files))))

(defthm fn-sn-known-abort-preserves-state
  (implies (fn-sn-statep s)
           (fn-sn-statep (fn-sn-known-abort s)))
  :hints (("Goal"
           :cases ((fn-sn-known-abort-enabledp s))
           :use ((:instance fn-sn-known-abort-files-preserves-state
                            (files (fn-sn-files s)))
                 (:instance fn-node-complete-preserves-state
                            (s (fn-sn-node s))
                            (txid (fn-record-txid
                                   (fn-sf-record-candidate (fn-sn-files s))))
                            (generation (fn-record-generation
                                         (fn-sf-record-candidate
                                          (fn-sn-files s))))
                            (completion-status :aborted)))
           :in-theory (e/d (fn-sn-known-abort fn-sn-update fn-sn-statep)
                           (fn-sn-record-bindsp
                            fn-sn-known-abort-files fn-node-complete)))))

(defthm fn-sn-refuse-reservation-preserves-configuration
  (and (equal (fn-sn-groups (fn-sn-refuse-reservation s txid))
              (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-sn-refuse-reservation s txid))
              (fn-sn-capacity s)))
  :hints (("Goal" :in-theory (enable fn-sn-refuse-reservation
                                      fn-sn-update))))

(defthm fn-sn-known-abort-preserves-configuration
  (and (equal (fn-sn-groups (fn-sn-known-abort s)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-sn-known-abort s)) (fn-sn-capacity s)))
  :hints (("Goal" :in-theory (enable fn-sn-known-abort fn-sn-update))))

(defthm fn-sn-refuse-reservation-cannot-acknowledge
  (equal (fn-sf-successes
          (fn-sn-files (fn-sn-refuse-reservation s txid)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal"
           :use ((:instance fn-sf-successes-of-refuse-reservation
                            (s (fn-sn-files s))))
           :in-theory (e/d (fn-sn-refuse-reservation fn-sn-update)
                           (fn-sf-refuse-reservation fn-sf-successes)))))

(defthm fn-sn-known-abort-file-start-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-known-abort-file-start files))
         (fn-sf-successes files))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-known-abort-file-start)
                           (fn-sf-record-file-result fn-sf-prepublish-abort
                            fn-sf-successes)))))

(defthm fn-sn-known-abort-cannot-acknowledge
  (equal (fn-sf-successes (fn-sn-files (fn-sn-known-abort s)))
         (fn-sf-successes (fn-sn-files s)))
  :hints (("Goal"
           :use ((:instance fn-sf-successes-of-abort-completion
                            (s (fn-sn-known-abort-file-start (fn-sn-files s)))
                            (sequence (fn-record-sequence
                                       (fn-sf-record-candidate (fn-sn-files s))))
                            (txid (fn-record-txid
                                   (fn-sf-record-candidate (fn-sn-files s))))))
           :in-theory (e/d (fn-sn-known-abort fn-sn-known-abort-files
                             fn-sn-update)
                           (fn-sn-known-abort-file-start
                            fn-sf-abort-completion fn-sf-successes)))))

(defthm fn-sn-known-abort-files-reaches-ready
  (implies (and (fn-sf-statep files)
                (or (equal (fn-sf-phase files) :record-staged)
                    (equal (fn-sf-phase files) :record-data-durable)))
           (equal (fn-sf-phase (fn-sn-known-abort-files files)) :ready))
  :hints (("Goal"
           :use ((:instance fn-sn-known-abort-file-start-preserves-state))
           :in-theory (enable fn-sn-known-abort-files
                              fn-sn-known-abort-file-start
                              fn-sf-record-file-result
                              fn-sf-prepublish-abort
                              fn-sf-abort-completion))))

(defthm fn-sn-refuse-reservation-is-exact-advance
  (implies (fn-sn-refuse-reservation-enabledp s txid)
           (and (equal (fn-sf-phase
                        (fn-sn-files (fn-sn-refuse-reservation s txid)))
                       :ready)
                (equal (fn-sn-node (fn-sn-refuse-reservation s txid))
                       (fn-replay-advance-txid
                        (fn-sn-node s) (fn-sf-frontier (fn-sn-files s))))
                (equal (fn-state-next-txid
                        (fn-node-acceptance
                         (fn-sn-node (fn-sn-refuse-reservation s txid))))
                       (fn-sf-frontier (fn-sn-files s)))))
  :hints (("Goal" :in-theory
           (enable fn-sn-refuse-reservation
                   fn-sn-refuse-reservation-enabledp fn-sn-update
                   fn-sf-refuse-reservation fn-replay-advance-txid))))

(defthm fn-sn-known-abort-is-exact-node-abort
  (implies (fn-sn-known-abort-enabledp s)
           (let ((record (fn-sf-record-candidate (fn-sn-files s))))
             (and (equal (fn-sf-phase
                          (fn-sn-files (fn-sn-known-abort s)))
                         :ready)
                  (equal (fn-sn-node (fn-sn-known-abort s))
                         (fn-node-complete
                          (fn-sn-node s) (fn-record-txid record)
                          (fn-record-generation record) :aborted)))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-known-abort
                             fn-sn-known-abort-enabledp fn-sn-update)
                           (fn-sn-known-abort-files fn-sf-phase
                            fn-node-complete)))))

(defthm fn-sn-refuse-reservation-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-refuse-reservation s txid)))
  :hints (("Goal"
           :cases ((fn-sn-refuse-reservation-enabledp s txid))
           :use (fn-sn-refuse-reservation-preserves-state
                 (:instance fn-snt-advance-replayed-node
                            (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s))
                            (records (fn-sf-records (fn-sn-files s)))
                            (first (1- (fn-sf-frontier (fn-sn-files s))))
                            (second (fn-sf-frontier (fn-sn-files s)))))
           :in-theory (e/d (fn-snt-relation fn-snt-idle-phasep
                             fn-sn-refuse-reservation
                             fn-sn-refuse-reservation-enabledp fn-sn-update
                             fn-sf-refuse-reservation)
                           (fn-sn-statep fn-sf-statep
                            fn-sf-history-recoverablep fn-sf-replay-node
                            fn-snt-pending-linkp fn-sn-completion-enabledp
                            fn-replay-advance-txid)))))

(defthm fn-sn-known-abort-preserves-relation
  (implies (fn-snt-relation s)
           (fn-snt-relation (fn-sn-known-abort s)))
  :hints (("Goal"
           :cases ((fn-sn-known-abort-enabledp s))
           :use (fn-sn-known-abort-preserves-state
                 fn-sn-known-abort-is-exact-node-abort)
           :in-theory (e/d (fn-snt-relation fn-snt-idle-phasep
                             fn-snt-pending-linkp
                             fn-sn-known-abort fn-sn-known-abort-enabledp
                             fn-sn-known-abort-files
                             fn-sn-known-abort-file-start fn-sn-update
                             fn-sf-record-file-result
                             fn-sf-prepublish-abort
                             fn-sf-abort-completion)
                            (fn-sn-statep fn-sf-statep
                             fn-sn-record-bindsp
                             fn-sf-history-recoverablep
                             fn-sf-replay-node fn-node-complete
                             fn-sn-completion-enabledp)))))
