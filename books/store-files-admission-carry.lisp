; Additive durable replay-prefix carry. No public allocation authority.
; PREFIX-NODE is the node produced by durable history replay, distinct from
; the live node with reservation/staging effects. No history walk in these
; candidate/one-produced-node consumers. Correspondence is proof-only.
(in-package "ACL2")
(include-book "store-files")

(defun fn-sfa-candidatep (record count lower frontier)
 (declare (xargs :guard t))
 (and (fn-store-event-p record)
      (equal (fn-store-event-sequence record) count)
      (equal (1+ (fn-store-event-txid record)) frontier)
      (<= (nfix lower) (fn-store-event-txid record))
      (equal (fn-store-event-generation record) (fn-store-event-txid record))))

(local (defthm fn-sfa-valid-history-lower-is-natural
 (implies (and (fn-sf-record-valuesp records) (natp lower))
  (natp (fn-sf-next-lower records lower)))
 :hints (("Goal" :induct (fn-sf-next-lower records lower)
  :in-theory (enable fn-sf-next-lower fn-sf-record-valuesp)))))

(defthm fn-sfa-candidate-consumes-exact-carried-coordinates
 (implies (and (fn-sf-record-valuesp records)
               (equal count (len records))
               (equal lower (fn-sf-next-lower records 0)))
  (equal (fn-sfa-candidatep record count lower frontier)
         (fn-sf-candidatep record records frontier)))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn-sfa-valid-history-lower-is-natural (lower 0))
  :in-theory (e/d (fn-sfa-candidatep fn-sf-candidatep) (fn-sf-next-lower fn-sf-record-valuesp)))))

(defun fn-sfa-append-from-produced (prefix-node count record next-node)
 (declare (xargs :guard t))
 (cond ((not (fn-store-event-p record))
        (fn-replay-fault prefix-node count :invalid-record))
       ((not (equal (fn-store-event-sequence record) count))
        (fn-replay-fault prefix-node count :sequence))
       ((not (consp next-node))
        (fn-replay-fault prefix-node count :node-refusal))
       (t (fn-replay-ok next-node (1+ count)))))

(defthm fn-sfa-produced-node-is-actual-single-record-replay
 (implies (and (fn-node-statep prefix-node)
               (equal next-node (fn-replay-apply-record prefix-node record)))
  (equal (fn-sfa-append-from-produced prefix-node count record next-node)
         (fn-replay-loop prefix-node (list record) count)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-replay-apply-record-statep-iff-consp
          (node prefix-node)))
  :in-theory (e/d (fn-sfa-append-from-produced fn-replay-loop)
    (fn-node-statep fn-replay-apply-record fn-store-event-p
     fn-replay-ok fn-replay-fault)))))

(local (defthm fn-sfa-loop-prefix-composition
 (implies (and (true-listp records) (fn-node-statep node) (natp count))
  (equal (fn-replay-loop node (append records suffix) count)
   (let ((prefix (fn-replay-loop node records count)))
    (if (fn-replay-okp prefix)
     (fn-replay-loop (fn-replay-result-node prefix) suffix
                     (fn-replay-result-sequence prefix))
     prefix))))
 :hints (("Goal" :induct (fn-replay-loop node records count)
  :in-theory (e/d (fn-replay-loop fn-replay-okp fn-replay-ok-shapep
                   fn-replay-result-kind fn-replay-result-node
                   fn-replay-result-sequence fn-replay-ok fn-replay-fault)
                  (fn-node-statep fn-replay-apply-record fn-store-event-p))))))

(local (defthm fn-sfa-ok-loop-has-proper-records
 (implies (fn-replay-okp (fn-replay-loop node records count)) (true-listp records))
 :hints (("Goal" :induct (fn-replay-loop node records count)
  :in-theory (e/d (fn-replay-loop fn-replay-okp fn-replay-ok-shapep
                  fn-replay-result-kind fn-replay-ok fn-replay-fault)
    (fn-node-statep fn-replay-apply-record fn-store-event-p))))) )
(local (defthm fn-sfa-ok-prefix-has-proper-records
 (implies (fn-replay-okp (fn-replay groups capacity records)) (true-listp records))
 :hints (("Goal"
  :use (:instance fn-sfa-ok-loop-has-proper-records
         (node (fn-node-initial-state groups capacity)) (count 0))
  :in-theory (e/d (fn-replay fn-replay-okp)
   (fn-sfa-ok-loop-has-proper-records fn-replay-loop fn-node-initial-state
    fn-node-statep fn-replay-fault true-listp))))))

(local (defthm fn-sfa-ok-prefix-has-typed-node-and-count
 (implies (fn-replay-okp prefix)
  (and (fn-node-statep (fn-replay-result-node prefix))
       (natp (fn-replay-result-sequence prefix))))
 :hints (("Goal" :in-theory (enable fn-replay-okp)))))
(local (defthm fn-sfa-ok-prefix-has-valid-initial-node
 (implies (fn-replay-okp (fn-replay groups capacity records))
  (fn-node-statep (fn-node-initial-state groups capacity)))
 :hints (("Goal" :in-theory (e/d (fn-replay fn-replay-okp)
  (fn-replay-loop fn-node-initial-state fn-node-statep fn-replay-fault))))))
(local (defthm fn-sfa-valid-initial-replay-is-loop
 (implies (fn-node-statep (fn-node-initial-state groups capacity))
  (equal (fn-replay groups capacity records)
         (fn-replay-loop (fn-node-initial-state groups capacity) records 0)))
 :hints (("Goal" :in-theory (enable fn-replay)))))

(defthm fn-sfa-exact-prefix-and-produced-node-equal-actual-append
 (implies (and (equal prefix (fn-replay groups capacity records))
               (fn-replay-okp prefix)
               (equal next-node
                (fn-replay-apply-record (fn-replay-result-node prefix) record)))
  (equal (fn-sfa-append-from-produced
           (fn-replay-result-node prefix) (fn-replay-result-sequence prefix)
           record next-node)
         (fn-replay groups capacity (append records (list record)))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-sfa-ok-prefix-has-proper-records
        fn-sfa-ok-prefix-has-typed-node-and-count
        fn-sfa-ok-prefix-has-valid-initial-node
        fn-sfa-valid-initial-replay-is-loop
        (:instance fn-sfa-valid-initial-replay-is-loop (records (append records (list record))))
        (:instance fn-sfa-produced-node-is-actual-single-record-replay
         (prefix-node (fn-replay-result-node prefix))
         (count (fn-replay-result-sequence prefix)))
        (:instance fn-sfa-loop-prefix-composition
         (node (fn-node-initial-state groups capacity)) (count 0)
         (suffix (list record))))
  :in-theory (disable fn-replay fn-replay-okp fn-replay-ok-shapep
   fn-replay-result-node fn-replay-result-kind fn-replay-result-sequence
   fn-sfa-append-from-produced fn-replay-loop fn-node-initial-state
   fn-node-statep fn-replay-apply-record fn-sfa-loop-prefix-composition
   fn-sfa-ok-prefix-has-typed-node-and-count fn-sfa-ok-prefix-has-valid-initial-node
   fn-sfa-valid-initial-replay-is-loop fn-sfa-ok-prefix-has-proper-records append))))

(defun fn-sfa-node-can-advancep (node frontier)
 (declare (xargs :guard t))
 (and (consp node) (natp frontier)
      (null (fn-node-stage node))
      (null (fn-state-pending (fn-node-acceptance node)))
      (equal (fn-state-fenced (fn-node-acceptance node)) nil)
      (natp (fn-state-next-txid (fn-node-acceptance node)))
      (<= (fn-state-next-txid (fn-node-acceptance node)) frontier)))
(defthm fn-sfa-carried-node-frontier-check-is-actual
 (implies (fn-node-statep node)
  (equal (fn-sfa-node-can-advancep node frontier)
         (fn-replay-advance-okp node frontier)))
 :hints (("Goal" :in-theory
  (e/d (fn-sfa-node-can-advancep fn-replay-advance-okp fn-node-statep fn-statep)
       (fn-node-stage fn-node-acceptance fn-state-pending
        fn-state-fenced fn-state-next-txid)))))

(local (defthm fn-sfa-history-recovery-is-prefix-and-frontier
 (equal (fn-sf-history-recoverablep groups capacity records frontier)
  (let ((answer (fn-replay groups capacity records)))
   (and (fn-replay-okp answer)
        (fn-replay-advance-okp (fn-replay-result-node answer) frontier))))
 :hints (("Goal"
  :use ((:instance fn-replay-advance-preserves-node-statep
          (node (fn-replay-result-node (fn-replay groups capacity records)))
          (recorded-txid frontier))
        (:instance fn-replay-advance-reconstructs-recorded-txid
          (node (fn-replay-result-node (fn-replay groups capacity records)))
          (recorded-txid frontier)))
  :in-theory (e/d (fn-sf-history-recoverablep fn-sf-replay-node fn-replay-okp)
    (fn-node-statep fn-replay fn-replay-advance-okp fn-replay-advance-txid
     fn-replay-result-node fn-replay-result-kind fn-replay-result-sequence))))) )

(defun fn-sfa-recoverable-from-produced (prefix-node count record next-node frontier)
 (declare (xargs :guard t) (ignore prefix-node))
 (and (fn-store-event-p record)
      (equal (fn-store-event-sequence record) count)
      (fn-sfa-node-can-advancep next-node frontier)))

(defthm fn-sfa-exact-prefix-and-produced-node-decide-actual-recoverability
 (implies (and (equal prefix (fn-replay groups capacity records))
               (fn-replay-okp prefix)
               (equal next-node
                (fn-replay-apply-record (fn-replay-result-node prefix) record)))
  (equal (fn-sfa-recoverable-from-produced
           (fn-replay-result-node prefix) (fn-replay-result-sequence prefix)
           record next-node frontier)
         (fn-sf-history-recoverablep groups capacity (append records (list record)) frontier)))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-sfa-exact-prefix-and-produced-node-equal-actual-append
        (:instance fn-sfa-history-recovery-is-prefix-and-frontier
          (records (append records (list record))))
        (:instance fn-replay-apply-record-statep-iff-consp
          (node (fn-replay-result-node prefix)))
        (:instance fn-sfa-carried-node-frontier-check-is-actual (node next-node)))
  :in-theory (e/d (fn-sfa-recoverable-from-produced fn-sfa-append-from-produced
                    fn-replay-okp fn-replay-ok fn-replay-fault fn-replay-ok-shapep
                    fn-replay-result-node fn-replay-result-kind fn-replay-result-sequence
                    fn-sfa-node-can-advancep fn-replay-advance-okp)
    (fn-node-statep fn-replay fn-sf-history-recoverablep fn-replay-apply-record
     fn-store-event-p fn-sfa-history-recovery-is-prefix-and-frontier)))))

(local (defthm fn-sfa-ok-loop-has-exact-count
 (implies (fn-replay-okp (fn-replay-loop node records count))
  (equal (fn-replay-result-sequence (fn-replay-loop node records count))
         (+ count (len records))))
 :hints (("Goal" :induct (fn-replay-loop node records count)
  :in-theory (e/d (fn-replay-loop fn-replay-okp fn-replay-ok-shapep
                    fn-replay-result-kind fn-replay-result-node
                    fn-replay-result-sequence fn-replay-ok fn-replay-fault)
    (fn-node-statep fn-replay-apply-record fn-store-event-p))))))
(local (defthm fn-sfa-ok-prefix-count-is-history-count
 (implies (fn-replay-okp (fn-replay groups capacity records))
  (equal (fn-replay-result-sequence (fn-replay groups capacity records)) (len records)))
 :hints (("Goal"
  :use (:instance fn-sfa-ok-loop-has-exact-count
         (node (fn-node-initial-state groups capacity)) (count 0))
  :in-theory (e/d (fn-replay fn-replay-okp)
    (fn-replay-loop fn-node-initial-state fn-node-statep fn-replay-fault
     fn-replay-result-sequence fn-sfa-ok-loop-has-exact-count))))))
(local (defthm fn-sfa-record-list-carries-values
 (implies (fn-sf-record-listp records sequence lower frontier)
          (fn-sf-record-valuesp records))
 :hints (("Goal" :induct (fn-sf-record-listp records sequence lower frontier)
  :in-theory (enable fn-sf-record-listp fn-sf-record-valuesp)))))

(defun fn-sfa-prepare-from-produced (s record lower prefix-node next-node)
 (declare (xargs :guard (fn-sf-statep s)))
 (if (and (mbe :logic (fn-sf-statep s) :exec t)
          (equal (fn-sf-phase s) :reserved)
          (fn-sfa-candidatep record (fn-sf-records-count s) lower (fn-sf-frontier s))
          (fn-sfa-recoverable-from-produced prefix-node (fn-sf-records-count s)
                                           record next-node (fn-sf-frontier s)))
  (fn-sf-remake :record-staged (fn-sf-frontier s) nil record nil (fn-sf-barriers s) s)
  s))

(defthm fn-sfa-carried-prepare-preserves-complete-file-machine-result
 (implies (and (equal prefix (fn-replay groups capacity (fn-sf-records s)))
               (fn-replay-okp prefix)
               (equal lower (fn-sf-next-lower (fn-sf-records s) 0))
               (equal prefix-node (fn-replay-result-node prefix))
               (equal next-node (fn-replay-apply-record prefix-node record)))
  (equal (fn-sfa-prepare-from-produced s record lower prefix-node next-node)
         (fn-sf-prepare-record s record groups capacity)))
 :rule-classes nil
 :hints (("Goal"
  :cases ((fn-sf-statep s))
  :use ((:instance fn-sfa-candidate-consumes-exact-carried-coordinates
          (records (fn-sf-records s)) (count (fn-sf-records-count s))
          (frontier (fn-sf-frontier s)))
        (:instance fn-sfa-exact-prefix-and-produced-node-decide-actual-recoverability
          (records (fn-sf-records s)) (frontier (fn-sf-frontier s)))
        (:instance fn-sfa-ok-prefix-count-is-history-count (records (fn-sf-records s)))
        (:instance fn-sfa-record-list-carries-values
          (records (fn-sf-records s)) (sequence 0) (lower 0) (frontier (fn-sf-frontier s))))
  :in-theory (e/d (fn-sfa-prepare-from-produced fn-sf-prepare-record fn-sf-statep
                   fn-sf-records-count)
    (fn-sfa-candidatep fn-sf-candidatep fn-sfa-recoverable-from-produced
     fn-sf-history-recoverablep fn-replay fn-replay-okp fn-sf-records
     fn-sf-record-listp fn-sf-record-valuesp fn-sf-next-lower fn-sf-make-fields
     fn-sfa-ok-prefix-count-is-history-count fn-sfa-record-list-carries-values
     fn-sfa-history-recovery-is-prefix-and-frontier fn-sfa-loop-prefix-composition
     fn-sfa-valid-initial-replay-is-loop fn-sfa-ok-prefix-has-valid-initial-node
     fn-sfa-ok-prefix-has-proper-records fn-sfa-ok-loop-has-exact-count)))))
