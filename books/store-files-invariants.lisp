; General safety properties for the immutable-file storage kernel.
;
; These theorems concern one executable kernel step and its abstract crash
; choices.  They do not prove reachability, raw file parsing, POSIX refinement,
; arbitrary-trace acknowledgement retention, or platform durability.

(in-package "ACL2")
(include-book "store-files")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Ordered record-list lemmas used by crash and publication preservation.

(defun fn-sf-prefixp (xs ys)
  (if (consp xs)
      (and (consp ys)
           (equal (car xs) (car ys))
           (fn-sf-prefixp (cdr xs) (cdr ys)))
    (null xs)))

(defthm fn-sf-prefixp-reflexive
  (implies (true-listp xs)
           (fn-sf-prefixp xs xs))
  :hints (("Goal" :induct (fn-sf-prefixp xs xs))))

(defthm fn-sf-prefixp-append
  (implies (true-listp xs)
           (fn-sf-prefixp xs (append xs ys)))
  :hints (("Goal" :induct (fn-sf-prefixp xs xs))))

(defthm fn-sf-record-listp-is-true-list
  (implies (fn-sf-record-listp records sequence lower frontier)
           (true-listp records))
  :rule-classes :forward-chaining)

(defthm fn-sf-record-listp-frontier-monotone
  (implies (and (fn-sf-record-listp records sequence lower old-frontier)
                (natp new-frontier)
                (<= old-frontier new-frontier))
           (fn-sf-record-listp records sequence lower new-frontier))
  :hints (("Goal" :induct
           (fn-sf-record-listp records sequence lower old-frontier))))

(defthm fn-sf-record-listp-append-one-general
  (implies
   (and (fn-sf-record-listp records sequence lower frontier)
        (natp sequence) (natp lower) (natp frontier)
        (fn-record-p record)
        (equal (fn-record-sequence record) (+ sequence (len records)))
        (<= (fn-sf-next-lower records lower) (fn-record-txid record))
        (< (fn-record-txid record) frontier)
        (equal (fn-record-generation record) (fn-record-txid record)))
   (fn-sf-record-listp (append records (list record))
                       sequence lower frontier))
  :hints (("Goal" :induct
           (fn-sf-record-listp records sequence lower frontier))))

(defthm fn-sf-candidate-append-preserves-record-list
  (implies (and (fn-sf-record-listp records 0 0 frontier)
                (fn-sf-candidatep record records frontier))
           (fn-sf-record-listp (append records (list record))
                               0 0 frontier))
  :hints (("Goal"
           :use ((:instance fn-sf-record-listp-append-one-general
                            (sequence 0) (lower 0))))))

(defthm fn-sf-record-pair-present-after-append
  (fn-sf-record-has-pairp
   (fn-sf-record-pair record)
   (append records (list record)))
  :hints (("Goal" :induct (len records))))

(defthm fn-sf-record-pair-preserved-by-append
  (implies (fn-sf-record-has-pairp pair records)
           (fn-sf-record-has-pairp pair (append records tail)))
  :hints (("Goal" :induct (fn-sf-record-has-pairp pair records))))

(defthm fn-sf-success-list-preserved-by-append
  (implies (fn-sf-success-listp successes records)
           (fn-sf-success-listp successes (append records tail)))
  :hints (("Goal" :induct (fn-sf-success-listp successes records))))

(defthm fn-sf-success-list-append-covered-pair
  (implies (and (fn-sf-success-listp successes records)
                (fn-sf-pairp pair)
                (fn-sf-record-has-pairp pair records))
           (fn-sf-success-listp (append successes (list pair)) records))
  :hints (("Goal" :induct (fn-sf-success-listp successes records))))

; -----------------------------------------------------------------------------
; One-crash preservation.  Stable records are never removed or replaced.

(defthm fn-sf-stable-records-prefix-of-crash
  (implies (and (fn-sf-statep s)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (fn-sf-prefixp
            (fn-sf-records s)
            (fn-sf-records
             (fn-sf-crash s frontier-choice record-choice))))
  :hints (("Goal"
           :in-theory (enable fn-sf-crash))))

(defthm fn-sf-surviving-candidate-is-exact-and-dominated
  (implies (and (fn-sf-statep s)
                (fn-sf-crash-choicep frontier-choice :present)
                (fn-sf-record-present-visiblep s))
           (let ((crashed (fn-sf-crash s frontier-choice :present)))
             (and (equal (fn-sf-records crashed)
                         (append (fn-sf-records s)
                                 (list (fn-sf-record-candidate s))))
                  (< (fn-record-txid (fn-sf-record-candidate s))
                     (fn-sf-frontier crashed)))))
  :hints (("Goal"
           :in-theory (enable fn-sf-crash
                              fn-sf-record-present-visiblep
                              fn-sf-frontier-new-visiblep
                              fn-sf-phase-shapep
                              fn-sf-record-phasep
                              fn-sf-frontier-phasep
                              fn-sf-completion-phasep))))

(defthm fn-sf-crash-preserves-state
  (implies (and (fn-sf-statep s)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (fn-sf-statep
            (fn-sf-crash s frontier-choice record-choice)))
  :hints (("Goal"
           :cases ((fn-sf-frontier-new-visiblep s)
                   (fn-sf-record-present-visiblep s))
           :in-theory (enable fn-sf-crash
                              fn-sf-statep fn-sf-phase-shapep
                              fn-sf-frontier-new-visiblep
                              fn-sf-record-present-visiblep
                              fn-sf-frontier-phasep
                              fn-sf-record-phasep
                              fn-sf-completion-phasep))))

(defthm fn-sf-successes-unchanged-by-crash
  (implies (and (fn-sf-statep s)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (equal (fn-sf-successes
                   (fn-sf-crash s frontier-choice record-choice))
                  (fn-sf-successes s)))
  :hints (("Goal" :in-theory (enable fn-sf-crash))))

(defthm fn-sf-success-member-has-record
  (implies (and (fn-sf-success-listp successes records)
                (member-equal pair successes))
           (fn-sf-record-has-pairp pair records))
  :hints (("Goal" :induct (fn-sf-success-listp successes records))))

(defthm fn-sf-state-success-member-has-record
  (implies (and (fn-sf-statep s)
                (member-equal pair (fn-sf-successes s)))
           (fn-sf-record-has-pairp pair (fn-sf-records s)))
  :hints (("Goal"
           :use ((:instance fn-sf-success-member-has-record
                            (successes (fn-sf-successes s))
                            (records (fn-sf-records s)))))))

; One crash step only: this is not an induction over arbitrary reachable traces
; and does not establish that real barriers implement the modeled crash choice.
(defthm fn-sf-prior-success-has-record-after-one-crash
  (implies (and (fn-sf-statep s)
                (fn-sf-crash-choicep frontier-choice record-choice)
                (member-equal pair (fn-sf-successes s)))
           (fn-sf-record-has-pairp
            pair
            (fn-sf-records
             (fn-sf-crash s frontier-choice record-choice))))
  :hints (("Goal"
           :use ((:instance fn-sf-crash-preserves-state)
                 (:instance fn-sf-successes-unchanged-by-crash)
                 (:instance fn-sf-state-success-member-has-record
                            (s (fn-sf-crash s frontier-choice record-choice))))
           :in-theory
           (disable fn-sf-statep fn-sf-crash
                    fn-sf-successes fn-sf-records
                    fn-sf-success-listp fn-sf-record-has-pairp))))

; -----------------------------------------------------------------------------
; Selected non-crash transition preservation.

(defthm fn-sf-frontier-file-result-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-frontier-file-result s result))))

(defthm fn-sf-frontier-replace-result-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-frontier-replace-result s result))))

(defthm fn-sf-frontier-dir-result-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-frontier-dir-result s result)))
  :hints (("Goal"
           :use ((:instance fn-sf-record-listp-frontier-monotone
                            (records (fn-sf-records s))
                            (sequence 0) (lower 0)
                            (old-frontier (fn-sf-frontier s))
                            (new-frontier
                             (fn-sf-frontier-candidate s)))))))

(defthm fn-sf-refuse-reservation-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-refuse-reservation s txid result))))

(defthm fn-sf-prepare-record-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep
            (fn-sf-prepare-record s record groups capacity)))
  :hints (("Goal"
           :in-theory (disable fn-sf-history-recoverablep
                               fn-sf-replay-node))))

(defthm fn-sf-record-file-result-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-record-file-result s result))))

(defthm fn-sf-prepublish-abort-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-prepublish-abort s))))

(defthm fn-sf-abort-completion-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep
            (fn-sf-abort-completion s sequence txid result))))

(defthm fn-sf-record-link-result-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-record-link-result s result))))

(defthm fn-sf-record-dir-result-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-record-dir-result s result)))
  :hints (("Goal"
           :use ((:instance fn-sf-record-pair-present-after-append
                            (records (fn-sf-records s))
                            (record (fn-sf-record-candidate s))))
           :in-theory (disable fn-sf-record-pair-present-after-append))))

(defthm fn-sf-core-completion-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep
            (fn-sf-core-completion s sequence txid result))))

(defthm fn-sf-emit-success-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-emit-success s sequence txid)))
  :hints (("Goal"
           :use ((:instance fn-sf-success-list-append-covered-pair
                            (successes (fn-sf-successes s))
                            (records (fn-sf-records s))
                            (pair (fn-sf-completion s))))
           :in-theory (disable fn-sf-success-list-append-covered-pair))))

(defthm fn-sf-lose-success-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-lose-success s sequence txid))))

(defthm fn-sf-recover-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-recover s groups capacity)))
  :hints (("Goal"
           :in-theory (disable fn-sf-history-recoverablep
                               fn-sf-replay-node))))

(defthm fn-sf-recovery-barrier-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-recovery-barrier s result))))
