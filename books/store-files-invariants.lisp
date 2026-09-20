; General safety properties for the immutable-file storage kernel.
;
; These theorems concern one executable kernel step and its abstract crash
; choices.  They do not prove reachability, raw file parsing, POSIX refinement,
; arbitrary-trace acknowledgement retention, or platform durability.

(in-package "ACL2")
(include-book "store-files")
(local (include-book "arithmetic/top" :dir :system))
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary)))

; The preservation keystones open the kernel definitions locally (docs/
; proof-style.md s2); the record stays opaque, so goals are in accessor
; vocabulary throughout.
(local (in-theory (enable fn-sf-statep fn-sf-phase-shapep fn-sf-initial-state
                          fn-sf-start-frontier fn-sf-frontier-file-result
                          fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                          fn-sf-refuse-reservation fn-sf-prepare-record
                          fn-sf-record-file-result fn-sf-prepublish-abort
                          fn-sf-abort-completion fn-sf-record-link-result
                          fn-sf-record-dir-result fn-sf-core-completion
                          fn-sf-emit-success fn-sf-lose-success
                          fn-sf-crash-imagep fn-sf-crash fn-sf-recover
                          fn-sf-recovery-barrier)))

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

; Whenever the present choice is live (from :record-data-durable, where the
; link may already have been issued, through the fenced link phase) the
; surviving record is exactly the data-durable candidate and its txid is
; below the frontier the image carries.
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
                     
                    fn-sf-success-listp fn-sf-record-has-pairp))))

; -----------------------------------------------------------------------------
; Crash-point fidelity.  Where a crash choice is genuine, where no choice
; exists yet, and where a completed barrier has already removed one.

; From :frontier-data-durable the replacement may or may not have been
; issued (crash point frontier-replace): both whole-file values are outcomes.
(defthm fn-sf-unobserved-frontier-replacement-crash-is-old-or-new
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :frontier-data-durable)
                (or (equal record-choice :absent)
                    (equal record-choice :present)))
           (and (equal (fn-sf-frontier (fn-sf-crash s :old record-choice))
                       (fn-sf-frontier s))
                (equal (fn-sf-frontier (fn-sf-crash s :new record-choice))
                       (fn-sf-frontier-candidate s))
                (equal (fn-sf-records (fn-sf-crash s :old record-choice))
                       (fn-sf-records s))
                (equal (fn-sf-records (fn-sf-crash s :new record-choice))
                       (fn-sf-records s))))
  :hints (("Goal" :in-theory (enable fn-sf-crash
                                     fn-sf-frontier-new-visiblep
                                     fn-sf-record-present-visiblep))))

; From :record-data-durable the link may or may not have been issued (crash
; point final-link): absence and the exact candidate are both outcomes.
(defthm fn-sf-unobserved-record-link-crash-is-absent-or-present
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :record-data-durable)
                (or (equal frontier-choice :old)
                    (equal frontier-choice :new)))
           (and (equal (fn-sf-records (fn-sf-crash s frontier-choice :absent))
                       (fn-sf-records s))
                (equal (fn-sf-records (fn-sf-crash s frontier-choice :present))
                       (append (fn-sf-records s)
                               (list (fn-sf-record-candidate s))))
                (equal (fn-sf-frontier (fn-sf-crash s frontier-choice :absent))
                       (fn-sf-frontier s))
                (equal (fn-sf-frontier (fn-sf-crash s frontier-choice :present))
                       (fn-sf-frontier s))))
  :hints (("Goal" :in-theory (enable fn-sf-crash
                                     fn-sf-frontier-new-visiblep
                                     fn-sf-record-present-visiblep))))

; Before any namespace syscall can have been issued, and after every barrier
; has completed, a crash leaves the image unchanged whatever choice is given.
(defthm fn-sf-crash-outside-namespace-window-keeps-image
  (implies (and (fn-sf-statep s)
                (not (fn-sf-frontier-new-visiblep s))
                (not (fn-sf-record-present-visiblep s)))
           (and (equal (fn-sf-frontier
                        (fn-sf-crash s frontier-choice record-choice))
                       (fn-sf-frontier s))
                (equal (fn-sf-records
                        (fn-sf-crash s frontier-choice record-choice))
                       (fn-sf-records s))))
  :hints (("Goal" :in-theory (enable fn-sf-crash))))

; A completed allocator directory barrier has moved the candidate into the
; stable frontier, so no later crash choice selects the old value.  The
; barrier step is the hypothesis; fn-sf-crash asserts nothing about it.
(defthm fn-sf-completed-frontier-barrier-removes-old-choice
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :frontier-attempted))
           (equal (fn-sf-frontier
                   (fn-sf-crash (fn-sf-frontier-dir-result s :ok)
                                frontier-choice record-choice))
                  (fn-sf-frontier-candidate s)))
  :hints (("Goal" :in-theory (enable fn-sf-crash fn-sf-frontier-dir-result
                                     fn-sf-frontier-new-visiblep
                                     fn-sf-record-present-visiblep))))

; A completed transaction directory barrier has appended the candidate to the
; stable records, so no later crash choice can make it absent.
(defthm fn-sf-completed-record-barrier-removes-absent-choice
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :record-attempted))
           (equal (fn-sf-records
                   (fn-sf-crash (fn-sf-record-dir-result s :ok)
                                frontier-choice record-choice))
                  (append (fn-sf-records s)
                          (list (fn-sf-record-candidate s)))))
  :hints (("Goal"
           :use ((:instance fn-sf-record-pair-present-after-append
                            (records (fn-sf-records s))
                            (record (fn-sf-record-candidate s))))
           :in-theory (e/d (fn-sf-crash fn-sf-record-dir-result
                                        fn-sf-frontier-new-visiblep
                                        fn-sf-record-present-visiblep)
                           (fn-sf-record-pair-present-after-append)))))

; -----------------------------------------------------------------------------
; The admissible-image premise and the constructor that inhabits it.

(defthm fn-sf-crash-image-is-admissible
  (implies (and (fn-sf-statep s)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (fn-sf-crash-imagep s
                               (fn-sf-frontier
                                (fn-sf-crash s frontier-choice record-choice))
                               (fn-sf-records
                                (fn-sf-crash s frontier-choice record-choice))))
  :hints (("Goal" :in-theory (enable fn-sf-crash fn-sf-crash-imagep))))

; The choice that reproduces a given admissible image.
(defun fn-sf-image-frontier-choice (s frontier)
  (if (equal frontier (fn-sf-frontier s)) :old :new))

(defun fn-sf-image-record-choice (s records)
  (if (equal records (fn-sf-records s)) :absent :present))

(defthm fn-sf-image-choices-are-choices
  (fn-sf-crash-choicep (fn-sf-image-frontier-choice s frontier)
                       (fn-sf-image-record-choice s records)))

(defthm fn-sf-crash-realizes-every-admissible-image
  (implies (fn-sf-crash-imagep s frontier records)
           (let ((crashed (fn-sf-crash s
                                       (fn-sf-image-frontier-choice s frontier)
                                       (fn-sf-image-record-choice s records))))
             (and (equal (fn-sf-frontier crashed) frontier)
                  (equal (fn-sf-records crashed) records)
                  (equal (fn-sf-phase crashed) :replaying)
                  (equal (fn-sf-successes crashed) (fn-sf-successes s)))))
  :hints (("Goal" :in-theory (enable fn-sf-crash fn-sf-crash-imagep))))

; Everything a reopen proof needs from an admissible image: the image is a
; valid frontier and record list, and every acknowledged pair of the pre-crash
; state names a record in it.
(defthm fn-sf-crash-imagep-implies-state
  (implies (fn-sf-crash-imagep s frontier records)
           (fn-sf-statep s))
  :hints (("Goal" :in-theory (e/d (fn-sf-crash-imagep) (fn-sf-statep)))))

(defthm fn-sf-state-image-components-typed
  (implies (fn-sf-statep s)
           (and (fn-record-uint32p (fn-sf-frontier s))
                (fn-sf-record-listp (fn-sf-records s) 0 0 (fn-sf-frontier s))
                (true-listp (fn-sf-records s))))
  :hints (("Goal"
           :use ((:instance fn-sf-record-listp-is-true-list
                            (records (fn-sf-records s)) (sequence 0) (lower 0)
                            (frontier (fn-sf-frontier s))))
           :in-theory (e/d (fn-sf-statep)
                           (fn-sf-phasep fn-sf-phase-shapep fn-sf-record-listp
                            fn-sf-success-listp  )))))

(defthm fn-sf-admissible-image-facts
  (implies (fn-sf-crash-imagep s frontier records)
           (and (fn-sf-statep s)
                (fn-record-uint32p frontier)
                (fn-sf-record-listp records 0 0 frontier)
                (true-listp records)
                (implies (member-equal pair (fn-sf-successes s))
                         (fn-sf-record-has-pairp pair records))))
  :hints (("Goal"
           :use (fn-sf-crash-imagep-implies-state
                 fn-sf-crash-realizes-every-admissible-image
                 (:instance fn-sf-crash-preserves-state
                            (frontier-choice
                             (fn-sf-image-frontier-choice s frontier))
                            (record-choice
                             (fn-sf-image-record-choice s records)))
                 (:instance fn-sf-prior-success-has-record-after-one-crash
                            (frontier-choice
                             (fn-sf-image-frontier-choice s frontier))
                            (record-choice
                             (fn-sf-image-record-choice s records)))
                 (:instance fn-sf-state-image-components-typed
                            (s (fn-sf-crash s
                                            (fn-sf-image-frontier-choice s frontier)
                                            (fn-sf-image-record-choice s records)))))
           :in-theory (disable fn-sf-statep fn-sf-crash fn-sf-crash-imagep
                               fn-sf-crash-choicep
                               fn-sf-image-frontier-choice
                               fn-sf-image-record-choice
                               fn-sf-record-listp fn-sf-success-listp
                               fn-sf-record-has-pairp
                                 
                               
                               fn-sf-crash-imagep-implies-state
                               fn-sf-crash-realizes-every-admissible-image
                               fn-sf-crash-preserves-state
                               fn-sf-prior-success-has-record-after-one-crash
                               fn-sf-state-image-components-typed))))

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
           (fn-sf-statep (fn-sf-refuse-reservation s txid))))

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
            (fn-sf-abort-completion s sequence txid))))

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
            (fn-sf-core-completion s sequence txid))))

(defthm fn-sf-emit-success-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-emit-success s sequence txid)))
  :hints (("Goal"
           :use ((:instance fn-sf-success-list-append-covered-pair
                            (successes (fn-sf-successes s))
                            (records (fn-sf-records s))
                            (pair (fn-sf-completion s))))
           :in-theory (disable fn-sf-success-list-append-covered-pair))))

; unreachable-in-composition: see fn-sf-lose-success in store-files.lisp.
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

; -----------------------------------------------------------------------------
; Export theory.  The ordered record-list and success-list lemmas are proof
; vocabulary; a book above re-enables them by this name.  The one-crash
; preservation, crash-point fidelity, admissible-image and transition
; preservation keystones stay enabled.
(deftheory fn-store-files-invariants-vocabulary
  '(fn-sf-prefixp-reflexive fn-sf-prefixp-append
    fn-sf-record-listp-is-true-list fn-sf-record-listp-frontier-monotone
    fn-sf-record-listp-append-one-general
    fn-sf-candidate-append-preserves-record-list
    fn-sf-record-pair-present-after-append fn-sf-record-pair-preserved-by-append
    fn-sf-success-list-preserved-by-append fn-sf-success-list-append-covered-pair
    fn-sf-success-member-has-record))
(in-theory (disable fn-store-files-invariants-vocabulary))
