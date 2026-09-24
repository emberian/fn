; fn: local article numbers over the served step (v0 P3, PRF-002).
;
; books/acceptance-invariants proves the numbering facts of the acceptance
; machine: prepare allocates at the group watermarks
; (fn-allocate-at-watermark), an allocation at the watermarks conflicts with
; no committed membership (fn-watermark-does-not-conflict), and every
; well-formed acceptance state holds each (group . number) in at most one
; article (fn-state-has-fresh-local-numbers).  None of those is stated over
; what the host runs.  This book states the two numbering properties over the
; host's calls: the writer events through fn-owner-step, which is
; fn-ocfg-step (host/owner-host.lisp:209), followed by the outcome installed
; through fn-owner-replace-core (fn-ocfg-with-owner of fn-own-outcome); the
; archive they speak of is the owner's committed view, the archive every
; reader pins when it opens or advances and reads through
; fn-ocfg-read-tls-prefix (owner-host.lisp:1240).
;
; Keystones:
;   fn-own-served-watermarks-never-decrease
;     for every group, the next local number of the committed view after
;     the writer events and the outcome is at least what it was before;
;   fn-own-served-local-number-is-never-reassigned
;     a (group . number) that names an article of the committed view names
;     the same Message-ID after the writer events and the outcome.
; Teeth: tests/acl2/owner-numbering-tests.lisp.
;
; How.  Under fn-own-relation the committed view is the acceptance
; projection of the replay of a prefix of the durable records
; (fn-own-view-okp), and the records only grow (fn-own-step-records-prefix).
; A writer step leaves the view alone or refreshes it at an idle store to the
; replay of the whole record list (fn-own-idle-node-is-replay).  Replaying a
; longer prefix only adds articles at the front of the committed list and
; only raises watermarks: each replayed record is a prepare, which changes
; neither, and a durable completion, which installs the pending article
; (cons) and advances the watermarks of its groups.  The Message-ID half then
; follows from fn-state-has-fresh-local-numbers on the new view.

(in-package "ACL2")
(include-book "owner-served-invariants")

; -----------------------------------------------------------------------------
; Vocabulary

; x is a tail of y: y is x with zero or more elements consed on the front.
(defun fn-own-tailp (x y)
  (declare (xargs :guard t))
  (or (equal x y)
      (and (consp y) (fn-own-tailp x (cdr y)))))

; The Message-ID of the first article of `articles' holding the local
; number (group . number), or nil.
(defun fn-own-number-holder (group number articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (if (fn-pair-memberp (cons group number) (fn-article-memberships (car articles)))
          (fn-article-msgid (car articles))
        (fn-own-number-holder group number (cdr articles)))
    nil))

(defthm fn-own-tailp-reflexive (fn-own-tailp x x))

(defthm fn-own-tailp-transitive
  (implies (and (fn-own-tailp x y) (fn-own-tailp y z))
           (fn-own-tailp x z)))

(local (defthm fn-own-tailp-nil-of-true-list
  (implies (true-listp y) (fn-own-tailp nil y))))

; -----------------------------------------------------------------------------
; One replayed record: the committed articles gain a head, the watermarks rise.

(local (defthm fn-own-next-number-of-bump
  (<= (fn-next-number g nexts) (fn-next-number g (fn-bump-number h nexts)))
  :rule-classes :linear))

(local (defthm fn-own-next-number-of-advance
  (<= (fn-next-number g nexts) (fn-next-number g (fn-advance-nexts hs nexts)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-advance-nexts hs nexts)
           :in-theory (disable fn-bump-number fn-next-number))
          ("Subgoal *1/1" :use ((:instance fn-own-next-number-of-bump (h (car hs))))))))

(local (defthm fn-own-accept-prepare-keeps-committed
  (and (equal (fn-state-nexts (fn-accept-prepare s generation msgid payload groups stamp))
              (fn-state-nexts s))
       (equal (fn-state-articles (fn-accept-prepare s generation msgid payload groups stamp))
              (fn-state-articles s)))
  :hints (("Goal" :in-theory (e/d (fn-accept-prepare) (fn-statep))))))

(local (defthm fn-own-accept-complete-grows
  (and (fn-own-tailp (fn-state-articles s)
                     (fn-state-articles (fn-accept-complete s txid generation status)))
       (<= (fn-next-number g (fn-state-nexts s))
           (fn-next-number g (fn-state-nexts (fn-accept-complete s txid generation status)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-accept-complete fn-install-pending fn-clear-pending)
                                  (fn-statep fn-pending-matchesp fn-next-number
                                   fn-advance-nexts))))))

(local (defthm fn-own-node-prepare-keeps-committed
  (and (equal (fn-state-nexts (fn-node-acceptance
                               (fn-node-prepare s generation msgid payload groups
                                                obligation-id subject evidence charge stamp)))
              (fn-state-nexts (fn-node-acceptance s)))
       (equal (fn-state-articles (fn-node-acceptance
                                  (fn-node-prepare s generation msgid payload groups
                                                   obligation-id subject evidence charge stamp)))
              (fn-state-articles (fn-node-acceptance s))))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare)
                                  (fn-node-statep fn-accept-prepare fn-retain-admissiblep
                                   fn-retain-admit fn-node-make-stage))))))

(local (defthm fn-own-node-complete-grows
  (and (fn-own-tailp (fn-state-articles (fn-node-acceptance s))
                     (fn-state-articles (fn-node-acceptance
                                         (fn-node-complete s txid generation status))))
       (<= (fn-next-number g (fn-state-nexts (fn-node-acceptance s)))
           (fn-next-number g (fn-state-nexts (fn-node-acceptance
                                               (fn-node-complete s txid generation status))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-node-complete)
                                  (fn-node-statep fn-accept-complete fn-node-pending-matchesp
                                   fn-next-number fn-own-tailp))
           :use ((:instance fn-own-accept-complete-grows (s (fn-node-acceptance s))
                            (status :durable))
                 (:instance fn-own-accept-complete-grows (s (fn-node-acceptance s))
                            (status :aborted))
                 (:instance fn-own-accept-complete-grows (s (fn-node-acceptance s))
                            (status :indeterminate)))))))

(local (defthm fn-own-replay-advance-keeps-nexts
  (equal (fn-state-nexts (fn-node-acceptance (fn-replay-advance-txid node txid)))
         (fn-state-nexts (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid)))))

(local (defthm fn-own-replay-apply-record-grows
  (implies (fn-node-statep (fn-replay-apply-record node record))
           (and (fn-own-tailp (fn-state-articles (fn-node-acceptance node))
                              (fn-state-articles (fn-node-acceptance
                                                  (fn-replay-apply-record node record))))
                (<= (fn-next-number g (fn-state-nexts (fn-node-acceptance node)))
                    (fn-next-number g (fn-state-nexts (fn-node-acceptance
                                                        (fn-replay-apply-record node record)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-replay-complete-retention fn-replay-node-with-retention
                                   fn-replay-apply-identity-neutral)
                                  (fn-node-statep fn-store-event-p fn-store-event-sequence
                                   fn-record-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-store-retention-event-p fn-cpe-eventp
                                   fn-th-topic-eventp fn-replay-composite-record
                                   fn-node-prepare fn-node-complete fn-node-pending-matchesp
                                   fn-retain-admissiblep fn-retain-admit fn-retain-release
                                   fn-retain-matching-releasep fn-retain-find-id
                                   fn-next-number fn-own-tailp))
           :use ((:instance fn-own-node-complete-grows
                            (s (fn-node-prepare
                                (fn-replay-advance-txid node (fn-store-event-txid record))
                                (fn-record-generation (if (fn-stxa-p record) (fn-replay-composite-record record) record))
                                (fn-record-msgid (if (fn-stxa-p record) (fn-replay-composite-record record) record))
                                (fn-record-payload (if (fn-stxa-p record) (fn-replay-composite-record record) record))
                                (fn-record-groups (if (fn-stxa-p record) (fn-replay-composite-record record) record))
                                (fn-record-obligation-id (if (fn-stxa-p record) (fn-replay-composite-record record) record))
                                (fn-record-content-subject (if (fn-stxa-p record) (fn-replay-composite-record record) record))
                                (fn-record-release-evidence (if (fn-stxa-p record) (fn-replay-composite-record record) record))
                                (fn-record-charge (if (fn-stxa-p record) (fn-replay-composite-record record) record))
                                (fn-record-stamp (if (fn-stxa-p record) (fn-replay-composite-record record) record))))
                            (txid (fn-record-txid (if (fn-stxa-p record) (fn-replay-composite-record record) record)))
                            (generation (fn-record-generation (if (fn-stxa-p record) (fn-replay-composite-record record) record)))
                            (status :durable))))))
)

; -----------------------------------------------------------------------------
; A replay, and a replay of a longer prefix of the same records.

(local (defthm fn-own-replay-loop-grows
  (implies (fn-replay-okp (fn-replay-loop node records seq))
           (and (fn-own-tailp (fn-state-articles (fn-node-acceptance node))
                              (fn-state-articles (fn-node-acceptance
                                                  (fn-replay-result-node
                                                   (fn-replay-loop node records seq)))))
                (<= (fn-next-number g (fn-state-nexts (fn-node-acceptance node)))
                    (fn-next-number g (fn-state-nexts (fn-node-acceptance
                                                        (fn-replay-result-node
                                                         (fn-replay-loop node records seq))))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-replay-loop node records seq)
           :in-theory (e/d (fn-replay-loop)
                           (fn-node-statep fn-store-event-p fn-store-event-sequence
                            fn-replay-apply-record fn-replay-okp fn-next-number fn-own-tailp)))
          ("Subgoal *1/5"
           :use ((:instance fn-own-replay-apply-record-grows (record (car records)))
                 (:instance fn-own-tailp-transitive
                            (x (fn-state-articles (fn-node-acceptance node)))
                            (y (fn-state-articles (fn-node-acceptance
                                                   (fn-replay-apply-record node (car records)))))
                            (z (fn-state-articles (fn-node-acceptance
                                                   (fn-replay-result-node
                                                    (fn-replay-loop (fn-replay-apply-record node (car records))
                                                                    (cdr records) (+ 1 seq)))))))))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-replay-loop fn-replay-okp)
                                 (fn-node-statep fn-store-event-p fn-store-event-sequence
                                  fn-replay-apply-record fn-next-number fn-own-tailp)))))))

(local (defun fn-own-loop-prefix-induct (node xs ys seq)
  (declare (xargs :measure (len ys)))
  (if (and (consp xs) (consp ys))
      (fn-own-loop-prefix-induct (fn-replay-apply-record node (car ys))
                                 (cdr xs) (cdr ys) (+ 1 seq))
    (list node xs ys seq))))

(local (defthm fn-own-replay-loop-prefix-grows
  (implies (and (fn-sf-prefixp xs ys)
                (natp seq)
                (fn-replay-okp (fn-replay-loop node ys seq)))
           (and (fn-replay-okp (fn-replay-loop node xs seq))
                (fn-own-tailp (fn-state-articles (fn-node-acceptance
                                                  (fn-replay-result-node
                                                   (fn-replay-loop node xs seq))))
                              (fn-state-articles (fn-node-acceptance
                                                  (fn-replay-result-node
                                                   (fn-replay-loop node ys seq)))))
                (<= (fn-next-number g (fn-state-nexts (fn-node-acceptance
                                                        (fn-replay-result-node
                                                         (fn-replay-loop node xs seq)))))
                    (fn-next-number g (fn-state-nexts (fn-node-acceptance
                                                        (fn-replay-result-node
                                                         (fn-replay-loop node ys seq))))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-own-loop-prefix-induct node xs ys seq)
           :in-theory (e/d (fn-sf-prefixp)
                           (fn-node-statep fn-store-event-p fn-store-event-sequence
                            fn-replay-apply-record fn-next-number fn-own-tailp)))
          ("Subgoal *1/2" :use ((:instance fn-own-replay-loop-grows (records ys)))
           :expand ((fn-replay-loop node nil seq)))
          (and stable-under-simplificationp
               '(:expand ((fn-replay-loop node xs seq) (fn-replay-loop node ys seq)))))))

(local (defthm fn-own-article-listp-true-list
  (implies (fn-article-listp c xs) (true-listp xs))))

(local (defthm fn-own-next-number-natural
  (implies (fn-nexts-for-p gs nexts) (natp (fn-next-number g nexts)))))

(local (defthm fn-own-statep-committed-facts
  (implies (fn-statep a)
           (and (true-listp (fn-state-articles a))
                (natp (fn-next-number g (fn-state-nexts a)))
                (fn-articles-freshp (fn-state-articles a))))
  
  :hints (("Goal" :use ((:instance fn-state-has-fresh-local-numbers (s a)))
           :in-theory (e/d (fn-statep) (fn-next-number fn-article-listp fn-articles-freshp
                                        fn-nexts-for-p fn-articles-below-nextsp fn-pendingp
                                        fn-state-has-fresh-local-numbers))))))

(local (defthm fn-own-node-statep-acceptance
  (implies (fn-node-statep node) (fn-statep (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-node-statep)))))

(local (defthm fn-own-replay-okp-node-statep
  (implies (fn-replay-okp x) (fn-node-statep (fn-replay-result-node x)))
  :hints (("Goal" :in-theory (enable fn-replay-okp)))))

(local (defthm fn-own-replay-fault-is-not-okp
  (not (fn-replay-okp (fn-replay-fault node seq reason)))
  :hints (("Goal" :in-theory (enable fn-replay-okp)))))

(local (defthm fn-own-next-number-of-nil
  (equal (fn-next-number g nil) 0)))

(local (defthm fn-own-statep-next-number-nonnegative
  (implies (fn-statep a) (<= 0 (fn-next-number g (fn-state-nexts a))))
  :rule-classes :linear
  :hints (("Goal" :use fn-own-statep-committed-facts :in-theory (disable fn-own-statep-committed-facts)))))

(defthm fn-own-replay-node-prefix-grows
  (implies (and (fn-sf-prefixp xs ys)
                (fn-sf-replay-node groups capacity ys f2))
           (and (fn-statep (fn-node-acceptance (fn-sf-replay-node groups capacity ys f2)))
                (fn-own-tailp
                 (fn-state-articles (fn-node-acceptance (fn-sf-replay-node groups capacity xs f1)))
                 (fn-state-articles (fn-node-acceptance (fn-sf-replay-node groups capacity ys f2))))
                (<= (fn-next-number
                     g (fn-state-nexts (fn-node-acceptance (fn-sf-replay-node groups capacity xs f1))))
                    (fn-next-number
                     g (fn-state-nexts (fn-node-acceptance (fn-sf-replay-node groups capacity ys f2)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-sf-replay-node fn-replay)
                                  (fn-node-statep fn-replay-loop fn-replay-okp fn-next-number
                                   fn-own-tailp fn-statep fn-node-initial-state
                                   fn-replay-advance-okp))
           :use ((:instance fn-own-replay-loop-prefix-grows
                            (node (fn-node-initial-state groups capacity)) (seq 0))
                 (:instance fn-replay-advance-preserves-node-statep
                            (node (fn-replay-result-node
                                   (fn-replay-loop (fn-node-initial-state groups capacity) ys 0)))
                            (recorded-txid f2))))))

; -----------------------------------------------------------------------------
; A writer step keeps the committed view or refreshes it at an idle store.

(local (defthm fn-own-take-is-prefix
  (implies (true-listp ys) (fn-sf-prefixp (fn-own-take n ys) ys))
  :hints (("Goal" :in-theory (enable fn-sf-prefixp)))))

(local (defthm fn-own-refresh-view-is-kept-or-the-idle-node
  (or (equal (fn-own-view (fn-own-refresh o)) (fn-own-view o))
      (and (fn-own-store-idlep (fn-own-store o))
           (equal (fn-own-view-version (fn-own-view (fn-own-refresh o)))
                  (len (fn-sf-records (fn-sn-files (fn-own-store o)))))
           (equal (fn-own-view-archive (fn-own-view (fn-own-refresh o)))
                  (fn-node-acceptance (fn-sn-node (fn-own-store o))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-refresh fn-own-view-version fn-own-view-archive fn-own-view-make-group-indexed) (fn-own-store-idlep fn-midx-refresh fn-gidx-build))))))

(local (defthm fn-own-writer-step-view-is-kept-or-the-idle-node
  (implies (fn-ocfg-writer-eventp event)
           (let ((o2 (fn-own-step o event)))
             (or (equal (fn-own-view o2) (fn-own-view o))
                 (and (fn-own-store-idlep (fn-own-store o2))
                      (equal (fn-own-view-version (fn-own-view o2))
                             (len (fn-sf-records (fn-sn-files (fn-own-store o2)))))
                      (equal (fn-own-view-archive (fn-own-view o2))
                             (fn-node-acceptance (fn-sn-node (fn-own-store o2))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-step fn-own-take-submission fn-own-begin
                                   fn-own-store-step fn-own-complete fn-ocfg-writer-eventp fn-own-refresh-keeps-fields)
                                  (fn-own-refresh fn-own-store-idlep fn-sn-finish fn-snrt-step))
           :use ((:instance fn-own-refresh-view-is-kept-or-the-idle-node
                            (o (fn-own-make (fn-snrt-step (fn-own-store o) (cadr event)) (fn-own-view o)
                                            (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                                            (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o)
                                            (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
                                            (fn-own-inflight o) (fn-own-feeds o))))
                 (:instance fn-own-refresh-view-is-kept-or-the-idle-node
                            (o (fn-own-make (fn-sn-finish (fn-own-store o)) (fn-own-view o) (fn-own-conns o)
                                            (fn-own-next-id o) (fn-own-max-conns o) nil
                                            (append (fn-own-ledger o)
                                                          (list (fn-sf-completion (fn-sn-files (fn-own-store o)))))
                                            (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                                            (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))))))))
)

(local (defthm fn-own-finish-keeps-store-configuration
  (and (equal (fn-sn-groups (fn-sn-finish s)) (fn-sn-groups s))
       (equal (fn-sn-capacity (fn-sn-finish s)) (fn-sn-capacity s)))
  :hints (("Goal" :use ((:instance fn-own-snrt-step-keeps-configuration (event '(:finish))))
           :in-theory (e/d (fn-snrt-step fn-snt-step) (fn-sn-finish fn-own-snrt-step-keeps-configuration))))))

(local (defthm fn-own-writer-step-keeps-store-configuration
  (implies (fn-ocfg-writer-eventp event)
           (and (equal (fn-sn-groups (fn-own-store (fn-own-step o event)))
                       (fn-sn-groups (fn-own-store o)))
                (equal (fn-sn-capacity (fn-own-store (fn-own-step o event)))
                       (fn-sn-capacity (fn-own-store o)))))
  :hints (("Goal" :in-theory (e/d (fn-own-step fn-own-take-submission fn-own-begin
                                   fn-own-store-step fn-own-complete fn-ocfg-writer-eventp
                                   fn-own-refresh-keeps-fields fn-own-snrt-step-keeps-configuration)
                                  (fn-own-refresh fn-own-store-idlep fn-snrt-step fn-sn-finish))))))

(local (defthm fn-own-relation-parts
  (implies (fn-own-relation o)
           (and (fn-snt-relation (fn-own-store o))
                (fn-own-view-okp (fn-own-view o)
                                 (fn-sn-groups (fn-own-store o))
                                 (fn-sn-capacity (fn-own-store o))
                                 (fn-sf-records (fn-sn-files (fn-own-store o))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-relation)
                                  (fn-own-view-okp fn-own-conns-okp fn-own-conn-boundedp
                                   fn-snt-relation fn-own-ledger-durablep fn-own-facts-okp))))))

(local (defthm fn-own-view-okp-archive
  (implies (fn-own-view-okp view groups capacity records)
           (and (natp (fn-own-view-version view))
                (<= (fn-own-view-version view) (len records))
                (equal (fn-own-view-archive view)
                       (fn-node-acceptance
                        (fn-sf-replay-node groups capacity
                                           (fn-own-take (fn-own-view-version view) records)
                                           (fn-own-view-frontier view))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-view-okp fn-own-prefix-archive)
                                  (fn-sf-replay-node fn-midx-correspondencep fn-gidx-build))))))

(local (defthm fn-own-related-node-is-statep
  (implies (fn-snt-relation s) (fn-node-statep (fn-sn-node s)))
  :hints (("Goal" :use (fn-snt-relation-implies-structural-state
                        fn-snt-typed-store-components)
           :in-theory (disable fn-snt-relation fn-sn-statep fn-node-statep)))))

; -----------------------------------------------------------------------------
; The committed view over one writer step, then over the host's writer events.

(local (defthm fn-own-writer-step-view-archive-grows
  (implies (and (fn-own-relation o)
                (fn-ocfg-writer-eventp event))
           (let ((a1 (fn-own-view-archive (fn-own-view o)))
                 (a2 (fn-own-view-archive (fn-own-view (fn-own-step o event)))))
             (and (fn-own-tailp (fn-state-articles a1) (fn-state-articles a2))
                  (<= (fn-next-number g (fn-state-nexts a1))
                      (fn-next-number g (fn-state-nexts a2)))
                  (or (equal (fn-own-view (fn-own-step o event)) (fn-own-view o))
                      (fn-statep a2)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-own-writer-step-view-is-kept-or-the-idle-node)
                 (:instance fn-own-step-preserves-relation)
                 (:instance fn-own-step-records-prefix)
                 (:instance fn-own-relation-parts)
                 (:instance fn-own-relation-parts (o (fn-own-step o event)))
                 (:instance fn-own-view-okp-archive
                            (view (fn-own-view o))
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (records (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-own-idle-node-is-replay (s (fn-own-store (fn-own-step o event))))
                 (:instance fn-own-related-node-is-statep (s (fn-own-store (fn-own-step o event))))
                 (:instance fn-own-relation-records-true-list (o (fn-own-step o event)))
                 (:instance fn-own-take-of-prefix
                            (n (fn-own-view-version (fn-own-view o)))
                            (xs (fn-sf-records (fn-sn-files (fn-own-store o))))
                            (ys (fn-sf-records (fn-sn-files (fn-own-store (fn-own-step o event))))))
                 (:instance fn-own-take-is-prefix
                            (n (fn-own-view-version (fn-own-view o)))
                            (ys (fn-sf-records (fn-sn-files (fn-own-store (fn-own-step o event))))))
                 (:instance fn-own-replay-node-prefix-grows
                            (groups (fn-sn-groups (fn-own-store o)))
                            (capacity (fn-sn-capacity (fn-own-store o)))
                            (xs (fn-own-take (fn-own-view-version (fn-own-view o))
                                             (fn-sf-records (fn-sn-files (fn-own-store (fn-own-step o event))))))
                            (ys (fn-sf-records (fn-sn-files (fn-own-store (fn-own-step o event)))))
                            (f1 (fn-own-view-frontier (fn-own-view o)))
                            (f2 (fn-sf-frontier (fn-sn-files (fn-own-store (fn-own-step o event)))))))
           :in-theory (union-theories
                       '(fn-own-tailp-reflexive fn-own-writer-step-keeps-store-configuration
                         fn-own-node-statep-acceptance)
                       (theory 'minimal-theory)))
          (and stable-under-simplificationp
               '(:in-theory (union-theories
                             '(fn-own-tailp-reflexive fn-own-writer-step-keeps-store-configuration
                               fn-own-node-statep-acceptance fn-own-prefixp-len)
                             (theory 'ground-zero)))))))

(local (defthm fn-ocfg-writer-step-owner
  (implies (fn-ocfg-writer-eventp event)
           (or (equal (fn-ocfg-owner (fn-ocfg-step oc event)) (fn-ocfg-owner oc))
               (equal (fn-ocfg-owner (fn-ocfg-step oc event))
                      (fn-own-step (fn-ocfg-owner oc) event))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step fn-ocfg-pass fn-ocfg-complete
                                   fn-ocfg-with-owner fn-ocfg-writer-eventp)
                                  (fn-own-step fn-own-complete fn-ocfg-open fn-ocfg-read
                                   fn-ocfg-read-step fn-ocfg-fault fn-ocfg-close
                                   fn-ocfg-advance fn-ocfg-open-peer fn-ocfg-reconfigure))
           :expand ((fn-own-step (fn-ocfg-owner oc) event))))))

(defthm fn-own-outcome-keeps-the-view
  (equal (fn-own-view (cdr (fn-own-outcome o id word))) (fn-own-view o))
  :hints (("Goal" :in-theory (enable fn-own-outcome fn-own-advance fn-own-advance-result
                                     fn-own-set-conns))))

(local (defthm fn-ocfg-writer-run-view-archive-grows
  (implies (and (fn-own-relation (fn-ocfg-owner oc))
                (fn-ocfg-writer-eventsp events))
           (let* ((o1 (fn-ocfg-owner oc))
                  (o2 (fn-ocfg-owner (fn-ocfg-run oc events)))
                  (a1 (fn-own-view-archive (fn-own-view o1)))
                  (a2 (fn-own-view-archive (fn-own-view o2))))
             (and (fn-own-relation o2)
                  (fn-own-tailp (fn-state-articles a1) (fn-state-articles a2))
                  (<= (fn-next-number g (fn-state-nexts a1))
                      (fn-next-number g (fn-state-nexts a2)))
                  (or (equal (fn-own-view o2) (fn-own-view o1))
                      (fn-statep a2)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ocfg-run oc events)
           :in-theory (e/d (fn-ocfg-run fn-ocfg-writer-eventsp)
                           (fn-ocfg-step fn-own-step fn-own-relation fn-ocfg-writer-eventp
                            fn-next-number fn-own-tailp fn-statep)))
          ("Subgoal *1/1"
           :use ((:instance fn-ocfg-writer-step-owner (event (car events)))
                 (:instance fn-own-writer-step-view-archive-grows
                            (o (fn-ocfg-owner oc)) (event (car events)))
                 (:instance fn-own-step-preserves-relation
                            (o (fn-ocfg-owner oc)) (event (car events)))
                 (:instance fn-own-tailp-transitive
                            (x (fn-state-articles (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc)))))
                            (y (fn-state-articles (fn-own-view-archive
                                                   (fn-own-view (fn-ocfg-owner (fn-ocfg-step oc (car events)))))))
                            (z (fn-state-articles (fn-own-view-archive
                                                   (fn-own-view (fn-ocfg-owner
                                                                 (fn-ocfg-run (fn-ocfg-step oc (car events))
                                                                              (cdr events))))))))))))
)

; -----------------------------------------------------------------------------
; A number held in a fresh article list is held by one article only.

(local (defthm fn-own-pair-memberp-of-append
  (implies (or (fn-pair-memberp p xs) (fn-pair-memberp p ys))
           (fn-pair-memberp p (append xs ys)))
  :hints (("Goal" :in-theory (enable fn-pair-memberp)))))

(local (defthm fn-own-holder-has-the-pair
  (implies (fn-own-number-holder group number articles)
           (fn-pair-memberp (cons group number) (fn-all-article-memberships articles)))
  :hints (("Goal" :in-theory (disable fn-pair-memberp fn-article-memberships fn-article-msgid)))))

(local (defthm fn-own-pair-memberp-of-equal-pair
  (implies (and (fn-pair-equalp p m) (fn-pair-memberp p xs))
           (fn-pair-memberp m xs))
  :hints (("Goal" :in-theory (enable fn-pair-memberp fn-pair-equalp)))))

(local (defthm fn-own-member-pair-conflicts
  (implies (and (fn-pair-memberp p ms)
                (fn-pair-memberp p (fn-all-article-memberships articles)))
           (fn-memberships-conflictsp ms articles))
  :hints (("Goal" :induct (fn-memberships-conflictsp ms articles)
           :in-theory (e/d (fn-pair-memberp) (fn-all-article-memberships))))))

(local (defthm fn-own-holder-of-fresh-extension
  (implies (and (fn-own-tailp xs ys)
                (fn-articles-freshp ys)
                (fn-own-number-holder group number xs))
           (equal (fn-own-number-holder group number ys)
                  (fn-own-number-holder group number xs)))
  :hints (("Goal" :induct (fn-own-tailp xs ys)
           :in-theory (disable fn-pair-memberp fn-all-article-memberships
                               fn-article-memberships fn-article-msgid))
          ("Subgoal *1/2" :use ((:instance fn-own-member-pair-conflicts
                                           (p (cons group number))
                                           (ms (fn-article-memberships (car ys)))
                                           (articles (cdr ys)))
                                (:instance fn-own-holder-has-the-pair (articles (cdr ys))))))))

; -----------------------------------------------------------------------------
; KEYSTONES (P3, PRF-002).

; For any group, any sequence of writer events -- (:take), (:begin id),
; (:store e), (:complete) -- through fn-ocfg-step (fn-owner-step,
; owner-host.lisp:209), then the outcome for any connection with any store
; word installed on the core (fn-owner-replace-core, fn-ocfg-with-owner of
; fn-own-outcome): the committed view's next local number for that group is
; at least what it was.  Hypothesis: the owner relation, which is what
; fn-ocfg-statep carries for the configured owner the host holds.
(defthm fn-own-served-watermarks-never-decrease
  (implies (and (fn-own-relation (fn-ocfg-owner oc))
                (fn-ocfg-writer-eventsp events))
           (let* ((oc1 (fn-ocfg-run oc events))
                  (oc2 (fn-ocfg-with-owner
                        oc1 (cdr (fn-own-outcome (fn-ocfg-owner oc1) sub-id word)))))
             (<= (fn-next-number
                  group (fn-state-nexts (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc)))))
                 (fn-next-number
                  group (fn-state-nexts (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc2))))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ocfg-writer-run-view-archive-grows (g group)))
           :in-theory (e/d (fn-ocfg-with-owner)
                           (fn-own-outcome fn-ocfg-run fn-own-relation fn-next-number
                            fn-own-tailp fn-statep)))))

; Over the same host calls: a local number (group . number) that names an
; article of the committed view before names an article with the same
; Message-ID after.  With the watermark theorem this is PRF-002's "never
; reuses an allocated number for another article" over the served path.
(defthm fn-own-served-local-number-is-never-reassigned
  (implies (and (fn-own-relation (fn-ocfg-owner oc))
                (fn-ocfg-writer-eventsp events)
                (fn-own-number-holder
                 group number
                 (fn-state-articles (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))))
           (let* ((oc1 (fn-ocfg-run oc events))
                  (oc2 (fn-ocfg-with-owner
                        oc1 (cdr (fn-own-outcome (fn-ocfg-owner oc1) sub-id word)))))
             (equal (fn-own-number-holder
                     group number
                     (fn-state-articles (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc2)))))
                    (fn-own-number-holder
                     group number
                     (fn-state-articles (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ocfg-writer-run-view-archive-grows (g group))
                        (:instance fn-own-holder-of-fresh-extension
                                   (xs (fn-state-articles (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc)))))
                                   (ys (fn-state-articles (fn-own-view-archive
                                                           (fn-own-view (fn-ocfg-owner (fn-ocfg-run oc events)))))))
                        (:instance fn-own-statep-committed-facts
                                   (g group)
                                   (a (fn-own-view-archive
                                       (fn-own-view (fn-ocfg-owner (fn-ocfg-run oc events)))))))
           :in-theory (e/d (fn-ocfg-with-owner)
                           (fn-own-outcome fn-ocfg-run fn-own-relation fn-next-number
                            fn-own-tailp fn-statep fn-own-number-holder
                            fn-own-holder-of-fresh-extension fn-own-statep-committed-facts
                            fn-articles-freshp)))))

(in-theory (disable fn-own-tailp fn-own-number-holder))
