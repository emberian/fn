; T2a: the host-called constructor and durable stamp carrier.
(in-package "ACL2")
(include-book "store-node-invariants")

; This projects the stamp conjunct of the actual durable completion theorem.
; The work is in fn-sn-actual-durable-completion-installs-record, whose proof
; follows the live node completion and whose predicate now binds the stamp.
(defthm fn-sn-finish-installs-the-stamp-the-record-carries
  (implies (and (fn-sn-completion-enabledp s)
                (not (fn-store-retention-event-p (fn-sn-completion-record s)))
                (not (fn-stxe-p (fn-sn-completion-record s)))
                (not (fn-stxk-p (fn-sn-completion-record s)))
                (not (fn-stxa-p (fn-sn-completion-record s))))
           (equal (fn-article-stamp
                   (fn-find-article
                    (fn-record-msgid (fn-sn-completion-record s))
                    (fn-state-articles
                     (fn-node-acceptance (fn-sn-node (fn-sn-finish s))))))
                  (fn-record-stamp (fn-sn-completion-record s))))
  :hints (("Goal" :use (fn-sn-finish-installs-exact-article-and-archive-pin)
           :in-theory (e/d (fn-sn-committed-recordp)
                           (fn-sn-finish-installs-exact-article-and-archive-pin
                            fn-sn-finish
                            fn-sn-completion-enabledp
                            fn-sn-completion-record
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-store-retention-event-p)))))

; These two projections are deliberately independent of the replay step.
; Article state is newest first; the Store journal is oldest first.
(defun fn-articles-msgid-stamps (articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (append (fn-articles-msgid-stamps (cdr articles))
              (list (cons (fn-article-msgid (car articles))
                          (fn-article-stamp (car articles)))))
    nil))

(defun fn-replay-article-record (record)
  (declare (xargs :guard t))
  (if (fn-stxa-p record)
      (fn-replay-composite-record record)
    record))

(defun fn-replay-article-eventp (record)
  (declare (xargs :guard t))
  (and (not (fn-store-retention-event-p record))
       (not (fn-stxe-p record))
       (not (fn-stxk-p record))))

(defun fn-replay-journal-article-stamps (records)
  (declare (xargs :guard t))
  (if (consp records)
      (if (fn-replay-article-eventp (car records))
          (cons (cons (fn-record-msgid (fn-replay-article-record (car records)))
                      (fn-record-stamp (fn-replay-article-record (car records))))
                (fn-replay-journal-article-stamps (cdr records)))
        (fn-replay-journal-article-stamps (cdr records)))
    nil))

(local
 (defthm fn-stamp-node-acceptance-statep
   (implies (fn-node-statep node)
            (fn-statep (fn-node-acceptance node)))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

(defthm fn-node-complete-installs-pending-stamp
  (implies (fn-node-pending-matchesp node txid generation)
           (equal
            (fn-article-stamp
             (fn-find-article
              (fn-pending-msgid (fn-state-pending (fn-node-acceptance node)))
              (fn-state-articles
               (fn-node-acceptance
                (fn-node-complete node txid generation :durable)))))
            (fn-pending-stamp (fn-state-pending (fn-node-acceptance node)))))
  :hints (("Goal" :use ((:instance fn-durable-completion-installs-exact-pending-article
                                  (s (fn-node-acceptance node))))
           :in-theory (e/d (fn-node-complete fn-node-pending-matchesp
                                            fn-article-from-pending)
                           (fn-durable-completion-installs-exact-pending-article
                            fn-accept-complete fn-find-article fn-node-statep
                            fn-statep))))
  :rule-classes nil)

(defthm fn-stamp-prepare-pending-fields-when-staged
  (implies (and (fn-node-statep node)
                (null (fn-node-stage node))
                (fn-node-pending-matchesp
                 (fn-node-prepare node generation msgid payload groups
                                  obligation-id subject evidence charge stamp)
                 txid generation))
           (let ((pending (fn-state-pending
                           (fn-node-acceptance
                            (fn-node-prepare node generation msgid payload groups
                                             obligation-id subject evidence charge stamp)))))
             (and (equal (fn-pending-msgid pending) msgid)
                  (equal (fn-pending-stamp pending) stamp))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-node-prepare fn-accept-prepare
                              fn-node-pending-matchesp fn-pending-matchesp)))
  :rule-classes nil)

(defthm fn-replay-advance-keeps-idle-stage
  (implies (null (fn-node-stage node))
           (null (fn-node-stage (fn-replay-advance-txid node txid))))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-stamp-prepared-completion-installs-stamp
  (implies
   (and (fn-node-statep node)
        (null (fn-node-stage node))
        (fn-node-pending-matchesp
         (fn-node-prepare node generation msgid payload groups
                          obligation-id subject evidence charge stamp)
         txid generation))
   (equal
    (fn-article-stamp
     (fn-find-article
      msgid
      (fn-state-articles
       (fn-node-acceptance
        (fn-node-complete
         (fn-node-prepare node generation msgid payload groups
                          obligation-id subject evidence charge stamp)
         txid generation :durable)))))
    stamp))
  :hints (("Goal"
           :use (fn-stamp-prepare-pending-fields-when-staged
                 (:instance fn-node-complete-installs-pending-stamp
                            (node (fn-node-prepare node generation msgid payload groups
                                                   obligation-id subject evidence charge stamp))))
           :in-theory (disable fn-node-prepare fn-node-complete
                               fn-node-pending-matchesp fn-node-statep fn-statep
                               fn-find-article)))
  :rule-classes nil)

(defthm fn-replay-apply-record-installs-the-stamp
  (let ((article (fn-replay-article-record record)))
    (implies (and (fn-node-statep node)
                  (fn-store-event-p record)
                  (fn-replay-article-eventp record)
                  (consp (fn-replay-apply-record node record)))
             (equal (fn-article-stamp
                     (fn-find-article
                      (fn-record-msgid article)
                      (fn-state-articles
                       (fn-node-acceptance
                        (fn-replay-apply-record node record)))))
                    (fn-record-stamp article))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-replay-advance-keeps-idle-stage
                            (txid (fn-store-event-txid record)))
                 (:instance fn-stamp-prepared-completion-installs-stamp
                            (node (fn-replay-advance-txid
                                   node (fn-store-event-txid record)))
                            (generation (fn-record-generation
                                         (fn-replay-article-record record)))
                            (msgid (fn-record-msgid
                                    (fn-replay-article-record record)))
                            (payload (fn-record-payload
                                      (fn-replay-article-record record)))
                            (groups (fn-record-groups
                                     (fn-replay-article-record record)))
                            (obligation-id (fn-record-obligation-id
                                            (fn-replay-article-record record)))
                            (subject (fn-record-content-subject
                                      (fn-replay-article-record record)))
                            (evidence (fn-record-release-evidence
                                       (fn-replay-article-record record)))
                            (charge (fn-record-charge
                                     (fn-replay-article-record record)))
                            (stamp (fn-record-stamp
                                    (fn-replay-article-record record)))
                            (txid (fn-record-txid
                                   (fn-replay-article-record record)))))
           :in-theory
           (e/d (fn-replay-apply-record)
                (fn-record-shape-vocabulary
                 fn-node-prepare fn-node-complete
                 fn-replay-advance-keeps-idle-stage
                 fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-store-retention-event-p))))
  :rule-classes nil)

(local
 (defthm fn-stamp-composite-kind-disjoint
   (implies (fn-stxa-p record)
            (and (not (fn-store-retention-event-p record))
                 (not (fn-stxe-p record))
                 (not (fn-stxk-p record))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory
            (e/d (fn-stxa-p fn-stxa-shapep fn-stxa-keyring-generation
                  fn-stxe-p fn-stxe-shapep fn-stxe-msgid
                  fn-stxk-p fn-stxk-shapep
                  fn-store-retention-event-p fn-record-msgidp)
                 (fn-stxe-bounded-octetsp
                  fn-record-metadata-bytes-p))))))

(local
 (defthm fn-stamp-composite-enabled-implies-replay-premises
   (implies (and (fn-sn-completion-enabledp s)
                 (fn-stxa-p (fn-sn-completion-record s)))
            (and (fn-node-statep (fn-sn-node s))
                 (fn-store-event-p (fn-sn-completion-record s))
                 (fn-replay-article-eventp (fn-sn-completion-record s))
                 (consp (fn-replay-apply-record
                         (fn-sn-node s) (fn-sn-completion-record s)))))
   :hints (("Goal" :use fn-stamp-composite-kind-disjoint :in-theory
            (e/d (fn-sn-completion-enabledp fn-sn-statep fn-store-event-p
                 fn-replay-article-eventp)
                 (fn-record-shape-vocabulary fn-replay-apply-record
                  fn-stxe-p fn-stxk-p fn-stxa-p
                  fn-store-retention-event-p))))))

(defthm fn-sn-finish-installs-the-stamp-the-composite-carries
  (implies (and (fn-sn-completion-enabledp s)
                (fn-stxa-p (fn-sn-completion-record s)))
           (equal (fn-article-stamp
                   (fn-find-article
                    (fn-record-msgid
                     (fn-replay-composite-record (fn-sn-completion-record s)))
                    (fn-state-articles
                     (fn-node-acceptance (fn-sn-node (fn-sn-finish s))))))
                  (fn-record-stamp
                   (fn-replay-composite-record (fn-sn-completion-record s)))))
  :hints (("Goal"
           :use (fn-stamp-composite-enabled-implies-replay-premises
                 (:instance fn-replay-apply-record-installs-the-stamp
                            (node (fn-sn-node s))
                            (record (fn-sn-completion-record s))))
           :in-theory (e/d (fn-sn-finish fn-replay-article-record)
                           (fn-store-event-p fn-record-shape-vocabulary
                            fn-stxa-p fn-stxe-p fn-stxk-p
                            fn-sn-completion-enabledp
                            fn-store-retention-event-p))))
  :rule-classes nil)

; Journal replay adds each accepted article to the front of node state.  The
; projection reverses that representation, so one committed article appends
; exactly one journal-order pair.
(defthm fn-articles-msgid-stamps-of-cons
  (equal (fn-articles-msgid-stamps (cons article articles))
         (append (fn-articles-msgid-stamps articles)
                 (list (cons (fn-article-msgid article)
                             (fn-article-stamp article)))))
  :hints (("Goal" :in-theory (enable fn-articles-msgid-stamps))))

(defthm fn-stamp-node-prepare-keeps-articles
  (implies (fn-node-statep node)
           (equal (fn-state-articles
                   (fn-node-acceptance
                    (fn-node-prepare node generation msgid payload groups
                                     obligation-id subject evidence charge stamp)))
                  (fn-state-articles (fn-node-acceptance node))))
  :hints (("Goal" :in-theory (enable fn-node-prepare fn-accept-prepare))))

(defthm fn-stamp-node-complete-adds-pending-article
  (implies (fn-node-pending-matchesp node txid generation)
           (equal (fn-state-articles
                   (fn-node-acceptance
                    (fn-node-complete node txid generation :durable)))
                  (cons (fn-article-from-pending
                         (fn-state-pending (fn-node-acceptance node)))
                        (fn-state-articles (fn-node-acceptance node)))))
  :hints (("Goal" :in-theory (enable fn-node-complete
                                     fn-node-pending-matchesp
                                     fn-accept-complete fn-install-pending
                                     fn-statep fn-node-statep))))

(defthm fn-stamp-apply-identity-neutral-keeps-articles
  (implies (consp (fn-replay-apply-identity-neutral node record))
           (equal (fn-state-articles
                   (fn-node-acceptance
                    (fn-replay-apply-identity-neutral node record)))
                  (fn-state-articles (fn-node-acceptance node))))
  :hints (("Goal" :in-theory (enable fn-replay-apply-identity-neutral))))

(defthm fn-stamp-apply-retention-event-keeps-articles
  (implies (consp (fn-replay-apply-retention-event node record))
           (equal (fn-state-articles
                   (fn-node-acceptance
                    (fn-replay-apply-retention-event node record)))
                  (fn-state-articles (fn-node-acceptance node))))
  :hints (("Goal" :in-theory
           (enable fn-replay-apply-retention-event
                   fn-replay-complete-retention
                   fn-replay-node-with-retention))))

(defthm fn-stamp-apply-article-adds-journal-pair
  (let ((article (fn-replay-article-record record)))
    (implies (and (fn-node-statep node)
                  (fn-store-event-p record)
                  (fn-replay-article-eventp record)
                  (consp (fn-replay-apply-record node record)))
             (equal
              (fn-articles-msgid-stamps
               (fn-state-articles
                (fn-node-acceptance (fn-replay-apply-record node record))))
              (append (fn-articles-msgid-stamps
                       (fn-state-articles (fn-node-acceptance node)))
                      (list (cons (fn-record-msgid article)
                                  (fn-record-stamp article)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-replay-advance-keeps-idle-stage
                            (txid (fn-store-event-txid record)))
                 (:instance fn-stamp-prepare-pending-fields-when-staged
                            (node (fn-replay-advance-txid
                                   node (fn-store-event-txid record)))
                            (generation (fn-record-generation
                                         (fn-replay-article-record record)))
                            (msgid (fn-record-msgid
                                    (fn-replay-article-record record)))
                            (payload (fn-record-payload
                                      (fn-replay-article-record record)))
                            (groups (fn-record-groups
                                     (fn-replay-article-record record)))
                            (obligation-id (fn-record-obligation-id
                                            (fn-replay-article-record record)))
                            (subject (fn-record-content-subject
                                      (fn-replay-article-record record)))
                            (evidence (fn-record-release-evidence
                                       (fn-replay-article-record record)))
                            (charge (fn-record-charge
                                     (fn-replay-article-record record)))
                            (stamp (fn-record-stamp
                                    (fn-replay-article-record record)))
                            (txid (fn-record-txid
                                   (fn-replay-article-record record)))))
           :in-theory (e/d (fn-replay-apply-record fn-article-from-pending)
                           (fn-record-shape-vocabulary
                            fn-node-prepare fn-node-complete
                            fn-replay-advance-keeps-idle-stage
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-store-retention-event-p))))
  :rule-classes nil)

(defthm fn-stamp-apply-record-projects-one-event
  (implies (and (fn-node-statep node)
                (fn-store-event-p record)
                (consp (fn-replay-apply-record node record)))
           (equal
            (fn-articles-msgid-stamps
             (fn-state-articles
              (fn-node-acceptance (fn-replay-apply-record node record))))
            (append
             (fn-articles-msgid-stamps
              (fn-state-articles (fn-node-acceptance node)))
             (fn-replay-journal-article-stamps (list record)))))
  :hints (("Goal" :do-not-induct t
           :use (fn-stamp-apply-article-adds-journal-pair
                 fn-stamp-apply-retention-event-keeps-articles
                 fn-stamp-apply-identity-neutral-keeps-articles)
           :in-theory (e/d (fn-replay-apply-record
                            fn-replay-journal-article-stamps
                            fn-replay-article-eventp)
                           (fn-record-shape-vocabulary
                            fn-stxe-p fn-stxk-p fn-stxa-p
                            fn-store-retention-event-p))))
  :rule-classes :rewrite)

(local
 (defthm fn-stamp-append-one-then-rest
   (equal (append (append xs (list x)) rest)
          (append xs (cons x rest)))
   :hints (("Goal" :use ((:instance fn-record-append-associative
                                     (a xs) (b (list x)) (c rest)))))))

(defthm fn-replay-loop-article-stamps-are-the-journal-stamps
  (implies (and (fn-node-statep node)
                (equal (fn-replay-result-kind
                        (fn-replay-loop node records expected-sequence)) :ok))
           (equal
            (fn-articles-msgid-stamps
             (fn-state-articles
              (fn-node-acceptance
               (fn-replay-result-node
                (fn-replay-loop node records expected-sequence)))))
            (append
             (fn-articles-msgid-stamps
              (fn-state-articles (fn-node-acceptance node)))
             (fn-replay-journal-article-stamps records))))
  :hints (("Goal" :induct (fn-replay-loop node records expected-sequence)
           :in-theory (e/d (fn-replay-loop
                            fn-replay-journal-article-stamps)
                           (fn-record-shape-vocabulary
                            fn-replay-apply-record
                            fn-store-event-p fn-node-statep
                            fn-replay-okp
                            fn-replay-article-eventp
                            fn-replay-article-record
                            fn-replay-composite-record
                            fn-stxa-p fn-stxe-p fn-stxk-p
                            fn-store-retention-event-p))))
  :rule-classes nil)

(defthm fn-replay-article-stamps-are-the-journal-stamps
  (implies (fn-replay-okp (fn-replay groups capacity records))
           (equal
            (fn-articles-msgid-stamps
             (fn-state-articles
              (fn-node-acceptance
               (fn-replay-result-node (fn-replay groups capacity records)))))
            (fn-replay-journal-article-stamps records)))
  :hints (("Goal"
           :use ((:instance fn-replay-loop-article-stamps-are-the-journal-stamps
                            (node (fn-node-initial-state groups capacity))
                            (expected-sequence 0)))
           :in-theory (e/d (fn-replay fn-replay-okp
                            fn-node-initial-state fn-initial-state
                            fn-articles-msgid-stamps)
                           (fn-replay-loop))))
  :rule-classes nil)
