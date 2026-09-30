; served-catalog-join-host-identity-finish.lisp -- the catalog join carried
; across the host's identity finish with its pending row (lane join-f2-2,
; 2026-09-29; PRF-302).
;
; host/owner-host.lisp fn-owner-finish-identity: fn-owner-finish installs
; fn-rix-ocfg-complete's owner and answers :durable when the store went from
; :completing to :ready; with a pending row the catalog then runs
; fn-sca-finish with the token read off the completion before the finish.
; books/served-catalog-join-inv.lisp fn-scj-invp-at-identity-finish took the
; signed composite's acceptance and verdict equations as hypotheses; here
; they are derived from the store's identity completion
; (fn-sjh-idf-finish-equations): the node conses exactly the composite's
; held article, and the verdicts gain exactly the pair of the composite's
; verdict statement, whose Message-ID is the article's (fn-stxa-bindsp; the
; row's article is the composite's record, fn-row-composite-okp).  The
; KEYSTONE is fn-sjh-okp-at-owner-finish-identity: every branch of the
; host's identity finish keeps fn-sjh-okp.

(in-package "ACL2")

(include-book "served-catalog-join-host-complete")
(include-book "served-catalog-join-host-identity")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The node: a retained composite row completes by the article step over its
; held article, which conses one article carrying the held row's Message-ID.

(defthm fn-sjh-idf-node-of-finish
  (let ((r (fn-ccar-completion-record s)))
    (implies (fn-evc-stxap r)
             (equal (fn-sn-node (fn-ccar-sn-finish-enabled s))
                    (fn-replay-apply-record (fn-sn-node s) r))))
  :hints (("Goal" :in-theory (e/d (fn-ccar-sn-finish-enabled fn-sn-finish-identity
                                   fn-sn-advance-identity-next fn-sn-with-topic fn-sn-with-consumer
                                   fn-evc-retentionp fn-evc-consumerp fn-evc-topicp fn-evc-stxap)
                                  (fn-sn-make-v6 fn-node-complete fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-sf-core-completion
                                   fn-sf-emit-success fn-stx-index-add fn-ccar-accepted-delta
                                   fn-ccar-cpe-projection-step fn-ccar-th-prefix-step
                                   fn-replay-identity-step fn-replay-verdict-pairs
                                   fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp fn-hstxa-p
                                   fn-evc-stxep fn-evc-stxkp fn-ccar-completion-record))
           :use ((:instance fn-hstxa-is-no-wire-event (x (fn-ccar-completion-record s)))))))

(defthm fn-sjh-idf-prepare-matched-facts
  (implies (fn-node-pending-matchesp (fn-node-prepare node generation msgid payload groups
                                                      obligation-id subject evidence charge stamp binding)
                                     txid gen2)
           (let ((p (fn-node-prepare node generation msgid payload groups
                                     obligation-id subject evidence charge stamp binding)))
             (implies (null (fn-node-stage node))
                      (and (equal (fn-state-articles (fn-node-acceptance p))
                                  (fn-state-articles (fn-node-acceptance node)))
                           (equal (fn-pending-msgid (fn-state-pending (fn-node-acceptance p))) msgid)))))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare fn-accept-prepare fn-node-pending-matchesp)
                                  (fn-retain-admissiblep fn-retain-admit fn-allocate-memberships
                                   fn-selection-validp fn-acceptedp fn-pending-matchesp)))))

(defthm fn-sjh-idf-advance-keeps-articles
  (equal (fn-state-articles (fn-node-acceptance (fn-replay-advance-txid node txid)))
         (fn-state-articles (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-sjh-idf-advance-stage
  (implies (not (equal (fn-replay-advance-txid node txid) node))
           (null (fn-node-stage (fn-replay-advance-txid node txid))))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-sjh-idf-install-pending-articles
  (implies (fn-statep s)
           (equal (fn-state-articles (fn-install-pending s))
                  (cons (fn-article-from-pending (fn-state-pending s)) (fn-state-articles s))))
  :hints (("Goal" :in-theory (e/d (fn-install-pending) (fn-article-from-pending fn-statep)))))

(defthm fn-sjh-idf-article-from-pending-msgid
  (equal (fn-article-msgid (fn-article-from-pending p)) (fn-pending-msgid p))
  :hints (("Goal" :in-theory (enable fn-article-from-pending fn-make-article fn-article-msgid
                                     fn-pending-msgid))))

(defthm fn-sjh-idf-matched-acceptance-statep
  (implies (fn-node-pending-matchesp p txid gen)
           (fn-statep (fn-node-acceptance p)))
  :hints (("Goal" :in-theory (enable fn-node-pending-matchesp fn-node-statep))))

(defthm fn-sjh-idf-complete-prepare-articles
  (implies (and (null (fn-node-stage n))
                (fn-node-pending-matchesp (fn-node-prepare n g m pl gr o su e c st binding) tx g2))
           (let ((after (fn-node-complete (fn-node-prepare n g m pl gr o su e c st binding) tx g2 :durable)))
             (and (equal (fn-state-articles (fn-node-acceptance after))
                         (cons (car (fn-state-articles (fn-node-acceptance after)))
                               (fn-state-articles (fn-node-acceptance n))))
                  (equal (fn-article-msgid (car (fn-state-articles (fn-node-acceptance after)))) m))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-idf-article-from-pending-msgid car-cons cdr-cons)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-idf-prepare-matched-facts (node n) (generation g) (msgid m) (payload pl)
                            (groups gr) (obligation-id o) (subject su) (evidence e) (charge c) (stamp st)
                            (txid tx) (gen2 g2))
                 (:instance fn-sjh-idf-matched-acceptance-statep
                            (p (fn-node-prepare n g m pl gr o su e c st binding)) (txid tx) (gen g2))
                 (:instance fn-scj-node-complete-articles
                            (node (fn-node-prepare n g m pl gr o su e c st binding)) (txid tx) (generation g2))))))

(defthm fn-sjh-idf-apply-composite-articles
  (let ((after (fn-replay-apply-record node r)))
    (implies (and (fn-hstxa-p r) (consp after))
             (and (equal (fn-state-articles (fn-node-acceptance after))
                         (cons (car (fn-state-articles (fn-node-acceptance after)))
                               (fn-state-articles (fn-node-acceptance node))))
                  (equal (fn-article-msgid (car (fn-state-articles (fn-node-acceptance after))))
                         (fn-record-msgid (fn-hstxa-held r))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-replay-apply-record fn-replay-composite-held)
                           (fn-node-prepare fn-node-complete fn-node-pending-matchesp fn-replay-advance-txid
                            fn-hstxa-p fn-stxe-p fn-stxk-p fn-cpe-eventp fn-th-topic-eventp
                            fn-store-retention-event-p fn-held-p fn-article-from-pending))
           :use ((:instance fn-hstxa-is-no-wire-event (x r))
                 (:instance fn-sjh-idf-advance-stage (txid (fn-store-event-txid r)))
                 (:instance fn-sjh-idf-complete-prepare-articles
                            (n (fn-replay-advance-txid node (fn-store-event-txid r)))
                            (g (fn-record-generation (fn-hstxa-held r)))
                            (m (fn-record-msgid (fn-hstxa-held r)))
                            (pl (fn-record-payload (fn-hstxa-held r)))
                            (gr (fn-record-groups (fn-hstxa-held r)))
                            (o (fn-record-obligation-id (fn-hstxa-held r)))
                            (su (fn-record-content-subject (fn-hstxa-held r)))
                            (e (fn-record-release-evidence (fn-hstxa-held r)))
                            (c (fn-record-charge (fn-hstxa-held r)))
                            (st (fn-record-stamp (fn-hstxa-held r)))
                            (tx (fn-record-txid (fn-hstxa-held r)))
                            (g2 (fn-record-generation (fn-hstxa-held r))))))))

; -----------------------------------------------------------------------------
; The verdicts: the identity step of a retained composite records exactly its
; verdict statement, whose Message-ID is the composite's article's.

(defthm fn-sjh-idf-identity-step-verdicts
  (let* ((w (fn-hstxa-stxa r))
         (e (fn-stmt-value (fn-stxe-decode-exact (fn-stxa-verdict-event w))))
         (ctx2 (fn-replay-identity-step ctx r)))
    (implies (and (fn-hstxa-p r)
                  (equal (fn-stxk-context-kind ctx) :ok)
                  (equal (fn-stxk-context-kind ctx2) :ok))
             (and (equal (fn-stxk-context-verdicts ctx2) (cons e (fn-stxk-context-verdicts ctx)))
                  (fn-stxe-p e)
                  (fn-stxa-bindsp w))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-replay-identity-step fn-replay-identity-wire fn-stxk-apply-verdict
                            fn-replay-apply-carried-verdict fn-replay-apply-revoked-verdict fn-stxk-fault
                            fn-stxk-context
                            fn-hsig-article-event-carried-bindsp fn-hsig-article-event-revoked-bindsp)
                           (fn-stxa-p fn-stxe-p fn-stxk-p fn-hstxa-p fn-stxa-bindsp fn-stxk-apply-snapshot
                            fn-hsig-article-event-snapshot-bindsp fn-stxe-decode-exact
                            fn-hsig-revoked-tombstone-bindsp
                            fn-stxk-find fn-hsig-carried-record-metadatap fn-hc-received-plan))
           :use ((:instance fn-hstxa-p-fields (x r))
                 (:instance fn-stxa-is-no-other-wire-event (x (fn-hstxa-stxa r)))))))

(defthm fn-sjh-idf-composite-verdict-msgid
  (implies (fn-stxa-bindsp w)
           (equal (fn-stxe-msgid (fn-stmt-value (fn-stxe-decode-exact (fn-stxa-verdict-event w))))
                  (fn-record-msgid (fn-replay-composite-record w))))
  :hints (("Goal" :in-theory (e/d (fn-stxa-bindsp fn-replay-composite-record)
                                  (fn-stxe-decode-exact fn-record-p fn-stxe-p fn-stxa-p)))))

(defthm fn-sjh-idf-row-wire-of-held-msgid
  (implies (fn-held-p h)
           (equal (fn-record-msgid (fn-row-wire-of h fn-arena)) (fn-record-msgid h)))
  :hints (("Goal" :in-theory (e/d (fn-row-wire-of) (fn-held-p fn-held-wire)))))

(defthm fn-sjh-idf-verdict-pairs-of-one
  (implies (fn-stxe-p e)
           (equal (fn-replay-verdict-pairs (list e))
                  (list (cons (fn-stxe-msgid e)
                              (fn-stx-make-verdict (fn-stxe-token e) (fn-stxe-detail e)
                                                   (fn-stxe-keyring-generation e))))))
  :hints (("Goal" :expand ((fn-replay-verdict-pairs (list e)) (fn-replay-verdict-pairs nil))
           :in-theory (disable fn-stxe-p))))

(defthm fn-sjh-idf-verdicts-of-finish
  (let ((r (fn-ccar-completion-record s)))
    (implies (fn-evc-stxap r)
             (equal (fn-sn-verdicts (fn-ccar-sn-finish-enabled s))
                    (append (fn-replay-verdict-pairs
                             (fn-stxk-context-verdicts
                              (fn-replay-identity-step (fn-sn-identity-context s) r)))
                            (fn-sn-verdicts s)))))
  :hints (("Goal" :in-theory (e/d (fn-ccar-sn-finish-enabled fn-sn-finish-identity
                                   fn-sn-with-topic fn-sn-with-consumer
                                   fn-evc-retentionp fn-evc-consumerp fn-evc-topicp fn-evc-stxap)
                                  (fn-sn-make-v6 fn-node-complete fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-sf-core-completion
                                   fn-sf-emit-success fn-stx-index-add fn-ccar-accepted-delta
                                   fn-ccar-cpe-projection-step fn-ccar-th-prefix-step
                                   fn-replay-identity-step fn-replay-verdict-pairs
                                   fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp fn-hstxa-p
                                   fn-evc-stxep fn-evc-stxkp fn-ccar-completion-record fn-sn-identity-context))
           :use ((:instance fn-hstxa-is-no-wire-event (x (fn-ccar-completion-record s)))))))

(defthm fn-sjh-idf-identity-context-facts
  (and (equal (fn-stxk-context-kind (fn-sn-identity-context s)) :ok)
       (equal (fn-stxk-context-verdicts (fn-sn-identity-context s)) nil))
  :hints (("Goal" :in-theory (enable fn-sn-identity-context fn-stxk-context))))

(defthm fn-sjh-idf-core-enabled-ok
  (let ((r (fn-ccar-completion-record s)))
    (implies (and (fn-ccar-completion-core-enabledp s) (fn-evc-stxap r))
             (and (consp (fn-replay-apply-record (fn-sn-node s) r))
                  (equal (fn-stxk-context-kind (fn-replay-identity-step (fn-sn-identity-context s) r)) :ok))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-ccar-completion-core-enabledp fn-evc-retentionp fn-evc-stxap)
                                             (theory 'minimal-theory))
           :use ((:instance fn-hstxa-is-no-wire-event (x (fn-ccar-completion-record s)))))))

; The signed composite's acceptance and verdict equations (the (I)
; hypotheses of fn-scj-invp-at-identity-finish), from the store alone.
(defthm fn-sjh-idf-finish-equations
  (let* ((r (fn-ccar-completion-record s))
         (s2 (fn-ccar-sn-finish-enabled s))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (a (car (fn-state-articles acc2))))
    (implies (and (fn-ccar-completion-enabledp s)
                  (fn-evc-stxap r)
                  (fn-row-composite-okp r fn-arena))
             (and (equal (fn-state-articles acc2)
                         (cons a (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
                  (equal (fn-sn-verdicts s2)
                         (cons (cons (fn-article-msgid a) (cdr (car (fn-sn-verdicts s2))))
                               (fn-sn-verdicts s))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-evc-stxap fn-row-composite-okp fn-sjh-idf-row-wire-of-held-msgid
                                        fn-hstxa-p-fields fn-sjh-idf-verdict-pairs-of-one
                                        fn-sjh-idf-identity-context-facts
                                        car-cons cdr-cons (:d append) (:e append)
                                        fn-ccar-completion-enabledp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-idf-node-of-finish)
                 (:instance fn-sjh-idf-core-enabled-ok)
                 (:instance fn-sjh-idf-apply-composite-articles (node (fn-sn-node s))
                            (r (fn-ccar-completion-record s)))
                 (:instance fn-sjh-idf-verdicts-of-finish)
                 (:instance fn-sjh-idf-identity-step-verdicts (r (fn-ccar-completion-record s))
                            (ctx (fn-sn-identity-context s)))
                 (:instance fn-sjh-idf-composite-verdict-msgid
                            (w (fn-hstxa-stxa (fn-ccar-completion-record s))))))))

; -----------------------------------------------------------------------------
; The invariant across the identity finish, with (I) discharged.

(defthm fn-sjh-idf-invp-at-finish
  (let* ((s (fn-own-store o))
         (r (fn-ccar-completion-record s))
         (view (fn-own-view o))
         (o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (events2 (append events0 (list event)))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid held)
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (and (fn-ccar-completion-enabledp s)
                  (fn-evc-stxap r)
                  (fn-row-composite-okp r fn-arena)
                  (fn-scj-invp o fn-arena fn-cat)
                  (fn-scar-view-indexedp o)
                  (fn-scj-rows-invp fn-cat events0)
                  (true-listp events0)
                  (fn-cst-relation s2)
                  (fn-own-store-idlep s2)
                  (equal (fn-sf-records (fn-sn-files s2)) events2)
                  (fn-rows-composites-okp events2 fn-arena)
                  (fn-scj-rows-clearp events2)
                  (equal (fn-scj-load-h event) held)
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (len fn-cat))
                  (equal (fn-state-articles (fn-own-view-archive view))
                         (fn-ctl-visible-articles (fn-own-view-raw view)
                                                  (fn-own-view-withdrawals view)
                                                  (fn-own-view-verdicts view)))
                  (equal (fn-state-articles (fn-own-view-archive view2))
                         (fn-ctl-visible-articles (fn-state-articles acc2)
                                                  (fn-own-view-withdrawals view2)
                                                  (fn-own-view-verdicts view2)))
                  (<= (nfix (fn-own-view-version view)) (len events0))
                  (fn-scj-seqs-sortedp fn-cat)
                  (fn-cnx-freshp fn-cat)
                  (fn-scj-conns-versions-atmostp (fn-own-conns o) (fn-own-view-version view))
                  (fn-scj-view-indexesp view2)
                  (fn-statep (fn-own-view-archive view2)))
             (and (fn-scj-invp o2 fn-arena c2)
                  (fn-scj-seqs-sortedp c2)
                  (fn-cnx-freshp c2))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(car-cons) (theory 'minimal-theory))
           :use ((:instance fn-scj-invp-at-host-finish
                            (verdict (cdr (car (fn-sn-verdicts (fn-ccar-sn-finish-enabled (fn-own-store o)))))))
                 (:instance fn-scj-invp-gives-vvp)
                 (:instance fn-scj-vvp-parts)
                 (:instance fn-scj-host-finish-store)
                 (:instance fn-sjh-idf-finish-equations (s (fn-own-store o)))))))

(defthm fn-sjh-idf-invp-at-finish-carried
  (let* ((s (fn-own-store o))
         (r (fn-ccar-completion-record s))
         (records (fn-sf-records (fn-sn-files s)))
         (event (car (last records)))
         (view (fn-own-view o))
         (o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid held)
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (and (fn-ccar-completion-enabledp s)
                  (fn-evc-stxap r)
                  (fn-row-composite-okp r fn-arena)
                  (fn-scj-invp o fn-arena fn-cat)
                  (fn-scjs-seenp o)
                  (fn-scjs-historyp o)
                  (consp records)
                  (fn-scar-view-indexedp o)
                  (fn-cst-relation s2)
                  (fn-own-store-idlep s2)
                  (fn-rows-composites-okp records fn-arena)
                  (fn-scj-rows-clearp records)
                  (equal (fn-scj-load-h event) held)
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (len fn-cat))
                  (equal (fn-state-articles (fn-own-view-archive view))
                         (fn-ctl-visible-articles (fn-own-view-raw view)
                                                  (fn-own-view-withdrawals view)
                                                  (fn-own-view-verdicts view)))
                  (equal (fn-state-articles (fn-own-view-archive view2))
                         (fn-ctl-visible-articles (fn-state-articles acc2)
                                                  (fn-own-view-withdrawals view2)
                                                  (fn-own-view-verdicts view2)))
                  (fn-scj-seqs-sortedp fn-cat)
                  (fn-cnx-freshp fn-cat)
                  (fn-scj-versions-okp o)
                  (fn-scj-view-indexesp view2)
                  (fn-statep (fn-own-view-archive view2)))
             (and (fn-scj-invp o2 fn-arena c2)
                  (fn-scj-seqs-sortedp c2)
                  (fn-cnx-freshp c2))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-versions-okp fn-scjs-historyp fn-scj-true-listp-butlast
                                        nfix natp (:type-prescription len))
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-enabled-is-completing (s (fn-own-store o)))
                 (:instance fn-scjs-rows-invp-before-in-flight)
                 (:instance fn-scj-host-finish-store)
                 (:instance fn-scj-records-kept-by-ccar-finish (s (fn-own-store o)))
                 (:instance fn-scj-snoc-of-butlast-last (r (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-sjh-idf-invp-at-finish
                            (events0 (butlast (fn-sf-records (fn-sn-files (fn-own-store o))) 1))
                            (event (car (last (fn-sf-records (fn-sn-files (fn-own-store o)))))))))))

; -----------------------------------------------------------------------------
; The premises from fn-sjh-okp: LINK names the completion as the last record,
; whose composite fact S carries.

(defthm fn-sjh-idf-composite-okp-of-last
  (implies (and (fn-rows-composites-okp rows fn-arena) (consp rows))
           (fn-row-composite-okp (car (last rows)) fn-arena))
  :hints (("Goal" :induct (fn-rows-composites-okp rows fn-arena)
           :in-theory (e/d (fn-rows-composites-okp) (fn-row-composite-okp)))))

(defthm fn-sjh-idf-linkp-at-completing
  (implies (and (fn-sjh-linkp o pending fn-arena fn-cat)
                (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :completing))
           (and (consp (fn-sf-records (fn-sn-files (fn-own-store o))))
                (equal (fn-sf-completion (fn-sn-files (fn-own-store o)))
                       (fn-sf-record-pair (car (last (fn-sf-records (fn-sn-files (fn-own-store o)))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-linkp fn-sjh-files-linkp fn-sjh-inflight
                                               (:e fn-sf-record-phasep) (:e equal))
                                             (theory 'minimal-theory)))))

(defthm fn-sjh-idf-completion-record-is-last
  (implies (and (fn-sjh-linkp o pending fn-arena fn-cat)
                (fn-ccar-completion-enabledp (fn-own-store o)))
           (equal (fn-ccar-completion-record (fn-own-store o))
                  (car (last (fn-sf-records (fn-sn-files (fn-own-store o)))))))
  :hints (("Goal" :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-scj-enabled-is-completing (s (fn-own-store o)))
                 (:instance fn-sjh-idf-linkp-at-completing)
                 (:instance fn-ccar-enabled-finds-a-store-event (s (fn-own-store o)))
                 (:instance fn-sjh-completion-record-is-last (s (fn-own-store o)))))))

(defun-nx fn-sjh-idf-premisesp (o cfg fn-arena fn-cat pending token)
  (let* ((s (fn-own-store o))
         (r (fn-ccar-completion-record s))
         (records (fn-sf-records (fn-sn-files s)))
         (event (car (last records)))
         (view (fn-own-view o))
         (o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (held (fn-pc-held pending)))
    (and (fn-ccar-completion-enabledp s)
         (fn-evc-stxap r)
         (fn-row-composite-okp r fn-arena)
         (fn-scj-invp o fn-arena fn-cat)
         (fn-scjs-seenp o)
         (fn-scjs-historyp o)
         (consp records)
         (fn-scar-view-indexedp o)
         (fn-cst-relation s2)
         (fn-own-store-idlep s2)
         (fn-rows-composites-okp records fn-arena)
         (fn-rows-handles-inp records fn-arena)
         (fn-scj-rows-clearp records)
         (equal (fn-scj-load-h event) held)
         (fn-pc-p pending)
         (equal token (fn-pc-token pending))
         (equal (fn-pc-expected pending) (len fn-cat))
         (equal (fn-state-articles (fn-own-view-archive view))
                (fn-ctl-visible-articles (fn-own-view-raw view)
                                         (fn-own-view-withdrawals view)
                                         (fn-own-view-verdicts view)))
         (equal (fn-state-articles (fn-own-view-archive view2))
                (fn-ctl-visible-articles (fn-state-articles acc2)
                                         (fn-own-view-withdrawals view2)
                                         (fn-own-view-verdicts view2)))
         (fn-scj-seqs-sortedp fn-cat)
         (fn-cnx-freshp fn-cat)
         (fn-scj-versions-okp o)
         (fn-scj-view-indexesp view2)
         (fn-statep (fn-own-view-archive view2)))))

(defthm fn-sjh-idf-premises-of-okp
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending))))
    (implies (and (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  pending
                  (fn-ccar-completion-enabledp s)
                  (fn-evc-stxap (fn-ccar-completion-record s)))
             (fn-sjh-idf-premisesp o cfg fn-arena fn-cat pending token)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-idf-premisesp fn-sjh-ocfg-owner-of-with-owner
                                        fn-ccar-ocl-relation-carries-sn-statep
                                        fn-sjh-ocl-gives-visible
                                        fn-sjh-invp-gives-view-gidx fn-sjh-finish-keeps-view-gidx
                                        fn-sjh-finish-keeps-view-indexed fn-sjh-view-indexesp-of-parts
                                        fn-sjh-completion-record-needs-records
                                        fn-sjh-linkp-at-enabled-completion (:e fn-evc-stxap))
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-finish-store-image (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-completion-record-needs-records (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-sjh-idf-completion-record-is-last (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-idf-composite-okp-of-last
                            (rows (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                 (:instance fn-ocmt-post-commit-preserves-ocl-relation)
                 (:instance fn-sjh-ocl-gives-cst
                            (oc (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                 (:instance fn-sjh-ocl-gives-visible
                            (oc (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                 (:instance fn-sjh-ocl-gives-view-statep
                            (oc (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                 (:instance fn-scj-vvp-of-host-finish (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-vvp-parts (o (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena))))))))

(defthm fn-sjh-idf-carried-by-premises
  (let* ((o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (view2 (fn-own-view o2))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (fn-sjh-idf-premisesp o cfg fn-arena fn-cat pending token)
             (and (fn-scj-invp o2 fn-arena c2)
                  (fn-scj-seqs-sortedp c2)
                  (fn-cnx-freshp c2))))
  :hints (("Goal" :in-theory '(fn-sjh-idf-premisesp)
           :use ((:instance fn-sjh-idf-invp-at-finish-carried)))))

(defthm fn-sjh-idf-premises-facts
  (implies (fn-sjh-idf-premisesp o cfg fn-arena fn-cat pending token)
           (let ((records (fn-sf-records (fn-sn-files (fn-own-store o)))))
             (and (fn-ccar-completion-enabledp (fn-own-store o))
                  (fn-scjs-historyp o)
                  (fn-scj-versions-okp o)
                  (fn-scar-view-indexedp o)
                  (fn-rows-composites-okp records fn-arena)
                  (fn-rows-handles-inp records fn-arena)
                  (fn-scj-rows-clearp records)
                  (fn-pc-p pending)
                  (equal (fn-pc-token pending) token)
                  (equal (fn-pc-expected pending) (len fn-cat)))))
  :hints (("Goal" :in-theory '(fn-sjh-idf-premisesp))))

(defthm fn-sjh-idf-okp-after-by-premises
  (let* ((o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (view2 (fn-own-view o2))
         (fin (fn-sca-finish token pending (fn-own-view-index view2)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view2))
                             fn-cat)))
    (implies (fn-sjh-idf-premisesp o cfg fn-arena fn-cat pending token)
             (and (equal (mv-nth 1 fin) nil)
                  (fn-sjh-okp o2 nil fn-arena (mv-nth 2 fin)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-okp-when-parts fn-sjh-idf-premises-facts fn-sjh-pc-p-non-nil
                                        fn-sjh-idf-carried-by-premises fn-sjh-finish-side-facts
                                        fn-sjh-finish-keeps-view-indexed fn-sjh-sca-finish-clears-pending)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-finish-store-image)
                 (:instance fn-sjh-idf-premises-facts)))))

; -----------------------------------------------------------------------------
; An article row at the identity finish: the article premises from an enabled
; completion of a held row (the host's word is the phase test, not
; fn-own-finish's).

(defthm fn-sjh-idf-stxe-shape
  (implies (fn-stxe-p x)
           (and (consp x) (natp (car x)) (equal (len x) 8)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-stxe-p fn-stxe-shapep fn-record-uint32p fn-stxe-sequence natp len))))

(defthm fn-sjh-idf-stxe-loads-no-row
  (implies (fn-stxe-p w) (not (fn-scj-load-h w)))
  :hints (("Goal" :in-theory (e/d (fn-scj-load-h fn-sca-composite-shapep fn-held-shapep fn-cat-rowp)
                                  (fn-stxe-p))
           :use ((:instance fn-sjh-idf-stxe-shape (x w))))))

(defthm fn-sjh-idf-loaded-event-kind
  (implies (and (fn-store-event-p r) (fn-scj-load-h r))
           (or (fn-held-p r) (fn-hstxa-p r)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-store-event-p)
                                  (fn-held-p fn-hstxa-p fn-cat-rowp fn-scj-load-h))
           :use ((:instance fn-sjh-other-event-row-facts (e r))
                 (:instance fn-sjh-idf-stxe-loads-no-row (w r))
                 (:instance fn-sjh-stxk-row-facts (w r))))))

(defthm fn-sjh-idf-pc-held-non-nil
  (implies (fn-pc-p pc) (fn-pc-held pc))
  :rule-classes nil
  :hints (("Goal" :in-theory '((:e fn-held-p)) :use ((:instance fn-pc-p-fields)))))

(defthm fn-sjh-idf-article-premises-of-okp
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending))))
    (implies (and (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  pending
                  (fn-ccar-completion-enabledp s)
                  (fn-held-p (fn-ccar-completion-record s)))
             (fn-sjh-finish-premisesp o cfg fn-arena fn-cat pending token)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-finish-premisesp fn-sjh-ocfg-owner-of-with-owner
                                        (:executable-counterpart fn-held-p)
                                        fn-ccar-ocl-relation-carries-sn-statep
                                        fn-sjh-held-row-is-no-other-event
                                        fn-sjh-ocl-acceptance-statep
                                        fn-sjh-ocl-gives-visible
                                        fn-sjh-invp-gives-view-gidx fn-sjh-finish-keeps-view-gidx
                                        fn-sjh-finish-keeps-view-indexed fn-sjh-view-indexesp-of-parts
                                        fn-sjh-completion-record-needs-records
                                        fn-sjh-linkp-at-enabled-completion)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-finish-store-image (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-completion-record-needs-records (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-ocmt-post-commit-preserves-ocl-relation)
                 (:instance fn-sjh-ocl-gives-cst
                            (oc (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                 (:instance fn-sjh-ocl-gives-visible
                            (oc (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                 (:instance fn-sjh-ocl-gives-view-statep
                            (oc (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                 (:instance fn-scj-vvp-of-host-finish (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-vvp-parts (o (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena))))))))

; -----------------------------------------------------------------------------
; The host's branches.

(defthm fn-sjh-idf-finish-not-enabled
  (implies (not (fn-ccar-completion-enabledp (fn-own-store o)))
           (equal (cdr (fn-ccar-own-finish o cfg fn-arena)) o))
  :hints (("Goal" :in-theory (e/d (fn-ccar-own-finish-is-own-finish fn-own-finish fn-own-complete
                                   fn-ccar-completion-enabledp-is-reference)
                                  (fn-sn-completion-enabledp fn-ccar-completion-enabledp)))))

(defthm fn-sjh-idf-rix-staged-owner
  (implies (fn-ocfg-staged oc)
           (equal (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist)) (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (enable fn-rix-ocfg-complete))))

(defthm fn-sjh-idf-enabled-completion-consp
  (implies (fn-ccar-completion-enabledp s)
           (consp (fn-sf-completion (fn-sn-files s))))
  :hints (("Goal" :in-theory (e/d (fn-ccar-completion-enabledp fn-ccar-completion-core-enabledp)
                                  (fn-ccar-completion-record fn-sn-statep fn-evc-sequence fn-evc-txid
                                   fn-replay-apply-record fn-replay-identity-step fn-replay-apply-retention-event
                                   fn-ccar-sn-record-bindsp fn-ccar-cpe-projection-step fn-ccar-th-prefix-step fn-ccar-completion-enabledp-is-reference fn-ccar-completion-core-enabledp-is-reference)))))

(defthm fn-sjh-idf-durable-is-enabled
  (let* ((o (fn-ocfg-owner oc))
         (o2 (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist))))
    (implies (and (fn-hist-of-storep fn-hist (fn-own-store o))
                  (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :completing)
                  (equal (fn-sf-phase (fn-sn-files (fn-own-store o2))) :ready))
             (and (not (fn-ocfg-staged oc))
                  (fn-ccar-completion-enabledp (fn-own-store o)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-idf-rix-staged-owner fn-sjh-idf-finish-not-enabled)
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-rix-complete-owner (cfg nil))))))

(defthm fn-sjh-idf-row-kind
  (let ((s (fn-own-store (fn-ocfg-owner oc))))
    (implies (and (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                  pending
                  (fn-ccar-completion-enabledp s))
             (or (fn-held-p (fn-ccar-completion-record s))
                 (fn-evc-stxap (fn-ccar-completion-record s)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-evc-stxap fn-pc-p-fields (:e fn-held-p))
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-linkp-at-enabled-completion (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-idf-pc-held-non-nil (pc pending))
                 (:instance fn-sjh-idf-completion-record-is-last (o (fn-ocfg-owner oc)))
                 (:instance fn-ccar-enabled-finds-a-store-event (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-sjh-idf-loaded-event-kind
                            (r (fn-ccar-completion-record (fn-own-store (fn-ocfg-owner oc)))))))))

(defthm fn-sjh-idf-okp-with-row
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (view2 (fn-own-view o2))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (fin (fn-sca-finish token pending (fn-own-view-index view2)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view2))
                             fn-cat)))
    (implies (and (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  pending
                  (fn-ccar-completion-enabledp s))
             (and (equal (mv-nth 1 fin) nil)
                  (fn-sjh-okp o2 nil fn-arena (mv-nth 2 fin)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-sjh-idf-row-kind)
                 (:instance fn-sjh-idf-article-premises-of-okp)
                 (:instance fn-sjh-idf-premises-of-okp)
                 (:instance fn-sjh-okp-after-finish-by-premises (o (fn-ocfg-owner oc))
                            (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                                         (fn-pc-expected pending))))
                 (:instance fn-sjh-idf-okp-after-by-premises (o (fn-ocfg-owner oc))
                            (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                                         (fn-pc-expected pending))))))))

; KEYSTONE (the join carried across the host's identity finish).
; host/owner-host.lisp fn-owner-finish-identity: fn-owner-finish installs
; fn-rix-ocfg-complete's owner (the history stobj synchronized to the store
; first) and answers :durable exactly when the store went from :completing to
; :ready (fn-owner-finish-synced; the ledger conjunct it also tests is not
; needed); with :durable, a pending row and a completion pair it runs
; fn-sca-finish with the token read off the completion before the finish and
; keeps the pending row fn-sca-finish answers, else it keeps both.  Under
; fn-sjh-okp before and the owner relation, fn-sjh-okp holds after with the
; pending row the host keeps, on every branch: a signed composite's row (the
; (I) equations derived above), an article row, a completion with no row
; (fn-sjh-okp-at-owner-finish-no-row), and a finish that changed nothing
; (a staged configuration, no enabled completion).  The view's archive after
; is a state: fn-ocl-relation after carries it (fn-acar-ocl-relation-
; carries-view-statep), row Q3c.
(defthm fn-sjh-okp-at-owner-finish-identity
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (completion (fn-sf-completion (fn-sn-files s)))
         (o2 (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist)))
         (view2 (fn-own-view o2))
         (durablep (and (equal (fn-sf-phase (fn-sn-files s)) :completing)
                        (equal (fn-sf-phase (fn-sn-files (fn-own-store o2))) :ready)))
         (fin (fn-sca-finish (cons (nfix (cdr completion)) (fn-pc-expected pending))
                             pending (fn-own-view-index view2)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view2))
                             fn-cat)))
    (implies (and (fn-hist-of-storep fn-hist s)
                  (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (fn-statep (fn-own-view-archive view2)))
             (if (and durablep pending (consp completion))
                 (and (equal (mv-nth 1 fin) nil)
                      (fn-sjh-okp o2 nil fn-arena (mv-nth 2 fin)))
               (fn-sjh-okp o2 pending fn-arena fn-cat))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-ocfg-staged oc)
                   (not (fn-ccar-completion-enabledp (fn-own-store (fn-ocfg-owner oc))))
                   (not (and (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) :completing)
                             (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner
                                                                            (fn-rix-ocfg-complete oc fn-hist)))))
                                    :ready))))
           :in-theory (union-theories '(fn-sjh-idf-rix-staged-owner fn-sjh-idf-finish-not-enabled
                                        fn-sjh-idf-enabled-completion-consp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-idf-durable-is-enabled)
                 (:instance fn-scj-enabled-is-completing (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-sjh-finish-store-image (o (fn-ocfg-owner oc)) (cfg nil))
                 (:instance fn-sjh-rix-complete-owner (cfg nil))
                 (:instance fn-sjh-idf-okp-with-row (cfg nil))
                 (:instance fn-sjh-okp-at-owner-finish-no-row)))))
