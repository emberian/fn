; served-catalog-join-host-finish.lisp -- the catalog join carried across
; the host's article finish (lane join-f2, 2026-09-28; PRF-302).
;
; host/owner-host.lisp fn-owner-finish-submission-synced: the owner's finish
; fn-apc-own-finish, and when it answers :durable with a pending row held,
; fn-sca-finish with the token the host reads off the store's completion, the
; refreshed view's index and the targets its withdrawals name.  Every
; hypothesis of books/served-catalog-join-inv.lisp's
; fn-scj-invp-at-host-article-finish-carried is derived here from
; fn-sjh-okp (books/served-catalog-join-host.lisp), the owner relation the
; host's owner satisfies and the finish's word.

(in-package "ACL2")

(include-book "served-catalog-join-host")
(include-book "owner-parse-carried") ; fn-apc-own-finish: the finish the host calls

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The host's article finish (host/owner-host.lisp fn-owner-finish-submission-
; synced): the owner's finish fn-apc-own-finish, and when it answers :durable
; and a pending row is held, fn-sca-finish with the token the host reads off
; the store's completion, the refreshed view's index and the targets its
; withdrawals name.  The facts below derive every hypothesis of
; fn-scj-invp-at-host-article-finish-carried from fn-sjh-okp, the owner
; relation and the words the host tests.

(defthm fn-sjh-durable-finish-is-enabled
  (implies (equal (car (fn-ccar-own-finish o cfg fn-arena)) :durable)
           (fn-ccar-completion-enabledp (fn-own-store o)))
  :hints (("Goal" :in-theory '(fn-ccar-own-finish-is-own-finish fn-own-finish car-cons
                               fn-ccar-completion-enabledp-is-reference))))

(defthm fn-sjh-durable-finish-names-a-held-row
  (implies (and (equal (car (fn-ccar-own-finish o cfg fn-arena)) :durable)
                (fn-sn-statep (fn-own-store o)))
           (fn-held-p (fn-ccar-completion-record (fn-own-store o))))
  :hints (("Goal" :in-theory '(fn-ccar-own-finish-is-own-finish fn-own-finish car-cons
                               fn-own-completion-names-submission-p
                               fn-ccar-completion-record-is-completion-record))))

(defthm fn-sjh-held-row-is-no-other-event
  (implies (fn-held-p r)
           (and (not (fn-evc-retentionp r)) (not (fn-evc-consumerp r)) (not (fn-evc-topicp r))
                (not (fn-evc-stxep r)) (not (fn-evc-stxkp r)) (not (fn-evc-stxap r))))
  :hints (("Goal" :in-theory (e/d (fn-evc-retentionp fn-evc-consumerp fn-evc-topicp
                                   fn-evc-stxep fn-evc-stxkp fn-evc-stxap)
                                  (fn-held-p fn-store-retention-event-p fn-stxe-p fn-stxk-p
                                   fn-hstxa-p fn-th-topic-eventp fn-cpe-eventp))
           :use ((:instance fn-snt-an-article-record-is-no-other-store-event (record r))))))

(defthm fn-sjh-ocl-acceptance-statep
  (implies (fn-ocl-relation oc)
           (fn-statep (fn-node-acceptance (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))))
  :hints (("Goal" :in-theory (e/d (fn-node-statep) (fn-statep))
           :use ((:instance fn-scar-ocl-relation-carries-node-statep)))))

(defthm fn-sjh-finish-store-image
  (implies (fn-ccar-completion-enabledp (fn-own-store o))
           (let ((s2 (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena))))
                 (s (fn-own-store o)))
             (and (equal (fn-sf-phase (fn-sn-files s2)) :ready)
                  (equal (fn-sf-records (fn-sn-files s2)) (fn-sf-records (fn-sn-files s)))
                  (fn-own-store-idlep s2))))
  :hints (("Goal" :in-theory (e/d (fn-own-store-idlep fn-snt-idle-phasep)
                                  (fn-ccar-own-finish fn-ccar-sn-finish-enabled fn-sn-finish fn-ccar-sn-finish))
           :use ((:instance fn-scj-host-finish-store)
                 (:instance fn-ccar-sn-finish-is-sn-finish (s (fn-own-store o)))
                 (:instance (:definition fn-ccar-sn-finish) (s (fn-own-store o)))
                 (:instance fn-snt-finish-image (s (fn-own-store o)))
                 (:instance fn-ccar-completion-enabledp-is-reference (s (fn-own-store o)))
                 (:instance fn-scj-records-kept-by-ccar-finish (s (fn-own-store o)))))))

(defthm fn-sjh-versions-atmost-monotone
  (implies (and (fn-scj-conns-versions-atmostp conns n) (<= (nfix n) (nfix m)))
           (fn-scj-conns-versions-atmostp conns m))
  :hints (("Goal" :induct (fn-scj-conns-versions-atmostp conns n)
           :in-theory (enable fn-scj-conns-versions-atmostp))))

(defthm fn-sjh-finish-keeps-conns
  (equal (fn-own-conns (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (fn-own-conns o))
  :hints (("Goal" :in-theory (e/d (fn-own-finish fn-own-complete fn-own-refresh)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-sn-finish
                                   fn-ctl-refresh-withdrawals fn-ctl-refresh-withdrawn fn-midx-refresh
                                   fn-gidx-refresh fn-ctl-visible-state-of fn-sn-completion-enabledp
                                   fn-own-completion-names-submission-p fn-own-view-make-visible)))))

(defthm fn-sjh-finish-keeps-view-gidx
  (implies (and (fn-ccar-completion-enabledp (fn-own-store o))
                (fn-sjh-view-gidxp (fn-own-view o)))
           (fn-sjh-view-gidxp (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena)))))
  :hints (("Goal" :in-theory (e/d (fn-crf-with-store) (fn-ccar-own-finish fn-own-refresh fn-sjh-view-gidxp))
           :use ((:instance fn-scj-host-finish-view-and-store)
                 (:instance fn-sjh-refresh-keeps-gidx
                            (o (fn-crf-with-store o (fn-ccar-sn-finish-enabled (fn-own-store o)))))))))

(defthm fn-sjh-finish-keeps-view-indexed
  (implies (fn-scar-view-indexedp o)
           (fn-scar-view-indexedp (cdr (fn-ccar-own-finish o cfg fn-arena))))
  :hints (("Goal" :in-theory '(fn-ccar-own-finish-is-own-finish fn-own-finish cdr-cons
                               fn-oix-complete-keeps-view-indexed))))

(defthm fn-sjh-not-enabled-at-ready
  (implies (equal (fn-sf-phase (fn-sn-files s)) :ready)
           (not (fn-ccar-completion-enabledp s)))
  :hints (("Goal" :use ((:instance fn-scj-enabled-is-completing)))))

(defthm fn-sjh-finish-side-facts
  (implies (and (fn-ccar-completion-enabledp (fn-own-store o))
                (fn-scjs-historyp o)
                (fn-scj-versions-okp o))
           (let ((o2 (cdr (fn-ccar-own-finish o cfg fn-arena))))
             (and (fn-scjs-seenp o2)
                  (fn-scjs-historyp o2)
                  (fn-scj-versions-okp o2)
                  (fn-sjh-linkp o2 nil fn-arena c2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scjs-seenp fn-scjs-store-seenp fn-scjs-seen-records fn-scjs-historyp
                            fn-scj-versions-okp fn-sjh-linkp fn-sjh-files-linkp fn-sjh-inflight fn-sf-record-phasep)
                           (fn-ccar-own-finish fn-ccar-completion-enabledp fn-own-store-idlep
                            fn-scj-conns-versions-atmostp nthcdr len))
           :use ((:instance fn-sjh-finish-store-image)
                 (:instance fn-scj-version-of-host-finish)
                 (:instance fn-sjh-finish-keeps-conns)
                 (:instance fn-scjs-no-rowsp-of-nthcdr-len
                            (xs (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-sjh-not-enabled-at-ready
                            (s (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena)))))
                 (:instance fn-sjh-versions-atmost-monotone
                            (conns (fn-own-conns o))
                            (n (fn-own-view-version (fn-own-view o)))
                            (m (len (fn-sf-records (fn-sn-files (fn-own-store o))))))))))

(defthm fn-sjh-completion-record-needs-records
  (implies (and (fn-sn-statep s) (fn-ccar-completion-record s))
           (consp (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-record fn-sn-find-record)
                                  (fn-sn-statep))
           :use ((:instance fn-ccar-completion-record-is-completion-record)))))

;; The catalog's finish under LINK's token and count answers the completion
;; and holds no pending row after.
(defthm fn-sjh-sca-finish-clears-pending
  (implies (and (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (len fn-cat)))
           (equal (mv-nth 1 (fn-sca-finish token pending view-index targets fn-cat)) nil))
  :hints (("Goal" :in-theory (e/d (fn-sca-finish fn-sca-complete fn-cat-complete fn-cat-complete-hidden
                                   fn-pc-p)
                                  (fn-sca-withdraw-targets fn-cat-commit fn-delta-of-row fn-cat-at
                                   fn-midx-lookup)))))

;; The carried finish theorem's hypotheses as one predicate, and all of them
;; from fn-sjh-okp, the owner relation and :durable.
(defun-nx fn-sjh-finish-premisesp (o cfg fn-arena fn-cat pending token)
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
         (fn-statep (fn-node-acceptance (fn-sn-node s)))
         (not (fn-evc-retentionp r)) (not (fn-evc-consumerp r)) (not (fn-evc-topicp r))
         (not (fn-evc-stxep r)) (not (fn-evc-stxkp r)) (not (fn-evc-stxap r))
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

(defthm fn-sjh-carried-finish-by-premises
  (let* ((o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (view2 (fn-own-view o2))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (fn-sjh-finish-premisesp o cfg fn-arena fn-cat pending token)
             (and (fn-scj-invp o2 fn-arena c2)
                  (fn-scj-seqs-sortedp c2)
                  (fn-cnx-freshp c2))))
  :hints (("Goal" :in-theory '(fn-sjh-finish-premisesp)
           :use ((:instance fn-scj-invp-at-host-article-finish-carried)))))

(defthm fn-sjh-finish-premises-of-okp
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending))))
    (implies (and (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (equal (car (fn-ccar-own-finish o cfg fn-arena)) :durable))
             (fn-sjh-finish-premisesp o cfg fn-arena fn-cat pending token)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-finish-premisesp fn-sjh-ocfg-owner-of-with-owner
                                        (:executable-counterpart fn-held-p)
                                        fn-sjh-durable-finish-is-enabled
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
                 (:instance fn-sjh-durable-finish-names-a-held-row (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-durable-needs-pending (o (fn-ocfg-owner oc)))
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

;; What the finished owner and catalog satisfy, from the premises alone.
(defthm fn-sjh-premises-facts
  (implies (fn-sjh-finish-premisesp o cfg fn-arena fn-cat pending token)
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
  :hints (("Goal" :in-theory '(fn-sjh-finish-premisesp))))

(defthm fn-sjh-pc-p-non-nil
  (implies (fn-pc-p pending) pending)
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-pc-p))))

(defthm fn-sjh-okp-after-finish-by-premises
  (let* ((o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (view2 (fn-own-view o2))
         (fin (fn-sca-finish token pending (fn-own-view-index view2)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view2))
                             fn-cat)))
    (implies (fn-sjh-finish-premisesp o cfg fn-arena fn-cat pending token)
             (and (equal (mv-nth 1 fin) nil)
                  (fn-sjh-okp o2 nil fn-arena (mv-nth 2 fin)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-okp-when-parts fn-sjh-premises-facts fn-sjh-pc-p-non-nil
                                        fn-sjh-carried-finish-by-premises fn-sjh-finish-side-facts
                                        fn-sjh-finish-keeps-view-indexed fn-sjh-sca-finish-clears-pending)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-finish-store-image)
                 (:instance fn-sjh-premises-facts)))))

; KEYSTONE (the join carried across the host's article finish).  Over
; fn-ccar-own-finish, the owner finish the host's call equals (below): under
; the owner relation and fn-sjh-okp before and the finish's :durable, the
; host holds a pending row (fn-sjh-durable-needs-pending), and the catalog
; fn-sca-finish leaves, with no pending row, satisfies fn-sjh-okp with the
; finished owner; the owner relation after is
; fn-ocmt-post-commit-preserves-ocl-relation's.
(defthm fn-sjh-okp-at-host-article-finish
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (res (fn-ccar-own-finish o cfg fn-arena))
         (o2 (cdr res))
         (view2 (fn-own-view o2))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (fin (fn-sca-finish token pending (fn-own-view-index view2)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view2))
                             fn-cat)))
    (implies (and (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (equal (car res) :durable))
             (and pending
                  (equal (mv-nth 1 fin) nil)
                  (fn-sjh-okp o2 nil fn-arena (mv-nth 2 fin))
                  (fn-ocl-relation (fn-ocfg-with-owner oc o2)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ocmt-post-commit-preserves-ocl-relation fn-sjh-pc-p-non-nil)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-finish-premises-of-okp)
                 (:instance fn-sjh-premises-facts (o (fn-ocfg-owner oc))
                            (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                                         (fn-pc-expected pending))))
                 (:instance fn-sjh-okp-after-finish-by-premises (o (fn-ocfg-owner oc))
                            (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                                         (fn-pc-expected pending))))))))

; The same over the function the host calls, fn-apc-own-finish, under the two
; facts that make it fn-own-finish (fn-apc-own-finish-is-own-finish): a
; well-formed parse carry and the history stobj synchronized to the store
; (fn-owner-finish-submission calls fn-host-hist-sync first).
(defthm fn-sjh-okp-at-owner-finish-submission
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (res (fn-apc-own-finish o cfg fn-arena fn-hist carry))
         (o2 (cdr res))
         (view2 (fn-own-view o2))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (fin (fn-sca-finish token pending (fn-own-view-index view2)
                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                (fn-own-view-withdrawals view2))
                             fn-cat)))
    (implies (and (fn-apc-p carry)
                  (fn-hist-of-storep fn-hist s)
                  (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (equal (car res) :durable))
             (and pending
                  (equal (mv-nth 1 fin) nil)
                  (fn-sjh-okp o2 nil fn-arena (mv-nth 2 fin))
                  (fn-ocl-relation (fn-ocfg-with-owner oc o2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-apc-own-finish-is-own-finish fn-ccar-own-finish-is-own-finish)
           :use ((:instance fn-sjh-okp-at-host-article-finish)))))
