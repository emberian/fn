; served-catalog-join-host.lisp -- the catalog join carried across the host's
; own protocol (lane join-f2, 2026-09-28; PRF-302, the discharge sca-join-5
; left open).
;
; The host threads the catalog's pending row between its entries in a state
; global, fn-owner-cat-pending (host/owner-host.lisp): fn-owner-cat-prepare-
; sealed sets it after the store staged the POST's row and the host sealed
; its payload; the store's io steps append that row to the history and reach
; :completing; fn-owner-finish-submission (and fn-owner-finish-identity)
; finish the owner and then the catalog with it.  The join's finish theorem
; (books/served-catalog-join-inv.lisp fn-scj-invp-at-host-article-finish-
; carried) took the facts that relate those pieces as named hypotheses.  This
; book states them as one predicate over the owner, the host's pending row,
; the arena and the catalog (fn-sjh-okp) and proves it carried by the host's
; finish from the owner relation the host's owner satisfies (fn-ocl-relation)
; and the words the host itself tests (:durable, a pending row): the finish
; hypotheses are then properties of the carried state, not of the step.
;
; fn-sjh-okp:
;   fn-scj-invp                 the catalog invariant (join, rows, VV, live
;                               view, every pinned connection);
;   the carried side facts      seen history, history shape, the view's trie,
;                               sorted rows, fresh numbers, pinned versions at
;                               or below the view's;
;   S                           every row of the store's history is a
;                               well-formed composite and carries no
;                               withdrawal (the load's two row facts);
;   LINK                        at an enabled completion with a pending row:
;                               the row is the last record's catalog row, its
;                               token names that completion and its expected
;                               count is the catalog's.

(in-package "ACL2")

(include-book "served-catalog-join-inv")
(include-book "owner-parse-carried") ; fn-apc-own-finish: the finish the host calls

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The view's group buckets over its visible archive: the live view's catalog
; premise carries them (fn-scj-live-okp), and a refresh keeps them.

(defun fn-sjh-view-gidxp (view)
  (declare (xargs :guard t))
  (implies (fn-own-view-group-index view)
           (equal (fn-own-view-group-index view)
                  (fn-gidx-build (fn-state-articles (fn-own-view-archive view))))))

(defthm fn-sjh-invp-gives-view-gidx
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-sjh-view-gidxp (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-sjh-view-gidxp fn-scj-invp fn-scj-live-okp fn-scr-live-catalogp
                                   fn-scr-fields-catalogp fn-scr-catalogp fn-gidx-pin-correspondencep)
                                  (fn-scj-joinp fn-scj-rows-invp fn-scj-vvp fn-scj-conns-pinp
                                   fn-scr-view-of fn-cat-view-articles fn-midx-correspondencep
                                   fn-gidx-build fn-own-view-live fn-statep fn-cnx-freshp))
           :use ((:instance fn-own-view-live-fields (view (fn-own-view o)))))))

(defthm fn-sjh-refresh-keeps-gidx
  (implies (fn-sjh-view-gidxp (fn-own-view o))
           (fn-sjh-view-gidxp (fn-own-view (fn-own-refresh o))))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh fn-sjh-view-gidxp fn-gidx-refresh-is-build)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-own-view-make-visible fn-own-view-group-index fn-own-view-archive
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-gidx-build fn-ctl-visible-state-of)))))

(defthm fn-sjh-view-indexesp-of-parts
  (implies (and (fn-scar-view-indexedp o)
                (fn-sjh-view-gidxp (fn-own-view o)))
           (fn-scj-view-indexesp (fn-own-view o)))
  :hints (("Goal" :in-theory (enable fn-scar-view-indexedp fn-sjh-view-gidxp fn-scj-view-indexesp))))

(in-theory (disable fn-sjh-view-gidxp))

; -----------------------------------------------------------------------------
; LINK and the carried predicate.

;; The store's in-flight row: the staged candidate at the record phases, the
;; last record while it completes.
(defun-nx fn-sjh-inflight (files)
  (let ((phase (fn-sf-phase files)))
    (cond ((fn-sf-record-phasep phase) (fn-sf-record-candidate files))
          ((equal phase :completing) (car (last (fn-sf-records files))))
          (t nil))))

;; LINK.  The completion names the last record; a staged candidate is a
;; well-formed composite without a withdrawal (so appending it keeps S); and
;; the host's pending row is exactly the in-flight row's catalog row, with the
;; token of that row's pair and the catalog's count -- or, without a pending
;; row, no in-flight row loads one.
(defun-nx fn-sjh-linkp (o pending fn-arena fn-cat)
  (let* ((files (fn-sn-files (fn-own-store o)))
         (phase (fn-sf-phase files))
         (r (fn-sjh-inflight files)))
    (and (implies (equal phase :completing)
                  (and (consp (fn-sf-records files))
                       (equal (fn-sf-completion files) (fn-sf-record-pair r))))
         (implies (fn-sf-record-phasep phase)
                  (and (fn-row-composite-okp r fn-arena)
                       (fn-scj-rows-clearp (list r))))
         (if pending
             (and (or (fn-sf-record-phasep phase) (equal phase :completing))
                  (fn-pc-p pending)
                  (equal (fn-scj-load-h r) (fn-pc-held pending))
                  (equal (fn-pc-token pending)
                         (cons (nfix (cdr (fn-sf-record-pair r))) (fn-pc-expected pending)))
                  (equal (fn-pc-expected pending) (len fn-cat)))
           (not (fn-scj-load-h r))))))

(defun-nx fn-sjh-okp (o pending fn-arena fn-cat)
  (let ((records (fn-sf-records (fn-sn-files (fn-own-store o)))))
    (and (fn-scj-invp o fn-arena fn-cat)
         (fn-scjs-seenp o)
         (fn-scjs-historyp o)
         (fn-scar-view-indexedp o)
         (fn-scj-seqs-sortedp fn-cat)
         (fn-cnx-freshp fn-cat)
         (fn-scj-versions-okp o)
         (fn-rows-composites-okp records fn-arena)
         (fn-scj-rows-clearp records)
         (fn-sjh-linkp o pending fn-arena fn-cat))))

; -----------------------------------------------------------------------------
; LINK at an enabled completion: the completion record is the last record
; (sequences are positions, fn-sf-record-listp), so the pending row is its
; catalog row; and a completion of a held row has a pending row at all.

(defthm fn-sjh-last-sequence
  (implies (and (fn-sf-record-listp records seq lower frontier) (consp records))
           (equal (fn-store-event-sequence (car (last records)))
                  (+ seq (len records) -1)))
  :hints (("Goal" :induct (fn-sf-record-listp records seq lower frontier)
           :in-theory (enable fn-sf-record-listp))))

(defthm fn-sjh-find-last-record
  (implies (and (fn-sf-record-listp records seq lower frontier) (consp records) (natp seq))
           (equal (fn-sn-find-record (fn-sf-record-pair (car (last records))) records)
                  (car (last records))))
  :hints (("Goal" :induct (fn-sf-record-listp records seq lower frontier)
           :in-theory (e/d (fn-sf-record-listp fn-sn-find-record fn-sf-record-pair)
                           (fn-store-event-p)))
          ("Subgoal *1/2" :use ((:instance fn-sjh-last-sequence (records (cdr records))
                                           (seq (+ 1 seq))
                                           (lower (+ 1 (fn-store-event-txid (car records)))))))))
(defthm fn-sjh-completion-record-is-last
  (implies (and (fn-sn-statep s)
                (consp (fn-sf-records (fn-sn-files s)))
                (equal (fn-sf-completion (fn-sn-files s))
                       (fn-sf-record-pair (car (last (fn-sf-records (fn-sn-files s)))))))
           (equal (fn-ccar-completion-record s)
                  (car (last (fn-sf-records (fn-sn-files s))))))
  :hints (("Goal" :in-theory (e/d (fn-sn-completion-record fn-sn-statep fn-sf-statep)
                                  (fn-sn-find-record fn-sf-record-pair fn-node-statep fn-sf-phase-shapep
                                   fn-sf-success-listp))
           :use ((:instance fn-ccar-completion-record-is-completion-record)
                 (:instance fn-sjh-find-last-record (records (fn-sf-records (fn-sn-files s)))
                            (seq 0) (lower 0) (frontier (fn-sf-frontier (fn-sn-files s))))))))
(defthm fn-sjh-load-h-of-held
  (implies (fn-held-p r) (equal (fn-scj-load-h r) r))
  :hints (("Goal" :in-theory (e/d (fn-scj-load-h) (fn-held-p fn-cat-rowp))
           :use ((:instance fn-held-p-implies-cat-rowp (x r))))))

(defthm fn-sjh-linkp-at-enabled-completion
  (implies (and (fn-sjh-linkp o pending fn-arena fn-cat)
                (fn-ccar-completion-enabledp (fn-own-store o))
                pending)
           (let* ((files (fn-sn-files (fn-own-store o)))
                  (records (fn-sf-records files)))
             (and (fn-pc-p pending)
                  (equal (fn-scj-load-h (car (last records))) (fn-pc-held pending))
                  (equal (fn-pc-token pending)
                         (cons (nfix (cdr (fn-sf-completion files))) (fn-pc-expected pending)))
                  (equal (fn-pc-expected pending) (len fn-cat)))))
  :hints (("Goal" :in-theory (e/d (fn-sjh-linkp fn-sjh-inflight fn-sf-record-phasep)
                                  (fn-ccar-completion-enabledp fn-sf-record-pair fn-scj-load-h fn-pc-p))
           :use ((:instance fn-scj-enabled-is-completing (s (fn-own-store o)))))))

(defthm fn-sjh-durable-needs-pending
  (implies (and (fn-sjh-linkp o pending fn-arena fn-cat)
                (fn-sn-statep (fn-own-store o))
                (fn-ccar-completion-enabledp (fn-own-store o))
                (fn-held-p (fn-ccar-completion-record (fn-own-store o))))
           pending)
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sjh-linkp fn-sjh-inflight fn-sf-record-phasep)
                                  (fn-ccar-completion-enabledp fn-sf-record-pair fn-scj-load-h fn-pc-p
                                   fn-held-p fn-sn-statep))
           :use ((:instance fn-scj-enabled-is-completing (s (fn-own-store o)))
                 (:instance fn-sjh-completion-record-is-last (s (fn-own-store o)))
                 (:instance fn-sjh-load-h-of-held
                            (r (fn-ccar-completion-record (fn-own-store o))))))))

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

(defthm fn-sjh-ocl-gives-cst
  (implies (fn-ocl-relation oc)
           (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory '(fn-ocl-relation))))

(defthm fn-sjh-ocl-gives-visible
  (implies (fn-ocl-relation oc)
           (equal (fn-state-articles (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))
                  (fn-ctl-visible-articles (fn-own-view-raw (fn-own-view (fn-ocfg-owner oc)))
                                           (fn-own-view-withdrawals (fn-own-view (fn-ocfg-owner oc)))
                                           (fn-own-view-verdicts (fn-own-view (fn-ocfg-owner oc))))))
  :hints (("Goal" :in-theory '(fn-ocl-relation fn-ocl-view-visiblep)
           :use ((:instance fn-ocl-view-historyp-is-visible (o (fn-ocfg-owner oc)))))))

(defthm fn-sjh-ocl-gives-view-statep
  (implies (fn-ocl-relation oc)
           (fn-statep (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc)))))
  :hints (("Goal" :in-theory '(fn-acar-view-statep)
           :use ((:instance fn-acar-ocl-relation-carries-view-statep)))))

(defthm fn-sjh-ocfg-owner-of-with-owner
  (equal (fn-ocfg-owner (fn-ocfg-with-owner oc owner)) owner)
  :hints (("Goal" :in-theory (enable fn-ocfg-with-owner))))

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
                            fn-scj-versions-okp fn-sjh-linkp fn-sjh-inflight fn-sf-record-phasep)
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
  (implies (and pending
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (len fn-cat)))
           (equal (mv-nth 1 (fn-sca-finish token pending view-index targets fn-cat)) nil))
  :hints (("Goal" :in-theory (e/d (fn-sca-finish fn-sca-complete fn-cat-complete fn-cat-complete-hidden)
                                  (fn-sca-withdraw-targets fn-cat-commit fn-delta-of-row fn-cat-at
                                   fn-midx-lookup)))))

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
           :in-theory (union-theories '(fn-sjh-okp fn-sjh-ocfg-owner-of-with-owner
                                        (:executable-counterpart fn-held-p)
                                        fn-sjh-durable-finish-is-enabled
                                        fn-ccar-ocl-relation-carries-sn-statep
                                        fn-sjh-held-row-is-no-other-event
                                        fn-sjh-ocl-acceptance-statep
                                        fn-ocmt-post-commit-preserves-ocl-relation
                                        fn-sjh-ocl-gives-cst fn-sjh-ocl-gives-visible
                                        fn-sjh-ocl-gives-view-statep
                                        fn-sjh-invp-gives-view-gidx fn-sjh-finish-keeps-view-gidx
                                        fn-sjh-finish-keeps-view-indexed fn-sjh-view-indexesp-of-parts
                                        fn-sjh-completion-record-needs-records
                                        fn-sjh-linkp-at-enabled-completion)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-finish-store-image (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-durable-finish-names-a-held-row (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-durable-needs-pending (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-completion-record-needs-records (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-sjh-sca-finish-clears-pending
                            (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))) (fn-pc-expected pending)))
                            (view-index (fn-own-view-index (fn-own-view (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                            (targets (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                        (fn-own-view-withdrawals (fn-own-view (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))))
                 (:instance fn-sjh-ocl-gives-cst
                            (oc (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                 (:instance fn-sjh-ocl-gives-visible
                            (oc (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                 (:instance fn-sjh-ocl-gives-view-statep
                            (oc (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                 (:instance fn-scj-vvp-of-host-finish (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-vvp-parts (o (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena))))
                 (:instance fn-sjh-finish-side-facts (o (fn-ocfg-owner oc))
                            (c2 (mv-nth 2 (fn-sca-finish (cons (nfix (cdr (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))) (fn-pc-expected pending))
                                          pending (fn-own-view-index (fn-own-view (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena))))
                                          (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                             (fn-own-view-withdrawals (fn-own-view (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
                                          fn-cat))))
                 (:instance fn-scj-invp-at-host-article-finish-carried
                            (o (fn-ocfg-owner oc))
                            (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))) (fn-pc-expected pending))))))))

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
