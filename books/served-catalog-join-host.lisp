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
(defun-nx fn-sjh-files-linkp (files pending fn-arena fn-cat)
  (let* ((phase (fn-sf-phase files))
         (r (fn-sjh-inflight files)))
    (and (implies (equal phase :completing)
                  (and (consp (fn-sf-records files))
                       (equal (fn-sf-completion files) (fn-sf-record-pair r))))
         (implies (fn-sf-record-phasep phase)
                  (and (fn-row-composite-okp r fn-arena)
                       (fn-rows-handles-inp (list r) fn-arena)
                       (fn-scj-rows-clearp (list r))))
         (if pending
             (and (or (fn-sf-record-phasep phase) (equal phase :completing))
                  (fn-pc-p pending)
                  (equal (fn-scj-load-h r) (fn-pc-held pending))
                  (equal (fn-pc-token pending)
                         (cons (nfix (cdr (fn-sf-record-pair r))) (fn-pc-expected pending)))
                  (equal (fn-pc-expected pending) (len fn-cat)))
           (not (fn-scj-load-h r))))))

(defun-nx fn-sjh-linkp (o pending fn-arena fn-cat)
  (fn-sjh-files-linkp (fn-sn-files (fn-own-store o)) pending fn-arena fn-cat))

;; The store's side: S (every row of the history a well-formed composite
;; without a withdrawal, its handles in the arena) and LINK.
(defun-nx fn-sjh-files-okp (files pending fn-arena fn-cat)
  (and (fn-rows-composites-okp (fn-sf-records files) fn-arena)
       (fn-rows-handles-inp (fn-sf-records files) fn-arena)
       (fn-scj-rows-clearp (fn-sf-records files))
       (fn-sjh-files-linkp files pending fn-arena fn-cat)))

(defun-nx fn-sjh-okp (o pending fn-arena fn-cat)
  (and (fn-scj-invp o fn-arena fn-cat)
       (fn-scjs-seenp o)
       (fn-scjs-historyp o)
       (fn-scar-view-indexedp o)
       (fn-scj-seqs-sortedp fn-cat)
       (fn-cnx-freshp fn-cat)
       (fn-scj-versions-okp o)
       (fn-sjh-files-okp (fn-sn-files (fn-own-store o)) pending fn-arena fn-cat)))

(defthm fn-sjh-okp-unfolds
  (equal (fn-sjh-okp o pending fn-arena fn-cat)
         (let ((records (fn-sf-records (fn-sn-files (fn-own-store o)))))
           (and (fn-scj-invp o fn-arena fn-cat)
                (fn-scjs-seenp o)
                (fn-scjs-historyp o)
                (fn-scar-view-indexedp o)
                (fn-scj-seqs-sortedp fn-cat)
                (fn-cnx-freshp fn-cat)
                (fn-scj-versions-okp o)
                (fn-rows-composites-okp records fn-arena)
                (fn-rows-handles-inp records fn-arena)
                (fn-scj-rows-clearp records)
                (fn-sjh-linkp o pending fn-arena fn-cat))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-sjh-okp fn-sjh-files-okp fn-sjh-linkp))))

(defthm fn-sjh-okp-when-parts
  (implies (and (fn-scj-invp o fn-arena fn-cat)
                (fn-scjs-seenp o)
                (fn-scjs-historyp o)
                (fn-scar-view-indexedp o)
                (fn-scj-seqs-sortedp fn-cat)
                (fn-cnx-freshp fn-cat)
                (fn-scj-versions-okp o)
                (fn-rows-composites-okp (fn-sf-records (fn-sn-files (fn-own-store o))) fn-arena)
                (fn-rows-handles-inp (fn-sf-records (fn-sn-files (fn-own-store o))) fn-arena)
                (fn-scj-rows-clearp (fn-sf-records (fn-sn-files (fn-own-store o))))
                (fn-sjh-linkp o pending fn-arena fn-cat))
           (fn-sjh-okp o pending fn-arena fn-cat))
  :hints (("Goal" :use fn-sjh-okp-unfolds)))

(in-theory (disable fn-sjh-okp-when-parts))

; What the owner relation the host's owner satisfies gives the join's proofs.
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

(defthm fn-sjh-ocl-facts-for-prepare
  (implies (fn-ocl-relation oc)
           (and (fn-statep (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc))))
                (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner oc)))))
  :hints (("Goal" :in-theory '(fn-acar-view-statep fn-ocl-relation)
           :use ((:instance fn-acar-ocl-relation-carries-view-statep)
                 (:instance fn-ocl-view-historyp-is-visible (o (fn-ocfg-owner oc)))))))

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
  :hints (("Goal" :in-theory (e/d (fn-sjh-linkp fn-sjh-files-linkp fn-sjh-inflight fn-sf-record-phasep)
                                  (fn-ccar-completion-enabledp fn-sf-record-pair fn-scj-load-h fn-pc-p))
           :use ((:instance fn-scj-enabled-is-completing (s (fn-own-store o)))))))

(defthm fn-sjh-durable-needs-pending
  (implies (and (fn-sjh-linkp o pending fn-arena fn-cat)
                (fn-sn-statep (fn-own-store o))
                (fn-ccar-completion-enabledp (fn-own-store o))
                (fn-held-p (fn-ccar-completion-record (fn-own-store o))))
           pending)
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sjh-linkp fn-sjh-files-linkp fn-sjh-inflight fn-sf-record-phasep)
                                  (fn-ccar-completion-enabledp fn-sf-record-pair fn-scj-load-h fn-pc-p
                                   fn-held-p fn-sn-statep))
           :use ((:instance fn-scj-enabled-is-completing (s (fn-own-store o)))
                 (:instance fn-sjh-completion-record-is-last (s (fn-own-store o)))
                 (:instance fn-sjh-load-h-of-held
                            (r (fn-ccar-completion-record (fn-own-store o))))))))

; -----------------------------------------------------------------------------
; The store's io steps (host/owner-host.lisp fn-owner-io: fn-rcon-ocfg-io, which
; is fn-ocfg-step of (:store (:io OPERATION RESULT)), and the log route's
; reserve and order): a file step keeps the rows' facts and LINK -- the
; record-directory append moves the staged candidate into the history as the
; completing last record, every other step keeps the candidate or has none.

(defthm fn-sjh-composites-okp-of-snoc
  (equal (fn-rows-composites-okp (append rows (list r)) fn-arena)
         (and (fn-rows-composites-okp rows fn-arena) (fn-row-composite-okp r fn-arena)))
  :hints (("Goal" :induct (fn-rows-composites-okp rows fn-arena)
           :in-theory (e/d (fn-rows-composites-okp) (fn-row-composite-okp)))))

(defthm fn-sjh-rows-clearp-of-snoc
  (equal (fn-scj-rows-clearp (append rows (list r)))
         (and (fn-scj-rows-clearp rows) (fn-scj-rows-clearp (list r))))
  :hints (("Goal" :induct (fn-scj-rows-clearp rows)
           :in-theory (e/d (fn-scj-rows-clearp) (fn-scj-load-h)))))

(defthm fn-sjh-handles-inp-of-snoc
  (equal (fn-rows-handles-inp (append rows (list r)) fn-arena)
         (and (fn-rows-handles-inp rows fn-arena) (fn-rows-handles-inp (list r) fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (e/d (fn-rows-handles-inp) (fn-row-handle-inp fn-held-p fn-hstxa-p)))))

(defthm fn-sjh-car-last-of-snoc
  (equal (car (last (append x (list c)))) c))

(defthm fn-sjh-consp-of-snoc
  (consp (append x (list c))))

(defthm fn-sjh-file-step-keeps-files-okp
  (implies (fn-sjh-files-okp files pending fn-arena fn-cat)
           (fn-sjh-files-okp (fn-sn-file-step files operation result) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-sjh-files-okp fn-sjh-files-linkp fn-sjh-inflight
                                   fn-sn-file-step fn-sf-start-frontier fn-sf-frontier-file-result
                                   fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                                   fn-sf-record-file-result fn-sf-record-link-result
                                   fn-sf-record-dir-result fn-sf-recovery-barrier
                                   fn-sf-record-phasep)
                                  (fn-sf-statep fn-row-composite-okp fn-scj-load-h fn-pc-p
                                   fn-sf-record-pair fn-rows-composites-okp fn-scj-rows-clearp
                                   fn-rows-handles-inp)))))

(defthm fn-sjh-okp-is-parts
  (equal (fn-sjh-okp o pending fn-arena fn-cat)
         (and (fn-scj-invp o fn-arena fn-cat)
              (fn-scjs-seenp o)
              (fn-scjs-historyp o)
              (fn-scar-view-indexedp o)
              (fn-scj-seqs-sortedp fn-cat)
              (fn-cnx-freshp fn-cat)
              (fn-scjs-versionsp o)
              (fn-sjh-files-okp (fn-sn-files (fn-own-store o)) pending fn-arena fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-sjh-okp fn-scj-versions-okp fn-scjs-versionsp))))

(defthm fn-sjh-io-store-files
  (implies (fn-sn-statep s)
           (equal (fn-sn-files (fn-snrt-step s (list :io operation result)))
                  (fn-sn-file-step (fn-sn-files s) operation result)))
  :hints (("Goal" :in-theory (e/d (fn-snrt-step fn-snt-step fn-sn-io) (fn-sn-file-step fn-sn-statep)))))

(defthm fn-sjh-refresh-version
  (equal (fn-own-view-version (fn-own-view (fn-own-refresh o)))
         (if (fn-own-store-idlep (fn-own-store o))
             (len (fn-sf-records (fn-sn-files (fn-own-store o))))
           (fn-own-view-version (fn-own-view o))))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-ctl-visible-state-of)))))

(defthm fn-sjh-store-step-historyp
  (implies (and (fn-scjs-historyp o)
                (fn-scjs-seenp o)
                (not (member-equal (car ev) '(:finish :crash :recover))))
           (fn-scjs-historyp (fn-own-store-step o ev)))
  :hints (("Goal" :in-theory (e/d (fn-scjs-historyp fn-own-store-step fn-ocl-owner-with-store)
                                  (fn-snrt-step fn-own-refresh fn-own-store-idlep fn-scjs-store-framep))
           :use ((:instance fn-scjs-seenp-unfolds)
                 (:instance fn-scjs-snrt-step-framep (s (fn-own-store o)) (event ev)
                            (v (fn-own-view-version (fn-own-view o))))
                 (:instance fn-scjs-frame-records-facts
                            (o2 (fn-own-make (fn-snrt-step (fn-own-store o) ev) (fn-own-view o)
                                             (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                                             (fn-own-pending o) (fn-own-ledger-field o) (fn-own-clock o)
                                             (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
                                             (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o)
                                             (fn-own-refused o))))))))

(defthm fn-sjh-store-step-store
  (equal (fn-own-store (fn-own-store-step o ev))
         (fn-snrt-step (fn-own-store o) ev))
  :hints (("Goal" :in-theory (e/d (fn-own-store-step) (fn-snrt-step fn-own-refresh)))))

(defthm fn-sjh-ocfg-store-step-owner
  (equal (fn-ocfg-owner (fn-ocfg-step oc (list :store ev) fn-arena))
         (fn-own-store-step (fn-ocfg-owner oc) ev))
  :hints (("Goal" :in-theory '(fn-ocfg-step fn-ocfg-pass fn-own-step fn-ocfg-owner-of-fn-ocfg-make
                               fn-ocfg-with-owner car-cons cdr-cons (:e equal)))))

; KEYSTONE (the store's io steps).  host/owner-host.lisp fn-owner-io calls
; fn-rcon-ocfg-io, equal to fn-ocfg-step of (:store (:io OPERATION RESULT))
; (fn-rcon-ocfg-io-is-ocfg-step): the carried predicate with the same pending
; row.  The view's archive after is a state: fn-ocl-relation after the step
; carries it (fn-acar-ocl-relation-carries-view-statep).
(defthm fn-sjh-okp-of-ocfg-io
  (let* ((o (fn-ocfg-owner oc))
         (o2 (fn-ocfg-owner (fn-ocfg-step oc (list :store (list :io operation result)) fn-arena))))
    (implies (and (fn-ocl-relation oc)
                  (fn-sjh-okp o pending fn-arena fn-cat)
                  (fn-statep (fn-own-view-archive (fn-own-view o2))))
             (fn-sjh-okp o2 pending fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-ocfg-store-step-owner fn-sjh-store-step-store
                                        fn-ccar-ocl-relation-carries-sn-statep
                                        fn-sjh-io-store-files fn-sjh-file-step-keeps-files-okp
                                        car-cons (:e member-equal) (:e car))
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-is-parts (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-okp-is-parts
                            (o (fn-ocfg-owner (fn-ocfg-step oc (list :store (list :io operation result)) fn-arena))))
                 (:instance fn-scjs-ocfg-store-step-keeps-invp (ev (list :io operation result)))
                 (:instance fn-scjs-ocfg-store-step-keeps-versions (ev (list :io operation result)))
                 (:instance fn-sjh-store-step-historyp (o (fn-ocfg-owner oc)) (ev (list :io operation result)))
                 (:instance fn-oix-ocfg-step-keeps-view-indexed (event (list :store (list :io operation result))))))))
