; served-catalog-join-inv.lisp -- the catalog invariant at the host's entries
; (lane sca-join-4, 2026-09-27; PRF-302, step 5 of the join's discharge).
;
; fn-scj-invp (books/served-catalog-join-conns.lisp) is what the served
; chain needs of the catalog (fn-scj-invp-gives-owner-catalogp).  This book
; establishes it where the host builds its catalog: at every open the
; catalog is fn-sca-load-held-rows of the installed store's rows under the
; installed view's index (host/owner-host.lisp fn-owner-install-extended,
; lines naming fn-sca-load-held-rows), and the installed owner has no
; connection, a current view and VV (its view is fn-own-start's refresh).

(in-package "ACL2")

(include-book "served-catalog-join-read")
(include-book "served-catalog-join-frame")
(include-book "served-catalog-join-pinned")
(include-book "served-catalog-join-frame-conns")
(include-book "served-catalog-join-frame-store")
(include-book "store-files-traces")
(include-book "owner-time-admission")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-midx-branch-get)
                          (:definition fn-midx-put-chars)
                          (:definition fn-scr-catalogp)
                          (:definition fn-scr-fields-catalogp)
                          (:rewrite fn-gidx-refresh-is-build)
                          (:rewrite fn-sn-new-success-requires-actual-matching-durable-node-completion))))

(local (in-theory (disable fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp
                           fn-scat-msgid-idp fn-nntp-index-msgid-okp-stringp
                           fn-nntp-index-msgid-okp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; The load's numbers are fresh (each commit assigns one past the high).

(defthm fn-scj-freshp-of-load-from
  (implies (fn-cnx-freshp c)
           (fn-cnx-freshp (fn-sca-load-held-rows-from rows idx c)))
  :hints (("Goal" :induct (fn-sca-load-held-rows-from rows idx c)
           :in-theory (e/d (fn-sca-load-held-row) (fn-cnx-freshp fn-cat-commit-is-append)))))

(defthm fn-scj-freshp-of-load
  (fn-cnx-freshp (fn-sca-load-held-rows rows idx fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-sca-load-held-rows) (fn-sca-load-held-rows-from fn-cnx-freshp)))))

; -----------------------------------------------------------------------------
; The owner the opens install.

(defthm fn-scj-own-start-conns
  (equal (fn-own-conns (fn-own-start store max-conns)) nil)
  :hints (("Goal" :in-theory (e/d (fn-own-start) (fn-own-refresh))
           :use ((:instance fn-scj-refresh-keeps-conns
                            (o (fn-own-make store
                                (let* ((prefix (fn-own-prefix-archive
                                                (fn-sn-groups store) (fn-sn-capacity store)
                                                (fn-sf-records (fn-sn-files store)) 0 0))
                                       (archive (fn-ctl-visible-state prefix nil nil)))
                                  (fn-own-view-make-visible
                                   0 0 archive nil
                                   (fn-midx-build (fn-state-articles archive))
                                   (fn-gidx-build (fn-state-articles archive))
                                   nil (fn-state-articles prefix)
                                   (fn-ctl-subseq-diff (fn-state-articles prefix)
                                                       (fn-state-articles archive))
                                   nil))
                                nil 0 max-conns nil nil nil nil nil nil nil nil nil nil)))))))

(defthm fn-scj-own-start-vvp
  (implies (fn-own-store-idlep store)
           (fn-scj-vvp (fn-own-start store max-conns)))
  :hints (("Goal" :in-theory (e/d (fn-own-start) (fn-own-refresh fn-own-store-idlep fn-scj-vvp)))))

; The started view's group index is the build of its articles.
(defthm fn-scj-own-start-group-index
  (implies (fn-own-store-idlep store)
           (let ((view (fn-own-view (fn-own-start store max-conns))))
             (equal (fn-own-view-group-index view)
                    (fn-gidx-build (fn-state-articles (fn-own-view-archive view))))))
  :hints (("Goal" :in-theory (e/d (fn-own-start fn-own-refresh)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-own-view-group-index fn-own-view-archive fn-own-view-make-visible
                                   fn-own-prefix-archive fn-ctl-visible-state fn-midx-build fn-gidx-build
                                   fn-ctl-subseq-diff fn-ctl-visible-state-of)))))

(defthm fn-scj-configure-keeps-conns
  (equal (fn-own-conns (fn-own-configure o config)) (fn-own-conns o))
  :hints (("Goal" :in-theory (enable fn-own-configure))))

(defthm fn-scj-vvp-by-view-and-store
  (implies (and (equal (fn-own-view o) (fn-own-view p))
                (equal (fn-own-store o) (fn-own-store p)))
           (equal (fn-scj-vvp o) (fn-scj-vvp p)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scj-vvp))))

; A Message-ID trie is an alist of branches, never a group-index pin.
(defun fn-scj-branchesp (x)
  (declare (xargs :guard t))
  (if (consp x) (and (consp (car x)) (fn-scj-branchesp (cdr x))) t))

(defthm fn-scj-branchesp-of-branch-put
  (implies (fn-scj-branchesp b) (fn-scj-branchesp (fn-midx-branch-put k v b))))

(defthm fn-scj-branchesp-of-branch-get-irrelevant
  (fn-scj-branchesp (fn-midx-put-chars cs a nil))
  :hints (("Goal" :induct (fn-midx-put-chars cs a nil))))

(defthm fn-scj-branchesp-of-put-chars
  (implies (fn-scj-branchesp trie) (fn-scj-branchesp (fn-midx-put-chars cs a trie))))

(defthm fn-scj-branchesp-of-midx-build
  (fn-scj-branchesp (fn-midx-build arts)))

(defthm fn-scj-midx-build-not-pin
  (not (fn-gidx-pinp (fn-midx-build arts)))
  :hints (("Goal" :use ((:instance fn-scj-branchesp-of-midx-build))
           :in-theory (e/d (fn-gidx-pinp) (fn-scj-branchesp-of-midx-build fn-midx-build)))))

(defthm fn-scj-not-pin-when-midx
  (implies (fn-midx-correspondencep idx arts) (not (fn-gidx-pinp idx)))
  :hints (("Goal" :in-theory (e/d (fn-midx-correspondencep) (fn-gidx-pinp fn-midx-build)))))

; The live view over a catalog joined to it, from the view's own facts.
(defthm fn-scj-live-okp-of-joined-view
  (implies (and (fn-scj-joinp view fn-arena fn-cat)
                (fn-cnx-freshp fn-cat)
                (fn-nntp-projectionp (fn-own-view-archive view))
                (fn-midx-correspondencep (fn-own-view-index view)
                                         (fn-state-articles (fn-own-view-archive view)))
                (equal (fn-own-view-group-index view)
                       (fn-gidx-build (fn-state-articles (fn-own-view-archive view)))))
           (fn-scj-live-okp view fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-scj-live-okp fn-scr-live-catalogp fn-scr-fields-catalogp
                                   fn-scr-catalogp fn-scj-joinp fn-gidx-pin-correspondencep)
                                  (fn-scr-view-of fn-cat-view-articles fn-midx-build fn-gidx-pinp
                                   fn-midx-correspondencep
                                   fn-nntp-projectionp fn-gidx-build fn-cnx-freshp fn-scj-midx-build-not-pin))
           :use ((:instance fn-scj-view-of-when-seqs-below (version (fn-own-view-version view)))
                 (:instance fn-scj-midx-build-not-pin
                            (arts (fn-state-articles (fn-own-view-archive view))))))))

(defthm fn-scj-conns-pinp-of-nil
  (fn-scj-conns-pinp nil fn-arena fn-cat)
  :hints (("Goal" :in-theory (enable fn-scj-conns-pinp))))

(defthm fn-scj-ock-install-conns
  (implies (not (equal (fn-ock-install replayed opened max-conns) :fault))
           (equal (fn-own-conns (fn-ocfg-owner (fn-ock-install replayed opened max-conns))) nil))
  :hints (("Goal" :in-theory (e/d (fn-ock-install) (fn-own-start fn-own-configure)))))

; KEYSTONE (E for the invariant at the opens).  The owner fn-ock-install
; builds (every open: fn-ock-recover-extended, fn-ock-recover-full) with the
; catalog the host loads from its store's rows under its view's index
; satisfies fn-scj-invp, given the join there (step 1:
; fn-scj-joinp-at-recover, fn-scj-joinp-at-full-open) and the view's archive
; a projection.
(defthm fn-scj-invp-at-install
  (let* ((oc (fn-ock-install replayed opened max-conns))
         (o (fn-ocfg-owner oc))
         (c (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                   (fn-own-view-index (fn-own-view o)) fn-arena fn-cat)))
    (implies (and (not (equal oc :fault))
                  (fn-own-store-idlep (fn-own-store o))
                  (true-listp (fn-sf-records (fn-sn-files (fn-own-store o))))
                  (fn-scj-joinp (fn-own-view o) fn-arena c)
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view o))))
             (fn-scj-invp o fn-arena c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scj-invp fn-scj-view-currentp fn-scar-view-indexedp)
                           (fn-ock-install fn-own-start fn-sca-load-held-rows fn-scj-joinp
                            fn-own-store-idlep fn-scj-vvp fn-scj-live-okp fn-scj-rows-invp
                            fn-midx-correspondencep fn-gidx-build fn-own-configure))
           :use ((:instance fn-scj-ock-install-owner)
                 (:instance fn-scj-installed-view-current-and-indexed)
                 (:instance fn-scj-own-start-vvp (store (fn-sn-open-state opened)))
                 (:instance fn-scj-own-start-group-index (store (fn-sn-open-state opened)))
                 (:instance fn-scj-ock-install-conns)
                 (:instance fn-scj-vvp-by-view-and-store
                            (o (fn-ocfg-owner (fn-ock-install replayed opened max-conns)))
                            (p (fn-own-start (fn-sn-open-state opened) max-conns)))
                 (:instance fn-scj-rows-invp-of-load
                            (events (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))))
                            (idx (fn-own-view-index (fn-own-view (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))))
                 (:instance fn-scj-live-okp-of-joined-view
                            (view (fn-own-view (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))
                            (fn-cat (fn-sca-load-held-rows
                                     (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner (fn-ock-install replayed opened max-conns)))))
                                     (fn-own-view-index (fn-own-view (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))
                                     fn-arena fn-cat)))))))

; KEYSTONE (E at recovery and the checkpoint open: the owner
; host/owner-host.lisp fn-owner-install-extended installs and the catalog it
; loads).
(defthm fn-scj-invp-at-recover
  (let* ((oc (fn-ock-recover-extended
              (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
              configs frontier max-conns))
         (o (fn-ocfg-owner oc))
         (rows (fn-sf-records (fn-sn-files (fn-own-store o)))))
    (implies (and (not (equal oc :fault))
                  (fn-arena-p fn-arena)
                  (fn-rows-handles-inp (append prefix suffix) fn-arena)
                  (fn-rows-composites-okp (append prefix suffix) fn-arena)
                  (fn-scj-rows-clearp (append prefix suffix))
                  (true-listp suffix)
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view o))))
             (fn-scj-invp o fn-arena
                          (fn-sca-load-held-rows rows (fn-own-view-index (fn-own-view o))
                                                 fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ock-recover-extended true-listp-append)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-joinp-at-recover)
                 (:instance fn-sca-ocl-relation-at-recover
                            (view-index (fn-own-view-index
                                         (fn-own-view (fn-ocfg-owner
                                                       (fn-ock-recover-extended
                                                        (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                                        configs frontier max-conns))))))
                 (:instance fn-scj-invp-at-install
                            (replayed (fn-sco-cpr-finish
                                       (fn-sco-cpr (fn-sco-extend (fn-sco-capture configs prefix) configs suffix))
                                       configs))
                            (opened (fn-sco-finalize
                                     (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                     configs frontier)))))))

(local (defthm fn-scj-arena-p-of-clear-inv
   (fn-arena-p (fn-arena-clear fn-arena))
   :hints (("Goal" :in-theory (enable fn-arena-clear)))))

(defthm fn-scj-intern-events-true-listp
  (implies (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad))
           (true-listp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (union-theories '(fn-intern-events true-listp mv-nth car-cons cdr-cons
                                        (:induction fn-intern-events)
                                        (:executable-counterpart equal)
                                        (:executable-counterpart true-listp)
                                        (:executable-counterpart zp) (:executable-counterpart not))
                                      (theory 'minimal-theory)))))

; KEYSTONE (E at the full open: the rows the open interns from the decoded
; journal into the cleared arena and the catalog loaded from them).
(defthm fn-scj-invp-at-full-open
  (let* ((arena0 (fn-arena-clear fn-arena))
         (rows (mv-nth 0 (fn-intern-events ws nil 0 arena0)))
         (arena (mv-nth 1 (fn-intern-events ws nil 0 arena0)))
         (oc (fn-ock-recover-extended
              (fn-sco-extend (fn-sco-capture configs nil) configs rows)
              configs frontier max-conns))
         (o (fn-ocfg-owner oc)))
    (implies (and (true-listp ws)
                  (not (equal rows :bad))
                  (not (equal oc :fault))
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view o))))
             (fn-scj-invp o arena
                          (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                                 (fn-own-view-index (fn-own-view o))
                                                 arena fn-cat))))
  :hints (("Goal" :use ((:instance fn-scj-invp-at-recover
                                   (prefix nil)
                                   (suffix (mv-nth 0 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena))))
                                   (fn-arena (mv-nth 1 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena)))))
                        (:instance fn-scj-intern-events-rows-clear
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-scj-intern-events-true-listp
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-sca-intern-events-accepts-wire-events
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-intern-events-arena-p
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-intern-events-handles-in
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-sca-intern-events-composites-okp
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(binary-append fn-scj-arena-p-of-clear-inv
                                        (:executable-counterpart natp)
                                        (:executable-counterpart consp))))))

; -----------------------------------------------------------------------------
; The host's article finish (step 2 with steps 3 and VV).

(defthm fn-scj-vvp-of-host-finish
  (implies (and (fn-ccar-completion-enabledp (fn-own-store o))
                (fn-own-store-idlep (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena)))))
           (fn-scj-vvp (cdr (fn-ccar-own-finish o cfg fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-scj-vvp) (fn-own-refresh fn-ccar-own-finish fn-own-store-idlep
                                               fn-scj-vvp-of-idle-refresh))
           :use ((:instance fn-scj-host-finish-view-and-store)
                 (:instance fn-scj-vvp-of-idle-refresh
                            (o (fn-crf-with-store o (fn-ccar-sn-finish-enabled (fn-own-store o)))))
                 (:instance fn-scj-own-refresh-store
                            (x (fn-crf-with-store o (fn-ccar-sn-finish-enabled (fn-own-store o)))))))))

(defthm fn-scj-version-of-host-finish
  (implies (and (fn-ccar-completion-enabledp (fn-own-store o))
                (fn-own-store-idlep (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena)))))
           (equal (fn-own-view-version (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena))))
                  (len (fn-sf-records (fn-sn-files (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena))))))))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh fn-crf-with-store)
                                  (fn-ccar-own-finish fn-own-store-idlep fn-ctl-refresh-visible
                                   fn-ctl-refresh-withdrawals fn-ctl-refresh-withdrawn fn-midx-refresh
                                   fn-gidx-refresh fn-ctl-visible-state-of))
           :use ((:instance fn-scj-host-finish-view-and-store)))))

; KEYSTONE (the invariant across the host's article finish).  The owner
; host/owner-host.lisp fn-owner-finish-submission installs
; (fn-ccar-own-finish; fn-apc-own-finish-is-ccar-own-finish) with the
; catalog after fn-sca-finish satisfies fn-scj-invp, and keeps the
; catalog's sorted sequences and fresh numbers: step 2
; (fn-scj-joinp-at-host-finish), step 3 (fn-scj-owner-catalogp-at-host-
; finish) and VV of the idle refresh.  The hypotheses are step 2's and step
; 3's; the ones the invariant carries (join, pins, live view, VV) enter
; through fn-scj-invp.
(defthm fn-scj-invp-at-host-finish
  (let* ((view (fn-own-view o))
         (o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (a (car (fn-state-articles acc2)))
         (events2 (append events0 (list event)))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid held)
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (and (fn-ccar-completion-enabledp (fn-own-store o))
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
                  (equal (fn-state-articles acc2) (cons a (fn-own-view-raw view)))
                  (equal (fn-sn-verdicts s2)
                         (cons (cons (fn-article-msgid a) verdict) (fn-own-view-verdicts view)))
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
                  (fn-own-view-okp view2 (fn-sn-groups s2) (fn-sn-capacity s2)
                                   (fn-sf-records (fn-sn-files s2)))
                  (fn-nntp-projectionp (fn-own-view-archive view2)))
             (and (fn-scj-invp o2 fn-arena c2)
                  (fn-scj-seqs-sortedp c2)
                  (fn-cnx-freshp c2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-invp fn-scj-take-of-len true-listp-append
                                        (:executable-counterpart true-listp) true-listp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-joinp-at-host-finish)
                 (:instance fn-scj-owner-catalogp-at-host-finish)
                 (:instance fn-scj-vvp-of-host-finish)
                 (:instance fn-scj-version-of-host-finish)))))

; PRF-202's verdict equation at the host's article finish: the store's
; verdicts grow by exactly the completed row's pair.
(defthm fn-scj-verdicts-of-article-finish
  (let ((r (fn-ccar-completion-record s)))
    (implies (and (not (fn-evc-retentionp r)) (not (fn-evc-consumerp r)) (not (fn-evc-topicp r))
                  (not (fn-evc-stxep r)) (not (fn-evc-stxkp r)) (not (fn-evc-stxap r)))
             (equal (fn-sn-verdicts (fn-ccar-sn-finish-enabled s))
                    (cons (cons (fn-record-msgid r) (fn-hc-verdict (fn-held-context r)))
                          (fn-sn-verdicts s)))))
  :hints (("Goal" :in-theory (e/d (fn-ccar-sn-finish-enabled fn-sn-update-accepted
                                   fn-sn-advance-identity-next fn-sn-with-topic fn-sn-with-consumer)
                                  (fn-sn-make-v6 fn-node-complete fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-sf-core-completion
                                   fn-sf-emit-success fn-stx-index-add fn-ccar-accepted-delta
                                   fn-ccar-cpe-projection-step fn-ccar-th-prefix-step
                                   fn-evc-retentionp fn-evc-consumerp fn-evc-topicp
                                   fn-evc-stxep fn-evc-stxkp fn-evc-stxap)))))

; The article the finish installs names the completed row's Message-ID.
(defthm fn-scj-msgid-of-held-wire
  (equal (fn-record-msgid (fn-held-wire r p)) (fn-record-msgid r))
  :hints (("Goal" :in-theory (enable fn-held-wire))))

(defthm fn-scj-msgid-of-pending-record
  (equal (fn-record-msgid (fn-sn-pending-record node seq))
         (fn-pending-msgid (fn-state-pending (fn-node-acceptance node))))
  :hints (("Goal" :in-theory (enable fn-sn-pending-record))))

(defthm fn-scj-msgid-of-bound-row
  (implies (equal (fn-held-wire r p) (fn-sn-pending-record node seq))
           (equal (fn-record-msgid r)
                  (fn-pending-msgid (fn-state-pending (fn-node-acceptance node)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-held-wire fn-sn-pending-record fn-scj-msgid-of-held-wire
                                      fn-scj-msgid-of-pending-record)
           :use (fn-scj-msgid-of-held-wire fn-scj-msgid-of-pending-record))))

(defthm fn-scj-node-complete-articles
  (implies (and (fn-node-pending-matchesp node txid generation)
                (fn-statep (fn-node-acceptance node)))
           (equal (fn-state-articles (fn-node-acceptance (fn-node-complete node txid generation :durable)))
                  (cons (fn-article-from-pending (fn-state-pending (fn-node-acceptance node)))
                        (fn-state-articles (fn-node-acceptance node)))))
  :hints (("Goal" :in-theory (e/d (fn-node-complete fn-accept-complete fn-install-pending
                                   fn-node-pending-matchesp)
                                  (fn-article-from-pending fn-statep fn-pending-matchesp)))))

(defthm fn-scj-node-of-article-finish
  (let ((r (fn-ccar-completion-record s)))
    (implies (and (not (fn-evc-retentionp r)) (not (fn-evc-consumerp r)) (not (fn-evc-topicp r))
                  (not (fn-evc-stxep r)) (not (fn-evc-stxkp r)) (not (fn-evc-stxap r)))
             (equal (fn-sn-node (fn-ccar-sn-finish-enabled s))
                    (fn-node-complete (fn-sn-node s) (fn-record-txid r) (fn-record-generation r) :durable))))
  :hints (("Goal" :in-theory (e/d (fn-ccar-sn-finish-enabled fn-sn-update-accepted
                                   fn-sn-advance-identity-next fn-sn-with-topic fn-sn-with-consumer)
                                  (fn-sn-make-v6 fn-node-complete fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-sf-core-completion
                                   fn-sf-emit-success fn-stx-index-add fn-ccar-accepted-delta
                                   fn-ccar-cpe-projection-step fn-ccar-th-prefix-step
                                   fn-evc-retentionp fn-evc-consumerp fn-evc-topicp
                                   fn-evc-stxep fn-evc-stxkp fn-evc-stxap fn-ccar-completion-record)))))

(defthm fn-scj-bindsp-of-article-core
  (let ((r (fn-ccar-completion-record s)))
    (implies (and (fn-ccar-completion-core-enabledp s)
                  (not (fn-evc-retentionp r)) (not (fn-evc-consumerp r)) (not (fn-evc-topicp r))
                  (not (fn-evc-stxep r)) (not (fn-evc-stxkp r)) (not (fn-evc-stxap r)))
             (fn-ccar-sn-record-bindsp (fn-sn-node s) r)))
  :hints (("Goal" :in-theory (union-theories '(fn-ccar-completion-core-enabledp) (theory 'minimal-theory)))))

; PRF-202's acceptance equation at the host's article finish: the store's
; acceptance grows by exactly one article, the completed row's Message-ID.
(defthm fn-scj-acceptance-of-article-finish
  (let* ((r (fn-ccar-completion-record s))
         (a (fn-article-from-pending (fn-state-pending (fn-node-acceptance (fn-sn-node s))))))
    (implies (and (fn-ccar-completion-core-enabledp s)
                  (fn-statep (fn-node-acceptance (fn-sn-node s)))
                  (not (fn-evc-retentionp r)) (not (fn-evc-consumerp r)) (not (fn-evc-topicp r))
                  (not (fn-evc-stxep r)) (not (fn-evc-stxkp r)) (not (fn-evc-stxap r)))
             (equal (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-ccar-sn-finish-enabled s))))
                    (cons a (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))))
  :hints (("Goal" :in-theory (union-theories '(fn-ccar-sn-record-bindsp) (theory 'minimal-theory))
           :use ((:instance fn-scj-node-of-article-finish)
                 (:instance fn-scj-bindsp-of-article-core)
                 (:instance fn-scj-node-complete-articles
                            (node (fn-sn-node s))
                            (txid (fn-record-txid (fn-ccar-completion-record s)))
                            (generation (fn-record-generation (fn-ccar-completion-record s))))))))

(defthm fn-scj-installed-article-msgid
  (let* ((r (fn-ccar-completion-record s))
         (a (fn-article-from-pending (fn-state-pending (fn-node-acceptance (fn-sn-node s))))))
    (implies (and (fn-ccar-completion-core-enabledp s)
                  (not (fn-evc-retentionp r)) (not (fn-evc-consumerp r)) (not (fn-evc-topicp r))
                  (not (fn-evc-stxep r)) (not (fn-evc-stxkp r)) (not (fn-evc-stxap r)))
             (equal (fn-article-msgid a) (fn-record-msgid r))))
  :hints (("Goal" :in-theory (union-theories '(fn-ccar-sn-record-bindsp fn-article-from-pending
                                               fn-make-article fn-article-msgid car-cons fn-ag-car)
                                             (theory 'minimal-theory))
           :use ((:instance fn-scj-bindsp-of-article-core)
                 (:instance fn-scj-msgid-of-bound-row
                            (r (fn-ccar-completion-record s))
                            (p (fn-record-payload (fn-ccar-completion-record s)))
                            (node (fn-sn-node s))
                            (seq (fn-record-sequence (fn-ccar-completion-record s))))))))

(defthm fn-scj-vvp-parts
  (implies (fn-scj-vvp o)
           (and (equal (fn-own-view-raw (fn-own-view o))
                       (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store o)))))
                (equal (fn-own-view-verdicts (fn-own-view o)) (fn-sn-verdicts (fn-own-store o)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scj-vvp))))

(defthm fn-scj-invp-gives-vvp
  (implies (fn-scj-invp o fn-arena fn-cat) (fn-scj-vvp o))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scj-invp))))

(defthm fn-scj-enabled-gives-core
  (implies (fn-ccar-completion-enabledp s) (fn-ccar-completion-core-enabledp s))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-ccar-completion-enabledp))))

; KEYSTONE (the invariant across the host's article finish, PRF-202's two
; equations discharged).  fn-scj-invp-at-host-finish with the acceptance and
; verdict equations derived: under VV the view's raw list and verdicts are
; the store's, and an article completion conses the installed article
; (Message-ID the completed row's) and its verdict pair
; (fn-scj-acceptance-of-article-finish, fn-scj-installed-article-msgid,
; fn-scj-verdicts-of-article-finish).
(defthm fn-scj-invp-at-host-article-finish
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
                  (fn-statep (fn-node-acceptance (fn-sn-node s)))
                  (not (fn-evc-retentionp r)) (not (fn-evc-consumerp r)) (not (fn-evc-topicp r))
                  (not (fn-evc-stxep r)) (not (fn-evc-stxkp r)) (not (fn-evc-stxap r))
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
                  (fn-own-view-okp view2 (fn-sn-groups s2) (fn-sn-capacity s2)
                                   (fn-sf-records (fn-sn-files s2)))
                  (fn-nntp-projectionp (fn-own-view-archive view2)))
             (and (fn-scj-invp o2 fn-arena c2)
                  (fn-scj-seqs-sortedp c2)
                  (fn-cnx-freshp c2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(car-cons) (theory 'minimal-theory))
           :use ((:instance fn-scj-enabled-gives-core (s (fn-own-store o)))
                 (:instance fn-scj-invp-at-host-finish
                            (verdict (fn-hc-verdict (fn-held-context (fn-ccar-completion-record (fn-own-store o))))))
                 (:instance fn-scj-invp-gives-vvp)
                 (:instance fn-scj-vvp-parts)
                 (:instance fn-scj-host-finish-view-and-store)
                 (:instance fn-scj-acceptance-of-article-finish (s (fn-own-store o)))
                 (:instance fn-scj-installed-article-msgid (s (fn-own-store o)))
                 (:instance fn-scj-verdicts-of-article-finish (s (fn-own-store o)))))))

; The same at the identity finish: host/owner-host.lisp
; fn-owner-finish-identity installs fn-rix-ocfg-complete, which is the
; article finish's owner (fn-scj-identity-finish-owner-is-article-finish-
; owner), then runs the same fn-sca-finish.  The signed composite's
; acceptance and verdict equations stay hypotheses here (the identity
; replay's, fn-sn-finish-identity).
(defthm fn-scj-invp-at-identity-finish
  (let* ((o (fn-ocfg-owner oc))
         (view (fn-own-view o))
         (o2 (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (a (car (fn-state-articles acc2)))
         (events2 (append events0 (list event)))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid held)
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (and (fn-hist-of-storep fn-hist (fn-own-store o))
                  (not (fn-ocfg-staged oc))
                  (fn-sn-completion-enabledp (fn-own-store o))
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
                  (equal (fn-state-articles acc2) (cons a (fn-own-view-raw view)))
                  (equal (fn-sn-verdicts s2)
                         (cons (cons (fn-article-msgid a) verdict) (fn-own-view-verdicts view)))
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
                  (fn-own-view-okp view2 (fn-sn-groups s2) (fn-sn-capacity s2)
                                   (fn-sf-records (fn-sn-files s2)))
                  (fn-nntp-projectionp (fn-own-view-archive view2)))
             (and (fn-scj-invp o2 fn-arena c2)
                  (fn-scj-seqs-sortedp c2)
                  (fn-cnx-freshp c2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ocfg-with-owner fn-ocfg-make fn-ocfg-owner car-cons
                                        fn-ccar-completion-enabledp-is-reference)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-identity-finish-owner-is-article-finish-owner (cfg (fn-ocfg-config oc)))
                 (:instance fn-scj-invp-at-host-finish (o (fn-ocfg-owner oc)) (cfg (fn-ocfg-config oc)))))))

; -----------------------------------------------------------------------------
; The article finish over the carried facts: the history before the in-flight
; event is fn-scjs-seenp's (fn-scjs-rows-invp-before-in-flight), the event is
; the history's last record, the finish keeps the history.

(defthm fn-scj-records-of-ccar-finish
  (equal (fn-sf-records (fn-sn-files (fn-ccar-sn-finish-enabled s)))
         (fn-sf-records (fn-sf-emit-success (fn-sf-core-completion (fn-sn-files s)
                                                                   (fn-evc-sequence (fn-ccar-completion-record s))
                                                                   (fn-evc-txid (fn-ccar-completion-record s)))
                                            (fn-evc-sequence (fn-ccar-completion-record s))
                                            (fn-evc-txid (fn-ccar-completion-record s)))))
  :hints (("Goal" :in-theory (e/d (fn-ccar-sn-finish-enabled fn-sn-update-accepted fn-sn-update-indexed
                                   fn-sn-finish-identity fn-sn-advance-identity-next fn-sn-with-topic
                                   fn-sn-with-consumer)
                                  (fn-sn-make-v6 fn-node-complete fn-replay-apply-record
                                   fn-replay-apply-retention-event fn-sf-core-completion
                                   fn-sf-emit-success fn-stx-index-add fn-ccar-accepted-delta
                                   fn-ccar-cpe-projection-step fn-ccar-th-prefix-step
                                   fn-replay-identity-step fn-replay-verdict-pairs)))))

(defthm fn-scj-snoc-of-butlast-last
  (implies (and (consp r) (true-listp r))
           (equal (append (butlast r 1) (list (car (last r)))) r)))

(defthm fn-scj-records-kept-by-ccar-finish
  (equal (fn-sf-records (fn-sn-files (fn-ccar-sn-finish-enabled s)))
         (fn-sf-records (fn-sn-files s)))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-records-of-ccar-finish fn-sf-records-of-emit-success
                                               fn-sf-records-of-core-completion)
                                             (theory 'minimal-theory)))))

(defthm fn-scj-host-finish-store
  (implies (fn-ccar-completion-enabledp (fn-own-store o))
           (equal (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena)))
                  (fn-ccar-sn-finish-enabled (fn-own-store o))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-scj-host-finish-view-and-store))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

(defthm fn-scj-true-listp-butlast
  (true-listp (butlast x n)))

(defthm fn-scj-enabled-is-completing
  (implies (fn-ccar-completion-enabledp s)
           (equal (fn-sf-phase (fn-sn-files s)) :completing))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-ccar-completion-enabledp fn-ccar-completion-core-enabledp))))

; KEYSTONE (the invariant across the host's article finish, over the carried
; facts).  fn-scj-invp-at-host-article-finish with the history before the
; in-flight event read off fn-scjs-seenp (fn-scjs-rows-invp-before-in-flight):
; EVENTS0 is the store's history less its last record, EVENT that record.
(defthm fn-scj-invp-at-host-article-finish-carried
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
                  (fn-own-view-okp view2 (fn-sn-groups s2) (fn-sn-capacity s2)
                                   (fn-sf-records (fn-sn-files s2)))
                  (fn-nntp-projectionp (fn-own-view-archive view2)))
             (and (fn-scj-invp o2 fn-arena c2)
                  (fn-scj-seqs-sortedp c2)
                  (fn-cnx-freshp c2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-versions-okp fn-scjs-historyp fn-scj-true-listp-butlast nfix natp (:type-prescription len))
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-enabled-is-completing (s (fn-own-store o)))
                 (:instance fn-scjs-rows-invp-before-in-flight)
                 (:instance fn-scj-host-finish-store)
                 (:instance fn-scj-records-kept-by-ccar-finish (s (fn-own-store o)))
                 (:instance fn-scj-snoc-of-butlast-last (r (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-scj-invp-at-host-article-finish
                            (events0 (butlast (fn-sf-records (fn-sn-files (fn-own-store o))) 1))
                            (event (car (last (fn-sf-records (fn-sn-files (fn-own-store o)))))))))))

; -----------------------------------------------------------------------------
; The host's read entry since owner-time-model: host/owner-host.lisp calls
; fn-otm-read-span (books/owner-time-admission.lisp), which is
; fn-orr-read-span when admitted and, when shed, the same read with the
; connection's posting allowance switched off and restored -- a field of the
; connection's configuration, which no pin reads -- and the disk-slow
; posture's entry pushed on and stripped from the owner's refused-offer
; memory, which the invariant does not read (batch AY's shape: the gate's
; value S, fn-otm-admit-post; lane sca-join-5 re-proved it).

(defthm fn-scj-conn-pin-fields-of-update-6
  (implies (< 6 (len c))
           (and (equal (fn-own-conn-archive (update-nth 6 v c)) (fn-own-conn-archive c))
                (equal (fn-own-conn-version (update-nth 6 v c)) (fn-own-conn-version c))
                (equal (fn-own-conn-index (update-nth 6 v c)) (fn-own-conn-index c))
                (equal (fn-own-conn-group-index (update-nth 6 v c)) (fn-own-conn-group-index c))
                (equal (fn-own-conn-control (update-nth 6 v c)) (fn-own-conn-control c))))
  :hints (("Goal" :in-theory (enable fn-own-conn-archive fn-own-conn-version fn-own-conn-index
                                     fn-own-conn-group-index fn-own-conn-control update-nth
                                     fn-ag-car fn-ag-cdr)
           :expand ((:free (v) (update-nth 6 v c)) (:free (v) (update-nth 5 v (cdr c)))
                    (:free (v) (update-nth 4 v (cddr c))) (:free (v) (update-nth 3 v (cdddr c)))
                    (:free (v) (update-nth 2 v (cddddr c)))
                    (:free (v) (update-nth 1 v (cdr (cddddr c))))
                    (:free (v) (update-nth 0 v (cddr (cddddr c))))))))

(defthm fn-scj-conn-pinp-of-with-allow
  (equal (fn-scj-conn-pinp (fn-otm-conn-with-allow c allow) fn-arena fn-cat)
         (fn-scj-conn-pinp c fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-otm-conn-with-allow fn-scj-conn-pinp fn-scj-conn-pinned-index
                                               fn-scj-conn-pin-fields-of-update-6)
                                             (theory 'minimal-theory)))))

(defthm fn-scj-invp-of-otm-owner-with-allow
  (implies (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
           (fn-scj-invp (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-otm-owner-with-allow)
                                  (fn-otm-conn-with-allow fn-scj-invp fn-own-set-conns fn-own-replace-conn))
           :use ((:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-conns-pinp-find (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-scj-invp-of-own-set-conns
                            (o (fn-ocfg-owner oc))
                            (conns (fn-own-replace-conn
                                    (fn-otm-conn-with-allow (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))
                                                            allow)
                                    (fn-own-conns (fn-ocfg-owner oc)))))))))

(defthm fn-scj-invp-of-otm-ocfg-with-refused
  (equal (fn-scj-invp (fn-ocfg-owner (fn-otm-ocfg-with-refused oc mem)) fn-arena fn-cat)
         (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat))
  :hints (("Goal" :in-theory (enable fn-otm-ocfg-with-refused fn-scj-invp fn-scj-vvp))))

(defthm fn-scj-invp-of-otm-shed-ocfg
  (implies (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
           (fn-scj-invp (fn-ocfg-owner (fn-otm-shed-ocfg oc id)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-otm-shed-ocfg fn-scj-invp-of-otm-ocfg-with-refused
                                               fn-scj-invp-of-otm-owner-with-allow)
                                             (theory 'minimal-theory)))))

(defthm fn-scj-invp-of-otm-unshed-ocfg
  (implies (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
           (fn-scj-invp (fn-ocfg-owner (fn-otm-unshed-ocfg oc id allow)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-otm-unshed-ocfg fn-scj-invp-of-otm-ocfg-with-refused
                                               fn-scj-invp-of-otm-owner-with-allow)
                                             (theory 'minimal-theory)))))

(defthm fn-scj-otm-read-span-owner
  (equal (fn-ocfg-owner (fn-own-tls-result-owner
                         (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat)))
         (if (eq (fn-otm-admit-post s) :shed)
             (fn-ocfg-owner
              (fn-otm-unshed-ocfg
               (fn-own-tls-result-owner
                (fn-orr-read-span (fn-otm-shed-ocfg oc id) views id i end
                                  fn-octets fn-arena fn-cat))
               id (fn-otm-conn-allow oc id)))
           (fn-ocfg-owner (fn-own-tls-result-owner
                           (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat)))))
  :hints (("Goal" :in-theory (union-theories '(fn-otm-read-span fn-scj-tls-result-owner-of-make)
                                             (theory 'minimal-theory)))))

; KEYSTONE (the host's read entry keeps the invariant).
(defthm fn-scj-invp-of-otm-read-span
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (implies (consp views) (fn-scj-live-okp (car views) fn-arena fn-cat)))
           (fn-scj-invp (fn-ocfg-owner (fn-own-tls-result-owner
                                        (fn-otm-read-span oc views id i end s
                                                          fn-octets fn-arena fn-cat)))
                        fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-otm-read-span-owner) (theory 'minimal-theory))
           :use ((:instance fn-scj-invp-of-orr-read-span)
                 (:instance fn-scj-invp-of-orr-read-span (oc (fn-otm-shed-ocfg oc id)))
                 (:instance fn-scj-invp-of-otm-shed-ocfg)
                 (:instance fn-scj-invp-of-otm-unshed-ocfg
                            (oc (fn-own-tls-result-owner
                                 (fn-orr-read-span (fn-otm-shed-ocfg oc id) views id i end
                                                   fn-octets fn-arena fn-cat)))
                            (allow (fn-otm-conn-allow oc id)))))))

; The premise of books/owner-reader-read.lisp's keystone
; fn-orr-read-span-at-a-captured-view-restores-the-owner (the catalog at the
; owner with the captured view in place) from the invariant and the captured
; view's being live over the catalog.
(defthm fn-scj-captured-owner-catalogp
  (implies (and (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-scj-live-okp v fn-arena fn-cat))
           (fn-scr-owner-catalogp (fn-ocfg-owner (fn-ocfg-with-view oc v)) id fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                 (:instance fn-orr-with-view-fields)
                 (:instance fn-scj-owner-catalogp-of-conns-and-live
                            (o (fn-ocfg-owner (fn-ocfg-with-view oc v))))))))

; A captured reader view stays live across the catalog's finish, like any
; pin at or below the completed row's sequence.
(defthm fn-scj-live-okp-of-finish
  (let ((c2 (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat))))
    (implies (and (fn-scj-live-okp v fn-arena fn-cat)
                  (fn-scj-seqs-sortedp fn-cat)
                  (fn-scj-seqs-below fn-cat (fn-record-sequence (fn-pc-held pending)))
                  (<= (nfix (fn-own-view-version v)) (nfix (fn-record-sequence (fn-pc-held pending)))))
             (fn-scj-live-okp v fn-arena c2)))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-live-okp fn-scr-live-catalogp fn-scr-fields-catalogp
                                               fn-own-view-live-fields fn-served-pinned-version
                                               fn-served-pinned-make fn-ag-car car-cons)
                                             (theory 'minimal-theory))
           :use ((:instance fn-scj-catalogp-of-finish
                            (archive (fn-own-view-archive v))
                            (index (if (fn-own-view-group-index v)
                                       (fn-gidx-pin-with-control (fn-own-view-index v)
                                                                 (fn-own-view-group-index v)
                                                                 (fn-own-view-control v))
                                     (fn-own-view-index v)))
                            (v (fn-own-view-version v)))))))
