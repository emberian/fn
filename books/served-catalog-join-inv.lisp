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
