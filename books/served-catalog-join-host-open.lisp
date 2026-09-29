; served-catalog-join-host-open.lisp -- the catalog join established at the
; host's install, every open (lane join-f2, 2026-09-28; PRF-302).
;
; host/owner-host.lisp fn-owner-install-extended installs the owner
; fn-ock-install builds, clears the catalog's pending row and loads the
; catalog from the installed store's rows under the view's index
; (fn-sca-load-held-rows): fn-sjh-okp holds there with no pending row.

(in-package "ACL2")

(include-book "served-catalog-join-host")

(local (in-theory (disable (tau-system))))

(defthm fn-sjh-idle-files-okp
  (implies (and (fn-own-store-idlep s)
                (fn-rows-composites-okp (fn-sf-records (fn-sn-files s)) fn-arena)
                (fn-rows-handles-inp (fn-sf-records (fn-sn-files s)) fn-arena)
                (fn-scj-rows-clearp (fn-sf-records (fn-sn-files s))))
           (fn-sjh-files-okp (fn-sn-files s) nil fn-arena fn-cat))
  :hints (("Goal" :in-theory (enable fn-sjh-files-okp fn-sjh-files-linkp fn-sjh-inflight fn-sf-record-phasep
                                     fn-own-store-idlep fn-snt-idle-phasep))))

(defthm fn-sjh-current-view-seen-and-history
  (implies (and (fn-scj-view-currentp o)
                (fn-own-store-idlep (fn-own-store o))
                (true-listp (fn-sf-records (fn-sn-files (fn-own-store o)))))
           (and (fn-scjs-seenp o) (fn-scjs-historyp o)))
  :hints (("Goal" :in-theory (enable fn-scj-view-currentp fn-scjs-seenp fn-scjs-store-seenp
                                     fn-scjs-seen-records fn-scjs-historyp fn-own-store-idlep
                                     fn-snt-idle-phasep))))

(defthm fn-sjh-versions-okp-of-no-conns
  (implies (not (consp (fn-own-conns o))) (fn-scj-versions-okp o))
  :hints (("Goal" :in-theory (enable fn-scj-versions-okp fn-scj-conns-versions-atmostp))))

; KEYSTONE (fn-sjh-okp at the host's install).  host/owner-host.lisp
; fn-owner-install-extended installs the owner fn-ock-install builds (every
; open), clears the pending row and loads the catalog from the store's rows
; under the view's index: fn-sjh-okp holds with no pending row, given the join
; there (fn-scj-joinp-at-recover, -at-full-open) and the rows' facts the open
; establishes (below, at the full open).
(defthm fn-sjh-okp-at-install
  (let* ((oc (fn-ock-install replayed opened max-conns))
         (o (fn-ocfg-owner oc))
         (records (fn-sf-records (fn-sn-files (fn-own-store o))))
         (c (fn-sca-load-held-rows records (fn-own-view-index (fn-own-view o)) fn-arena fn-cat)))
    (implies (and (not (equal oc :fault))
                  (fn-ocl-relation oc)
                  (fn-own-store-idlep (fn-own-store o))
                  (true-listp records)
                  (fn-scj-joinp (fn-own-view o) fn-arena c)
                  (fn-rows-composites-okp records fn-arena)
                  (fn-rows-handles-inp records fn-arena)
                  (fn-scj-rows-clearp records))
             (fn-sjh-okp o nil fn-arena c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-okp fn-sjh-idle-files-okp fn-sjh-versions-okp-of-no-conns
                                        fn-scj-freshp-of-load fn-sjh-ocl-gives-cst fn-sjh-ocl-facts-for-prepare)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-invp-at-install)
                 (:instance fn-scj-installed-view-current-and-indexed)
                 (:instance fn-scj-ock-install-conns)
                 (:instance fn-sjh-current-view-seen-and-history
                            (o (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))
                 (:instance fn-scj-seqs-sortedp-at-open
                            (st (fn-own-store (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))
                            (idx (fn-own-view-index (fn-own-view (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))))))))

; KEYSTONE (the checkpoint open and recovery): the owner
; fn-owner-install-extended installs from a checkpoint's rows PREFIX and the
; replayed SUFFIX, with the catalog loaded from them: fn-sjh-okp with no
; pending row.  The rows' three facts (handles in the arena, well-formed
; composites, no withdrawal) are the checkpoint image's (named here; the full
; open below discharges them from the intern).
(defthm fn-sjh-okp-at-recover
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
                  (true-listp suffix))
             (fn-sjh-okp o nil fn-arena
                         (fn-sca-load-held-rows rows (fn-own-view-index (fn-own-view o))
                                                fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-ock-recover-extended true-listp-append)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-joinp-at-recover)
                 (:instance fn-ock-recover-installs-ocl-relation)
                 (:instance fn-sca-ocl-relation-at-recover
                            (view-index (fn-own-view-index
                                         (fn-own-view (fn-ocfg-owner
                                                       (fn-ock-recover-extended
                                                        (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                                        configs frontier max-conns))))))
                 (:instance fn-sjh-okp-at-install
                            (replayed (fn-sco-cpr-finish
                                       (fn-sco-cpr (fn-sco-extend (fn-sco-capture configs prefix) configs suffix))
                                       configs))
                            (opened (fn-sco-finalize
                                     (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                     configs frontier)))))))

(local (defthm fn-sjh-arena-p-of-clear
   (fn-arena-p (fn-arena-clear fn-arena))
   :hints (("Goal" :in-theory (enable fn-arena-clear)))))

; KEYSTONE (the full open): the rows the open interns from the decoded journal
; into the cleared arena and the catalog loaded from them: fn-sjh-okp with no
; pending row and no named hypothesis beyond the open's own success.
(defthm fn-sjh-okp-at-full-open
  (let* ((arena0 (fn-arena-clear fn-arena))
         (rows (mv-nth 0 (fn-intern-events ws nil 0 arena0)))
         (arena (mv-nth 1 (fn-intern-events ws nil 0 arena0)))
         (oc (fn-ock-recover-extended
              (fn-sco-extend (fn-sco-capture configs nil) configs rows)
              configs frontier max-conns))
         (o (fn-ocfg-owner oc)))
    (implies (and (true-listp ws)
                  (not (equal rows :bad))
                  (not (equal oc :fault)))
             (fn-sjh-okp o nil arena
                         (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                                (fn-own-view-index (fn-own-view o))
                                                arena fn-cat))))
  :hints (("Goal" :use ((:instance fn-sjh-okp-at-recover
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
                                      '(binary-append fn-sjh-arena-p-of-clear
                                        (:executable-counterpart natp)
                                        (:executable-counterpart consp))))))
