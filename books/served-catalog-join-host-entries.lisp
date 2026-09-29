; served-catalog-join-host-entries.lisp -- the catalog join carried across the
; host's remaining owner entries: the log route's composite io steps, the
; live configuration's completion and the opens (lane join-f2-2, 2026-09-29;
; PRF-302).

(in-package "ACL2")

(include-book "served-catalog-join-host-arms")
(include-book "served-catalog-join-host-read") ; fn-sjh-views-okp: the captured reader view
(include-book "owner-open-carried")   ; fn-ocar-ocfg-open, fn-ocar-exp-open: the opens the host calls
(include-book "owner-reader-view")    ; fn-ocfg-at-reader-view, fn-ocfg-with-view
(include-book "owner-log-route")      ; fn-olr-ocfg-reserve, fn-olr-ocfg-order
(include-book "config-owner-carried") ; fn-oclc-publish: the completion the host calls

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The log route (host/owner-host.lisp fn-owner-io's :log-reserve and
; :log-order): compositions of the store's io steps (fn-olr-ocfg-*-is-the-
; file-route-by-definition), each of which keeps fn-sjh-okp
; (fn-sjh-okp-of-ocfg-io) under the owner relation before it and a state view
; after it.

(defun fn-sjh-io-eventp (e)
  (declare (xargs :guard t))
  (and (true-listp e) (equal (len e) 2) (eq (car e) :store)
       (true-listp (cadr e)) (equal (len (cadr e)) 3) (eq (car (cadr e)) :io)))

(defun fn-sjh-io-eventsp (events)
  (declare (xargs :guard t))
  (if (consp events)
      (and (fn-sjh-io-eventp (car events)) (fn-sjh-io-eventsp (cdr events)))
    t))

(defun-nx fn-sjh-io-run-premisesp (oc events fn-arena)
  (declare (xargs :measure (len events)))
  (if (consp events)
      (let ((oc2 (fn-ocfg-step oc (car events) fn-arena)))
        (and (fn-ocl-relation oc)
             (fn-statep (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc2))))
             (fn-sjh-io-run-premisesp oc2 (cdr events) fn-arena)))
    t))

(defthm fn-sjh-io-eventp-shape
  (implies (fn-sjh-io-eventp e)
           (equal e (list :store (list :io (cadr (cadr e)) (caddr (cadr e))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sjh-io-eventp)
           :expand ((len e) (len (cdr e)) (len (cadr e)) (len (cdr (cadr e))) (len (cddr (cadr e)))))))


(defthm fn-sjh-okp-of-ocfg-io-run
  (implies (and (fn-sjh-io-eventsp events)
                (fn-sjh-io-run-premisesp oc events fn-arena)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat))
           (fn-sjh-okp (fn-ocfg-owner (fn-ocfg-run oc events fn-arena)) pending fn-arena fn-cat))
  :hints (("Goal" :induct (fn-ocfg-run oc events fn-arena)
           :in-theory (e/d (fn-ocfg-run fn-sjh-io-eventsp fn-sjh-io-run-premisesp)
                           (fn-ocfg-step fn-sjh-okp fn-ocl-relation fn-sjh-io-eventp)))
          ("Subgoal *1/1" :use ((:instance fn-sjh-io-eventp-shape (e (car events)))
                                (:instance fn-sjh-okp-of-ocfg-io
                                           (operation (cadr (cadr (car events))))
                                           (result (caddr (cadr (car events)))))))))

(defconst *fn-sjh-log-reserve-events*
  '((:store (:io :start-frontier nil)) (:store (:io :frontier-file :ok))
    (:store (:io :frontier-replace :ok)) (:store (:io :frontier-directory :ok))))
(defconst *fn-sjh-log-order-events*
  '((:store (:io :record-file :ok)) (:store (:io :record-link :ok))
    (:store (:io :record-directory :ok))))

; KEYSTONE (fn-owner-io :log-reserve).
(defthm fn-sjh-okp-at-owner-log-reserve
  (implies (and (fn-sjh-io-run-premisesp oc *fn-sjh-log-reserve-events* fn-arena)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat))
           (fn-sjh-okp (fn-ocfg-owner (fn-olr-ocfg-reserve oc)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-olr-ocfg-reserve-is-the-file-route-by-definition
                                               fn-ocfg-run car-cons cdr-cons (:e fn-sjh-io-eventsp)
                                               (:e consp) (:e car) (:e cdr))
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-of-ocfg-io-run (events *fn-sjh-log-reserve-events*))))))

; KEYSTONE (fn-owner-io :log-order).
(defthm fn-sjh-okp-at-owner-log-order
  (implies (and (fn-sjh-io-run-premisesp oc *fn-sjh-log-order-events* fn-arena)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat))
           (fn-sjh-okp (fn-ocfg-owner (fn-olr-ocfg-order oc)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories '(fn-olr-ocfg-order-is-the-file-route-by-definition
                                               fn-ocfg-run car-cons cdr-cons (:e fn-sjh-io-eventsp)
                                               (:e consp) (:e car) (:e cdr))
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-of-ocfg-io-run (events *fn-sjh-log-order-events*))))))

; -----------------------------------------------------------------------------
; The live configuration's completion (host/owner-host.lisp
; fn-owner-reconfigure-complete: fn-oclc-publish).  The carried configure
; (fn-oclc-configure) installs a node over the same acceptance articles, and
; keeps the store's files and verdicts: the catalog's frame
; (fn-scjs-store-framep) holds by definition, where sca-join-4 had to name
; it for the replaying fn-cpo-configure-durable the host no longer calls.

(defthm fn-sjh-rc-oclc-advance-articles
  (equal (fn-state-articles (fn-node-acceptance (fn-oclc-advance node txid)))
         (fn-state-articles (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-oclc-advance))))

(defthm fn-sjh-rc-oclc-apply-articles
  (equal (fn-state-articles (fn-node-acceptance (fn-cnode-node (fn-oclc-apply cn record))))
         (fn-state-articles (fn-node-acceptance (fn-cnode-node cn))))
  :hints (("Goal" :in-theory (e/d (fn-oclc-apply) (fn-cnode-carried-acceptablep fn-cfg-apply-record
                                                   fn-cnode-domain-of fn-cnode-extend-nexts)))))

(defthm fn-sjh-rc-configure-store-fields
  (let ((st (mv-nth 0 (fn-oclc-configure s config record))))
    (and (equal (fn-sn-files st) (fn-sn-files s))
         (equal (fn-sn-verdicts st) (fn-sn-verdicts s))
         (equal (fn-state-articles (fn-node-acceptance (fn-sn-node st)))
                (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
  :hints (("Goal" :in-theory (e/d (fn-oclc-configure fn-cpo-install fn-sn-with-configuration
                                   fn-sn-files fn-sn-verdicts fn-sn-node)
                                  (fn-oclc-advance fn-oclc-apply fn-cnode-carried-acceptablep
                                   fn-oclc-advance-okp fn-oclc-install-okp fn-cfg-recordp)))))

(defthm fn-sjh-rc-owner-with-store-fields
  (let ((o2 (fn-ocl-owner-with-store o st)))
    (and (equal (fn-own-store o2) st)
         (equal (fn-own-conns o2) (fn-own-conns o))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-owner-with-store fn-own-refresh)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-own-view-make-visible fn-ctl-refresh-withdrawn fn-midx-refresh
                                   fn-gidx-refresh fn-ctl-visible-state-of)))))


(defthm fn-sjh-rc-historyp-of-owner-with-store
  (implies (and (fn-scjs-historyp o)
                (equal (fn-sn-files st) (fn-sn-files (fn-own-store o))))
           (fn-scjs-historyp (fn-ocl-owner-with-store o st)))
  :hints (("Goal" :in-theory (e/d (fn-ocl-owner-with-store fn-scjs-historyp fn-sjh-refresh-version)
                                  (fn-own-refresh fn-own-store-idlep)))))

(defthm fn-sjh-rc-okp-of-owner-with-store
  (implies (and (fn-sjh-okp o pending fn-arena fn-cat)
                (equal (fn-sn-files st) (fn-sn-files (fn-own-store o)))
                (fn-scjs-store-framep (fn-own-store o) st (fn-own-view-version (fn-own-view o)))
                (fn-statep (fn-own-view-archive (fn-own-view (fn-ocl-owner-with-store o st)))))
           (fn-sjh-okp (fn-ocl-owner-with-store o st) pending fn-arena fn-cat))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-okp-when-parts fn-sjh-versionsp-is-versions-okp
                                        fn-sjh-rc-owner-with-store-fields fn-sjh-linkp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-scjs-owner-with-store-keeps-invp)
                 (:instance fn-scjs-owner-with-store-keeps-versions)
                 (:instance fn-oix-ocl-owner-with-store-keeps-view-indexed)
                 (:instance fn-sjh-rc-historyp-of-owner-with-store)))))

(defthm fn-sjh-rc-configure-framep
  (implies (fn-scjs-store-seenp s v)
           (fn-scjs-store-framep s (mv-nth 0 (fn-oclc-configure s config record)) v))
  :hints (("Goal" :in-theory (union-theories '(fn-scjs-store-framep fn-scjs-store-seenp fn-scjs-seen-records
                                               fn-sjh-rc-configure-store-fields)
                                             (theory 'minimal-theory)))))

(defthm fn-sjh-rc-oclc-complete-okp
  (let ((next (fn-oclc-complete oc)))
    (implies (and (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                  (fn-statep (fn-own-view-archive (fn-own-view (fn-ocfg-owner next)))))
             (fn-sjh-okp (fn-ocfg-owner next) pending fn-arena fn-cat)))
  :hints (("Goal" :in-theory (union-theories '(fn-oclc-complete fn-ocfg-owner-of-fn-ocfg-make)
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scjs-seenp (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-rc-configure-store-fields
                            (s (fn-own-store (fn-ocfg-owner oc))) (config (fn-ocfg-config oc))
                            (record (fn-ocfg-staged oc)))
                 (:instance fn-sjh-rc-configure-framep
                            (s (fn-own-store (fn-ocfg-owner oc))) (config (fn-ocfg-config oc))
                            (record (fn-ocfg-staged oc))
                            (v (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-sjh-rc-okp-of-owner-with-store
                            (o (fn-ocfg-owner oc))
                            (st (mv-nth 0 (fn-oclc-configure (fn-own-store (fn-ocfg-owner oc))
                                                             (fn-ocfg-config oc) (fn-ocfg-staged oc)))))))))

(defthm fn-sjh-rc-configure-view
  (equal (fn-own-view (fn-own-configure o config)) (fn-own-view o))
  :hints (("Goal" :in-theory (enable fn-own-configure))))

; KEYSTONE (the live configuration's completion).  host/owner-host.lisp
; fn-owner-reconfigure-complete installs fn-oclc-publish's owner: refused or
; recovery-required, the owner it was given; durable, the owner over the
; carried configure's store (its history, verdicts and acceptance articles
; unchanged: fn-sjh-rc-configure-store-fields) with the published posting
; configuration.  fn-sjh-okp with the same pending row; the view's archive
; after is a state (the owner relation after, Q3c).
(defthm fn-sjh-okp-at-owner-reconfigure-complete
  (let ((oc2 (mv-nth 1 (fn-oclc-publish oc generation max-octets))))
    (implies (and (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                  (fn-statep (fn-own-view-archive (fn-own-view (fn-ocfg-owner oc2)))))
             (fn-sjh-okp (fn-ocfg-owner oc2) pending fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-oclc-publish fn-sjh-ocfg-owner-of-with-owner fn-sjh-rc-configure-view
                                   fn-sjh-arm-okp-of-own-configure)
                                  (fn-oclc-complete fn-sjh-okp fn-own-configure fn-oag-post-config
                                   fn-cfg-record-generation fn-ocfg-with-owner))
           :use ((:instance fn-sjh-rc-oclc-complete-okp)))))

; -----------------------------------------------------------------------------
; The opens (host/owner-host.lisp fn-owner-open, fn-owner-exposure-open).
; The carried open (fn-ocar-ocfg-open) adds one connection pinned at the
; owner's view and sets its reader context; the store and the view stay.  At
; a captured reader view the new connection is pinned there, and the host
; puts the working view back.


(defthm fn-sjh-op-ocar-own-open-facts
  (let ((o2 (cdr (fn-ocar-own-open o acfg))))
    (and (equal (fn-own-store o2) (fn-own-store o))
         (equal (fn-own-view o2) (fn-own-view o))
         (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                       (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat))
                  (fn-scj-conns-pinp (fn-own-conns o2) fn-arena fn-cat))
         (implies (and (fn-scj-conns-versions-atmostp (fn-own-conns o) n)
                       (<= (nfix (fn-own-view-version (fn-own-view o))) (nfix n)))
                  (fn-scj-conns-versions-atmostp (fn-own-conns o2) n))))
  :hints (("Goal" :in-theory (e/d (fn-ocar-own-open) (fn-ocar-served-open-group-indexed fn-own-conn-make-group-indexed
                                                      fn-scj-live-okp fn-scj-conn-pinp
                                                      fn-own-view-group-index fn-own-view-index fn-own-view-archive
                                                      fn-own-view-version)))))


(defthm fn-sjh-op-conn-make-version
  (equal (fn-own-conn-version (fn-own-conn-make-group-indexed id v fr wire sess arch cfg obs vd idx gidx ctl)) v)
  :hints (("Goal" :in-theory (enable fn-own-conn-make-group-indexed fn-own-conn-version fn-ag-car fn-ag-cdr))))

(defthm fn-sjh-op-conn-make-pinp
  (equal (fn-scj-conn-pinp (fn-own-conn-make-group-indexed (fn-own-conn-id c) (fn-own-conn-version c)
                                                           fr wire sess (fn-own-conn-archive c) cfg obs vd
                                                           (fn-own-conn-index c) (fn-own-conn-group-index c)
                                                           (fn-own-conn-control c))
                           fn-arena fn-cat)
         (fn-scj-conn-pinp c fn-arena fn-cat))
  :hints (("Goal" :in-theory (enable fn-scj-conn-pinp fn-scj-conn-pinned-index fn-own-conn-make-group-indexed
                                     fn-own-conn-version fn-own-conn-archive fn-own-conn-index
                                     fn-own-conn-group-index fn-own-conn-control fn-ag-car fn-ag-cdr))))

(defthm fn-sjh-op-ocar-reader-context-facts
  (let ((o2 (fn-ocar-own-reader-context o id cfg)))
    (and (equal (fn-own-store o2) (fn-own-store o))
         (equal (fn-own-view o2) (fn-own-view o))
         (implies (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                  (fn-scj-conns-pinp (fn-own-conns o2) fn-arena fn-cat))
         (implies (fn-scj-conns-versions-atmostp (fn-own-conns o) n)
                  (fn-scj-conns-versions-atmostp (fn-own-conns o2) n))))
  :hints (("Goal" :in-theory (e/d (fn-ocar-own-reader-context fn-own-set-conns)
                                  (fn-own-conn-make-group-indexed fn-scj-conn-pinp
                                   fn-scj-conns-pinp fn-own-find-conn fn-own-replace-conn
                                   fn-auth-with-base fn-ocar-peer-open-reader fn-cfgp
                                   fn-own-conn-archive fn-own-conn-index
                                   fn-own-conn-group-index fn-own-conn-control fn-scj-conns-versions-atmostp))
           :use ((:instance fn-scj-conns-pinp-find (conns (fn-own-conns o)))
                 (:instance fn-scj-versions-atmost-of-replace-conn
                            (conn (fn-own-conn-make-group-indexed
                                   (fn-own-conn-id (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-version (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-frontier (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-wire (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-auth-with-base
                                    (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o)))
                                    (fn-ocar-peer-open-reader
                                     (fn-own-conn-archive (fn-own-find-conn id (fn-own-conns o)))
                                     (fn-sn-node (fn-own-store o)) cfg))
                                   (fn-own-conn-archive (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-config (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-observation (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-verdicts (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-index (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-group-index (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-control (fn-own-find-conn id (fn-own-conns o)))))
                            (conns (fn-own-conns o)))
                 (:instance fn-scj-versions-atmost-find-conn (conns (fn-own-conns o)))))))

(defthm fn-sjh-op-ocar-ocfg-open-owner
  (equal (fn-ocfg-owner (cdr (fn-ocar-ocfg-open oc acfg)))
         (let* ((o (fn-ocfg-owner oc))
                (raw (cdr (fn-ocar-own-open o (fn-auth-config-with-accounts
                                               acfg (fn-cfg-value (fn-ocfg-config oc)))))))
           (if (fn-own-find-conn (fn-own-next-id o) (fn-own-conns raw))
               (fn-ocar-own-reader-context raw (fn-own-next-id o) (fn-ocfg-config oc))
             raw)))
  :hints (("Goal" :in-theory '(fn-ocar-ocfg-open fn-ocfg-owner-of-fn-ocfg-make cdr-cons))))

(defthm fn-sjh-op-ocar-ocfg-open-facts2
  (let* ((o (fn-ocfg-owner oc))
         (o2 (fn-ocfg-owner (cdr (fn-ocar-ocfg-open oc acfg)))))
    (and (equal (fn-own-store o2) (fn-own-store o))
         (equal (fn-own-view o2) (fn-own-view o))
         (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                       (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat))
                  (fn-scj-conns-pinp (fn-own-conns o2) fn-arena fn-cat))
         (implies (and (fn-scj-conns-versions-atmostp (fn-own-conns o) n)
                       (<= (nfix (fn-own-view-version (fn-own-view o))) (nfix n)))
                  (fn-scj-conns-versions-atmostp (fn-own-conns o2) n))))
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-op-ocar-ocfg-open-owner) (theory 'minimal-theory))
           :use ((:instance fn-sjh-op-ocar-own-open-facts (o (fn-ocfg-owner oc))
                            (acfg (fn-auth-config-with-accounts acfg (fn-cfg-value (fn-ocfg-config oc)))))
                 (:instance fn-sjh-op-ocar-reader-context-facts
                            (o (cdr (fn-ocar-own-open (fn-ocfg-owner oc)
                                                      (fn-auth-config-with-accounts
                                                       acfg (fn-cfg-value (fn-ocfg-config oc))))))
                            (id (fn-own-next-id (fn-ocfg-owner oc)))
                            (cfg (fn-ocfg-config oc)))))))

(defthm fn-sjh-op-okp-of-open-at-view
  (let* ((o (fn-ocfg-owner oc))
         (o1 (fn-ocfg-owner oc1))
         (o2 (fn-ocfg-owner (fn-ocfg-with-view (cdr (fn-ocar-ocfg-open oc1 acfg)) (fn-own-view o)))))
    (implies (and (fn-sjh-okp o pending fn-arena fn-cat)
                  (equal (fn-own-store o1) (fn-own-store o))
                  (equal (fn-own-conns o1) (fn-own-conns o))
                  (fn-scj-live-okp (fn-own-view o1) fn-arena fn-cat)
                  (<= (nfix (fn-own-view-version (fn-own-view o1)))
                      (nfix (fn-own-view-version (fn-own-view o)))))
             (fn-sjh-okp o2 pending fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-versions-okp fn-ocfg-with-view-keeps-the-rest)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-op-ocar-ocfg-open-facts2 (oc oc1)
                            (n (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-sjh-versions-atmost-monotone
                            (conns (fn-own-conns (fn-ocfg-owner oc)))
                            (n (fn-own-view-version (fn-own-view (fn-ocfg-owner oc))))
                            (m (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-scj-invp-by-parts (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-ocfg-with-view (cdr (fn-ocar-ocfg-open oc1 acfg))
                                                                  (fn-own-view (fn-ocfg-owner oc))))))
                 (:instance fn-sjh-okp-of-same-store-and-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-ocfg-with-view (cdr (fn-ocar-ocfg-open oc1 acfg))
                                                                  (fn-own-view (fn-ocfg-owner oc))))))))))

; KEYSTONE (fn-owner-open, a capture held).  host/owner-host.lisp
; fn-owner-open: fn-owner-at-reader-view installs fn-ocfg-at-reader-view,
; fn-owner-open-at opens through fn-ocar-ocfg-open there, and
; fn-owner-at-working-view puts the working view back (fn-ocfg-with-view).
; The new connection is pinned at the captured view, live over the catalog
; and no newer than the working view (fn-sjh-views-okp, named).
(defthm fn-sjh-okp-at-owner-open-captured
  (let ((o2 (fn-ocfg-owner
             (fn-ocfg-with-view (cdr (fn-ocar-ocfg-open (fn-ocfg-at-reader-view oc views) acfg))
                                (fn-own-view (fn-ocfg-owner oc))))))
    (implies (and (consp views)
                  (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                  (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat))
             (fn-sjh-okp o2 pending fn-arena fn-cat)))
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-views-okp fn-ocfg-at-reader-view fn-ocv-reader-view
                                               fn-ocfg-with-view-keeps-the-rest)
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-op-okp-of-open-at-view
                            (oc1 (fn-ocfg-with-view oc (car views))))))))

; KEYSTONE (fn-owner-open, no capture): fn-ocar-ocfg-open at the working view.
(defthm fn-sjh-okp-at-owner-open
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (cdr (fn-ocar-ocfg-open oc acfg))) pending fn-arena fn-cat))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-versions-okp) (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-invp-gives-live-okp (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-op-ocar-ocfg-open-facts2
                            (n (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))
                 (:instance fn-scj-invp-by-parts (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (cdr (fn-ocar-ocfg-open oc acfg)))))
                 (:instance fn-sjh-okp-of-same-store-and-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (cdr (fn-ocar-ocfg-open oc acfg)))))))))

; KEYSTONE (fn-owner-exposure-open): the owner of fn-ocar-exp-open's result
; -- a refused accept keeps the owner, an admitted one opens a reader
; (fn-ocar-ocfg-open) or a peer (fn-ocfg-open-peer).
(defthm fn-sjh-okp-at-owner-exposure-open
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (fn-exp-open-ocfg (fn-ocar-exp-open oc xs lim acfg peer address now)))
                       pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocar-exp-open fn-exp-open-ocfg fn-exp-at)
                                  (fn-ocar-ocfg-open fn-ocfg-open-peer fn-sjh-okp fn-exp-admit-decision
                                   fn-exp-register fn-exp-pinned-acfg fn-exp-with fn-exp-counters-bump
                                   fn-exp-line))
           :use ((:instance fn-sjh-okp-at-owner-open (acfg (fn-exp-pinned-acfg acfg lim)))
                 (:instance fn-sjh-okp-at-owner-open-peer (acfg (fn-exp-pinned-acfg acfg lim)))))))


; -----------------------------------------------------------------------------
; The served connection's wire events outside a read (fn-ocfg-read-step):
; the served dispatch keeps the connection's catalog facts
; (fn-scr-conn-okp-of-scar-dispatch) and its pin no newer than the view
; (fn-scj-sconn-atmostp-of-scar-dispatch).


(defthm fn-sjh-rs-served-conn-okp-session-free
  (equal (fn-scr-conn-okp (fn-own-served-conn o conn s1) fn-arena fn-cat)
         (fn-scr-conn-okp (fn-own-served-conn o conn s2) fn-arena fn-cat))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-served-conn fn-scr-conn-okp fn-scr-conn-catalogp-unfolds
                                   fn-served-make-conn-live fn-served-conn-archive fn-served-conn-pinned-index
                                   fn-served-conn-pinned fn-served-conn-live fn-served-conn-index
                                   fn-served-conn-group-index fn-served-conn-control)
                                  (fn-scr-catalogp fn-scr-live-catalogp fn-scr-conn-catalogp)))))

(defthm fn-sjh-rs-sconn-atmostp-of-own-served-conn
  (implies (and (<= (nfix (fn-own-conn-version conn)) (nfix n))
                (<= (nfix (fn-own-view-version (fn-own-view o))) (nfix n)))
           (fn-scj-sconn-atmostp (fn-own-served-conn o conn s) n))
  :hints (("Goal" :in-theory (e/d (fn-scj-sconn-atmostp fn-own-served-conn)
                                  (fn-served-make-conn-live)))))

(defthm fn-sjh-rs-dispatch-result-facts
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (result (fn-served-dispatch (fn-own-served-conn o conn (fn-own-conn-session conn)) event fn-arena))
         (n (fn-own-view-version (fn-own-view o))))
    (implies (and conn
                  (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                  (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat)
                  (fn-node-statep (fn-sn-node (fn-own-store o)))
                  (fn-scar-view-indexedp o)
                  (fn-scj-conns-versions-atmostp (fn-own-conns o) n))
             (and (fn-scr-conn-okp (fn-served-result-conn result) fn-arena fn-cat)
                  (fn-scj-sconn-atmostp (fn-served-result-conn result) n))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-scar-view-indexedp fn-own-tls-served-conn)
                                             (theory 'minimal-theory))
           :use ((:instance fn-scj-served-conn-okp-of-pins)
                 (:instance fn-sjh-rs-served-conn-okp-session-free
                            (conn (fn-own-find-conn id (fn-own-conns o)))
                            (s1 (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))))
                            (s2 (fn-own-conn-live-session o (fn-own-find-conn id (fn-own-conns o)))))
                 (:instance fn-scar-dispatch-is-served-dispatch
                            (conn (fn-own-served-conn o (fn-own-find-conn id (fn-own-conns o))
                                                      (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o)))))
                            (live (fn-sn-node (fn-own-store o)))
                            (trie (fn-own-view-index (fn-own-view o)))
                            (arts (fn-state-articles (fn-own-view-archive (fn-own-view o)))))
                 (:instance fn-scr-conn-okp-of-scar-dispatch
                            (conn (fn-own-served-conn o (fn-own-find-conn id (fn-own-conns o))
                                                      (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o)))))
                            (live (fn-sn-node (fn-own-store o)))
                            (trie (fn-own-view-index (fn-own-view o)))
                            (arts (fn-state-articles (fn-own-view-archive (fn-own-view o)))))
                 (:instance fn-scj-sconn-atmostp-of-scar-dispatch
                            (conn (fn-own-served-conn o (fn-own-find-conn id (fn-own-conns o))
                                                      (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o)))))
                            (live (fn-sn-node (fn-own-store o)))
                            (trie (fn-own-view-index (fn-own-view o)))
                            (arts (fn-state-articles (fn-own-view-archive (fn-own-view o))))
                            (n (fn-own-view-version (fn-own-view o))))
                 (:instance fn-sjh-rs-sconn-atmostp-of-own-served-conn
                            (conn (fn-own-find-conn id (fn-own-conns o)))
                            (s (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o))))
                            (n (fn-own-view-version (fn-own-view o))))
                 (:instance fn-scj-versions-atmost-find-conn (conns (fn-own-conns o))
                            (n (fn-own-view-version (fn-own-view o))))))))

(defthm fn-sjh-rs-read-step-owner-facts
  (let* ((o2 (car (cdr (fn-own-read-step-full o id event fn-arena))))
         (n (fn-own-view-version (fn-own-view o))))
    (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                  (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat)
                  (fn-node-statep (fn-sn-node (fn-own-store o)))
                  (fn-scar-view-indexedp o)
                  (fn-scj-conns-versions-atmostp (fn-own-conns o) n))
             (and (equal (fn-own-store o2) (fn-own-store o))
                  (equal (fn-own-view o2) (fn-own-view o))
                  (fn-scj-conns-pinp (fn-own-conns o2) fn-arena fn-cat)
                  (fn-scj-conns-versions-atmostp (fn-own-conns o2) n))))
  :hints (("Goal" :cases ((fn-own-find-conn id (fn-own-conns o)))
           :in-theory (e/d (fn-own-read-step-full fn-own-set-conns fn-scr-conn-okp fn-scj-sconn-atmostp)
                           (fn-served-dispatch fn-own-served-conn fn-own-conn-make-group-indexed
                            fn-own-conn-boundedp fn-own-replace-conn fn-own-remove-conn fn-own-find-conn
                            fn-scj-conns-pinp fn-scj-conn-pinp fn-scj-live-okp fn-scr-conn-catalogp
                            fn-scr-live-catalogp fn-scj-conns-versions-atmostp fn-own-result-repinned
                            fn-scar-view-indexedp fn-node-statep)))
          ("Subgoal 1" :use ((:instance fn-sjh-rs-dispatch-result-facts)
                             (:instance fn-scj-versions-atmost-of-replace-conn
                                        (conns (fn-own-conns o)) (n (fn-own-view-version (fn-own-view o)))
                                        (conn (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
                                          (sconn (fn-served-result-conn
                                                  (fn-served-dispatch (fn-own-served-conn o conn (fn-own-conn-session conn))
                                                                      event fn-arena)))
                                          (pinned (fn-served-conn-pinned sconn)))
                                     (fn-own-conn-make-group-indexed (fn-own-conn-id conn)
                                                                     (fn-served-pinned-version pinned)
                                                                     (fn-served-pinned-frontier pinned)
                                                                     (fn-served-conn-wire sconn)
                                                                     (fn-served-conn-session sconn)
                                                                     (fn-served-conn-archive sconn)
                                                                     (fn-own-conn-config conn)
                                                                     (fn-own-conn-observation conn)
                                                                     (fn-served-conn-verdicts sconn)
                                                                     (fn-served-conn-index sconn)
                                                                     (fn-served-conn-group-index sconn)
                                                                     (fn-served-conn-control sconn)))))
                             (:instance fn-scj-versions-atmost-of-remove-conn
                                        (conns (fn-own-conns o)) (n (fn-own-view-version (fn-own-view o))))))))

(defthm fn-sjh-rs-ocfg-read-step-owner
  (equal (fn-ocfg-owner (cdr (fn-ocfg-read-step oc id event fn-arena)))
         (car (cdr (fn-own-read-step-full (fn-ocfg-owner oc) id event fn-arena))))
  :hints (("Goal" :in-theory '(fn-ocfg-read-step fn-ocfg-with-read-owner fn-ocfg-owner-of-fn-ocfg-make cdr-cons))))

; KEYSTONE (the served connection's wire events outside a read:
; host/owner-host.lisp fn-owner-tls-established (:tls-established) and
; host/native-admin-host.lisp fn-owner-account-outcome (:account-outcome),
; both fn-ocfg-read-step).  The node's state is the owner relation's.
(defthm fn-sjh-okp-at-owner-read-step
  (implies (and (fn-ocl-relation oc)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat))
           (fn-sjh-okp (fn-ocfg-owner (cdr (fn-ocfg-read-step oc id event fn-arena))) pending fn-arena fn-cat))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-versions-okp fn-sjh-rs-ocfg-read-step-owner) (theory 'minimal-theory))
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-invp-gives-live-okp (o (fn-ocfg-owner oc)))
                 (:instance fn-scar-ocl-relation-carries-node-statep)
                 (:instance fn-sjh-rs-read-step-owner-facts (o (fn-ocfg-owner oc)))
                 (:instance fn-scj-invp-by-parts (o (fn-ocfg-owner oc))
                            (o2 (car (cdr (fn-own-read-step-full (fn-ocfg-owner oc) id event fn-arena)))))
                 (:instance fn-sjh-okp-of-same-store-and-view (o (fn-ocfg-owner oc))
                            (o2 (car (cdr (fn-own-read-step-full (fn-ocfg-owner oc) id event fn-arena)))))))))
