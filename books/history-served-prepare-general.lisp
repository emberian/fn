; Identity and article prepares: a staged candidate is busy; refusal retains history.
(in-package "ACL2")
(include-book "history-served-prepare")
(include-book "identity-retain-carried")
(include-book "post-prepare-catalog")

(defthm fn-hsp-refresh-busy
 (implies (not (fn-own-store-idlep (fn-own-store o)))
  (and (equal (fn-own-refresh-ix o hist) o)
       (equal (fn-own-refresh o) o)))
 :hints (("Goal" :in-theory '(fn-own-refresh-ix fn-own-refresh))))

(defthm fn-hsp-identity-prepare-unchanged-or-busy
 (or (equal (fn-irc-sn-prepare-identity s event carry) s)
     (not (fn-own-store-idlep (fn-irc-sn-prepare-identity s event carry))))
 :rule-classes nil
 :hints (("Goal" :in-theory '(fn-irc-sn-prepare-identity fn-own-store-idlep
 fn-sn-files-of-fn-sn-update fn-snt-idle-phasep (:executable-counterpart member-equal) (:executable-counterpart equal)))))

(defthm fn-hsp-article-prepare-unchanged-or-busy
 (or (equal (fn-ppc-spc-prepare s record dup carry) s)
     (not (fn-own-store-idlep (fn-ppc-spc-prepare s record dup carry))))
 :rule-classes nil
 :hints (("Goal" :in-theory '(fn-ppc-spc-prepare fn-own-store-idlep
 fn-sn-files-of-fn-sn-update fn-snt-idle-phasep (:executable-counterpart member-equal) (:executable-counterpart equal)))))

(defun fn-hsp-irc-ocfg-prepare-identity (oc event carry fn-hist)
  (declare (xargs :guard (and (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry)) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
                  :verify-guards t
                  :stobjs fn-hist
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store fn-sn-statep)))))
  (mbe :logic (let ((o (fn-ocfg-owner oc)))
    (fn-ocfg-with-owner oc
                        (fn-own-refresh-ix (fn-own-make (fn-irc-sn-prepare-identity (fn-own-store o)
                                                                                    event
                                                                                    carry)
                                                        (fn-own-view o)
                                                        (fn-own-conns o)
                                                        (fn-own-next-id o)
                                                        (fn-own-max-conns o)
                                                        (fn-own-pending o)
                                                        (fn-own-ledger-field o)
                                                        (fn-own-clock o)
                                                        (fn-own-facts o)
                                                        (fn-own-config o)
                                                        (fn-own-queue o)
                                                        (fn-own-inflight o)
                                                        (fn-own-feeds o)
                                                        (fn-own-node-secret o)
                                                        (fn-own-refused o))
                                           fn-hist)))
       :exec (let ((o (fn-ocfg-owner oc)))
    (fn-ocfg-with-owner oc
                        (fn-own-refresh-ix (fn-own-make (fn-hpf-irc-sn-prepare-identity (fn-own-store o)
                                                                                    event
                                                                                    carry)
                                                        (fn-own-view o)
                                                        (fn-own-conns o)
                                                        (fn-own-next-id o)
                                                        (fn-own-max-conns o)
                                                        (fn-own-pending o)
                                                        (fn-own-ledger-field o)
                                                        (fn-own-clock o)
                                                        (fn-own-facts o)
                                                        (fn-own-config o)
                                                        (fn-own-queue o)
                                                        (fn-own-inflight o)
                                                        (fn-own-feeds o)
                                                        (fn-own-node-secret o)
                                                        (fn-own-refused o))
                                           fn-hist)))))

(defthm fn-hsp-irc-ocfg-prepare-identity-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-irc-ocfg-prepare-identity oc event carry fn-hist) (fn-irc-ocfg-prepare-identity oc event carry)))
 :hints (("Goal" :in-theory '(fn-irc-ocfg-prepare-identity fn-hsp-irc-ocfg-prepare-identity fn-sbud-oc-store fn-hsp-refresh-busy fn-own-refresh-ix-is-own-refresh fn-own-store-of-fn-own-make) :cases ((equal (fn-irc-sn-prepare-identity (fn-own-store (fn-ocfg-owner oc)) event carry) (fn-own-store (fn-ocfg-owner oc)))) :use ((:instance fn-hsp-identity-prepare-unchanged-or-busy (s (fn-own-store (fn-ocfg-owner oc))))))))
(in-theory (disable fn-hsp-irc-ocfg-prepare-identity))

(defun fn-hsp-irc-psrv-prepare-identity (oc event carry fn-hist)
  (declare (xargs :guard (and (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry)) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
                  :stobjs fn-hist
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store fn-sn-statep)))))
  (if (and (fn-psrv-event-servedp (fn-ocfg-config oc) event) (fn-psrv-event-numberedp oc event))
      (fn-hsp-irc-ocfg-prepare-identity oc event carry fn-hist)
    oc))

(defthm fn-hsp-irc-psrv-prepare-identity-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-irc-psrv-prepare-identity oc event carry fn-hist) (fn-irc-psrv-prepare-identity oc event carry)))
 :hints (("Goal" :in-theory '(fn-irc-psrv-prepare-identity fn-hsp-irc-psrv-prepare-identity fn-sbud-oc-store fn-hsp-irc-ocfg-prepare-identity-is-reference) )))
(in-theory (disable fn-hsp-irc-psrv-prepare-identity))

(defun fn-hsp-irc-oiis-prepare-identity (oc w h carry fn-hist)
  (declare (xargs :guard (and (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (natp h)
                              (fn-prc-carryp carry)) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
                  :verify-guards t
                  :stobjs fn-hist
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store fn-sn-statep)))))
  (let ((s (fn-own-store (fn-ocfg-owner oc))))
    (fn-hsp-irc-psrv-prepare-identity oc
                                      (fn-oii-identity-row w
                                                           (fn-sn-keyring s)
                                                           (fn-sn-keyring-generation s)
                                                           h)
                                      carry
                                      fn-hist)))

(defthm fn-hsp-irc-oiis-prepare-identity-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-irc-oiis-prepare-identity oc w h carry fn-hist) (fn-irc-oiis-prepare-identity oc w h carry)))
 :hints (("Goal" :in-theory '(fn-irc-oiis-prepare-identity fn-hsp-irc-oiis-prepare-identity fn-sbud-oc-store fn-hsp-irc-ocfg-prepare-identity-is-reference fn-hsp-irc-psrv-prepare-identity-is-reference) )))
(in-theory (disable fn-hsp-irc-oiis-prepare-identity))

(defun fn-hsp-irc-pout-prepare-identity (oc w h carry fn-hist)
  (declare (xargs :guard (and (and (fn-sn-statep (fn-sbud-oc-store oc)) (natp h) (fn-prc-carryp carry)) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
                  :verify-guards t
                  :stobjs fn-hist
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store fn-sn-statep)))))
  (let ((next (fn-hsp-irc-oiis-prepare-identity oc w h carry fn-hist)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          (fn-pout-identity-refusal-kind oc w h))
        next)))

(defthm fn-hsp-irc-pout-prepare-identity-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-irc-pout-prepare-identity oc w h carry fn-hist) (fn-irc-pout-prepare-identity oc w h carry)))
 :hints (("Goal" :in-theory '(fn-irc-pout-prepare-identity fn-hsp-irc-pout-prepare-identity fn-sbud-oc-store fn-hsp-irc-ocfg-prepare-identity-is-reference fn-hsp-irc-psrv-prepare-identity-is-reference fn-hsp-irc-oiis-prepare-identity-is-reference) )))
(in-theory (disable fn-hsp-irc-pout-prepare-identity))

(defun fn-hsp-ppc-opc-owner-prepare (o record dup carry fn-hist)
  (declare (xargs :guard (and (and (fn-sn-statep (fn-own-store o))
                              (fn-prc-carryp carry)
                              (fn-ppc-dup-okp (fn-own-store o) record dup)) (fn-cst-relation (fn-own-store o)))
                  :stobjs fn-hist
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store fn-sn-statep)))))
  (mbe :logic (fn-own-refresh-ix (fn-own-make (fn-ppc-spc-prepare (fn-own-store o) record dup carry)
                                  (fn-own-view o)
                                  (fn-own-conns o)
                                  (fn-own-next-id o)
                                  (fn-own-max-conns o)
                                  (fn-own-pending o)
                                  (fn-own-ledger-field o)
                                  (fn-own-clock o)
                                  (fn-own-facts o)
                                  (fn-own-config o)
                                  (fn-own-queue o)
                                  (fn-own-inflight o)
                                  (fn-own-feeds o)
                                  (fn-own-node-secret o)
                                  (fn-own-refused o))
                     fn-hist)
       :exec (fn-own-refresh-ix (fn-own-make (fn-hpf-ppc-spc-prepare (fn-own-store o) record dup carry)
                                  (fn-own-view o)
                                  (fn-own-conns o)
                                  (fn-own-next-id o)
                                  (fn-own-max-conns o)
                                  (fn-own-pending o)
                                  (fn-own-ledger-field o)
                                  (fn-own-clock o)
                                  (fn-own-facts o)
                                  (fn-own-config o)
                                  (fn-own-queue o)
                                  (fn-own-inflight o)
                                  (fn-own-feeds o)
                                  (fn-own-node-secret o)
                                  (fn-own-refused o))
                     fn-hist)))

(defthm fn-hsp-ppc-opc-owner-prepare-is-reference
 (implies (and (fn-sn-statep (fn-own-store o)) (fn-hist-of-storep fn-hist (fn-own-store o)))
  (equal (fn-hsp-ppc-opc-owner-prepare o record dup carry fn-hist) (fn-ppc-opc-owner-prepare o record dup carry)))
 :hints (("Goal" :in-theory '(fn-ppc-opc-owner-prepare fn-hsp-ppc-opc-owner-prepare fn-sbud-oc-store fn-hsp-irc-ocfg-prepare-identity-is-reference fn-hsp-irc-psrv-prepare-identity-is-reference fn-hsp-irc-oiis-prepare-identity-is-reference fn-hsp-irc-pout-prepare-identity-is-reference fn-hsp-refresh-busy fn-own-refresh-ix-is-own-refresh fn-own-store-of-fn-own-make) :cases ((equal (fn-ppc-spc-prepare (fn-own-store o) record dup carry) (fn-own-store o))) :use ((:instance fn-hsp-article-prepare-unchanged-or-busy (s (fn-own-store o)))))))
(in-theory (disable fn-hsp-ppc-opc-owner-prepare))

(defun fn-hsp-ppc-sbud-prepare (oc record budget dup carry fn-hist)
  (declare (xargs :guard (and (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-prc-carryp carry)
                              (fn-ppc-dup-okp (fn-sbud-oc-store oc) record dup)) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))
                  :stobjs fn-hist))
  (if (fn-sbud-admitp budget (fn-sbud-count (fn-sbud-oc-store oc)))
      (fn-ocfg-with-owner oc
                          (fn-hsp-ppc-opc-owner-prepare (fn-ocfg-owner oc) record dup carry fn-hist))
    oc))

(defthm fn-hsp-ppc-sbud-prepare-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-ppc-sbud-prepare oc record budget dup carry fn-hist) (fn-ppc-sbud-prepare oc record budget dup carry)))
 :hints (("Goal" :in-theory '(fn-ppc-sbud-prepare fn-hsp-ppc-sbud-prepare fn-sbud-oc-store fn-hsp-irc-ocfg-prepare-identity-is-reference fn-hsp-irc-psrv-prepare-identity-is-reference fn-hsp-irc-oiis-prepare-identity-is-reference fn-hsp-irc-pout-prepare-identity-is-reference fn-hsp-ppc-opc-owner-prepare-is-reference) )))
(in-theory (disable fn-hsp-ppc-sbud-prepare))

(defun fn-hsp-ppc-psrv-prepare (oc record budget dup carry fn-hist)
  (declare (xargs :guard (and (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-prc-carryp carry)
                              (fn-ppc-dup-okp (fn-sbud-oc-store oc) record dup)) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
                  :stobjs fn-hist
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store fn-sn-statep)))))
  (if (and (fn-psrv-event-servedp (fn-ocfg-config oc) record) (fn-psrv-event-numberedp oc record))
      (fn-hsp-ppc-sbud-prepare oc record budget dup carry fn-hist)
    oc))

(defthm fn-hsp-ppc-psrv-prepare-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-ppc-psrv-prepare oc record budget dup carry fn-hist) (fn-ppc-psrv-prepare oc record budget dup carry)))
 :hints (("Goal" :in-theory '(fn-ppc-psrv-prepare fn-hsp-ppc-psrv-prepare fn-sbud-oc-store fn-hsp-irc-ocfg-prepare-identity-is-reference fn-hsp-irc-psrv-prepare-identity-is-reference fn-hsp-irc-oiis-prepare-identity-is-reference fn-hsp-irc-pout-prepare-identity-is-reference fn-hsp-ppc-opc-owner-prepare-is-reference fn-hsp-ppc-sbud-prepare-is-reference) )))
(in-theory (disable fn-hsp-ppc-psrv-prepare))

(defun fn-hsp-ppc-pout-prepare-article-cat (oc record budget carry fn-arena fn-cat fn-hist)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist)
                  :guard (and (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-prc-carryp carry)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                              (fn-ppc-dup-okp (fn-sbud-oc-store oc)
                                              record
                                              (fn-pidx-find-article-cat (fn-record-msgid record)
                                                                        (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
                                                                        (fn-own-view (fn-ocfg-owner oc))
                                                                        fn-arena
                                                                        fn-cat))) (fn-cst-relation (fn-own-store (fn-ocfg-owner oc))))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))))
  (let* ((o (fn-ocfg-owner oc))
         (dup (fn-pidx-find-article-cat (fn-record-msgid record)
                                        (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store o))))
                                        (fn-own-view o)
                                        fn-arena
                                        fn-cat))
         (next (fn-hsp-ppc-psrv-prepare oc record budget dup carry fn-hist)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          (fn-psrv-refusal-kind oc record budget))
        next)))

(defthm fn-hsp-ppc-pout-prepare-article-cat-is-reference
 (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc))))
  (equal (fn-hsp-ppc-pout-prepare-article-cat oc record budget carry fn-arena fn-cat fn-hist) (fn-ppc-pout-prepare-article-cat oc record budget carry fn-arena fn-cat)))
 :hints (("Goal" :in-theory '(fn-ppc-pout-prepare-article-cat fn-hsp-ppc-pout-prepare-article-cat fn-sbud-oc-store fn-hsp-irc-ocfg-prepare-identity-is-reference fn-hsp-irc-psrv-prepare-identity-is-reference fn-hsp-irc-oiis-prepare-identity-is-reference fn-hsp-irc-pout-prepare-identity-is-reference fn-hsp-ppc-opc-owner-prepare-is-reference fn-hsp-ppc-sbud-prepare-is-reference fn-hsp-ppc-psrv-prepare-is-reference) )))
(in-theory (disable fn-hsp-ppc-pout-prepare-article-cat))

(defthm fn-hsp-irc-ocfg-prepare-is-owner-with-store
 (equal (fn-hsp-irc-ocfg-prepare-identity oc e carry hist)
        (fn-ocfg-with-owner oc
         (fn-ocl-owner-with-store-ix (fn-ocfg-owner oc)
          (fn-irc-sn-prepare-identity (fn-own-store (fn-ocfg-owner oc)) e carry) hist)))
 :hints (("Goal" :in-theory '(fn-hsp-irc-ocfg-prepare-identity fn-ocl-owner-with-store-ix))))

(defthm fn-hsp-irc-psrv-prepare-preserves-invariant
 (implies (and (fn-lgoc-invariantp oc) (fn-prc-carryp carry))
  (fn-lgoc-invariantp (fn-hsp-irc-psrv-prepare-identity oc e carry hist)))
 :hints (("Goal"
 :use ((:instance fn-psrv-ccar-sn-prepare-identity-preserves
         (s (fn-own-store (fn-ocfg-owner oc))))
       (:instance fn-hsp-owner-with-store-preserves-invariant
         (st (fn-ccar-sn-prepare-identity (fn-own-store (fn-ocfg-owner oc)) e))
         (fn-hist hist))
       fn-lgoc-ocl-relation-cst fn-psrv-invariant-served-is-fold-served)
 :in-theory '(fn-hsp-irc-psrv-prepare-identity fn-hsp-irc-ocfg-prepare-is-owner-with-store
 fn-irc-sn-prepare-identity-is-ccar fn-psrv-deferred-prepare-keeps-histories
 fn-lgoc-invariantp))))

(defthm fn-hsp-irc-oiis-prepare-preserves-invariant
 (implies (and (fn-lgoc-invariantp oc) (fn-prc-carryp carry))
  (fn-lgoc-invariantp (fn-hsp-irc-oiis-prepare-identity oc w h carry hist)))
 :hints (("Goal" :in-theory '(fn-hsp-irc-oiis-prepare-identity
 fn-hsp-irc-psrv-prepare-preserves-invariant))))

(defthm fn-hsp-irc-pout-prepare-preserves-invariant
 (implies (and (fn-lgoc-invariantp oc) (fn-prc-carryp carry))
  (fn-lgoc-invariantp (mv-nth 1 (fn-hsp-irc-pout-prepare-identity oc w h carry hist))))
 :hints (("Goal" :in-theory '(fn-hsp-irc-pout-prepare-identity
 fn-hsp-irc-oiis-prepare-preserves-invariant mv-nth nth zp car-cons cdr-cons
 (:executable-counterpart zp)))))
