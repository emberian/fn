; post-prepare-catalog.lisp -- a POST's prepare with its duplicate test read
; from the catalog, not the owner's Message-ID trie (lane join-f2-midx, the
; fn-midx retirement).
;
; host/owner-host.lisp fn-owner-prepare-buffer installs
; fn-pout-prepare-article (books/owner-prepare-outcome.lisp), whose chain
; fn-psrv-prepare -> fn-prc-sbud-prepare -> fn-prc-opc-prepare ->
; fn-prc-opc-owner-prepare -> fn-prc-spc-prepare -> fn-prc-sn-prepare-node ->
; fn-prc-node-prepare -> fn-pidx-accept-prepare carries the owner's view to
; ONE use: the acceptance's duplicate test, fn-pidx-find-article of the
; record's Message-ID over the acceptance's articles through the view's trie.
;
; This book is that chain with the view replaced by the test's answer, DUP,
; decided once at the top from the catalog (fn-pidx-find-article-cat,
; books/post-identity-catalog.lisp) over the Store node's articles, which the
; chain's txid advance does not change (fn-ppc-advance-txid-articles).  Each
; layer fn-ppc-X is fn-prc-X's text with VIEW replaced by DUP; DUP is read
; only as a truth value (the defcongs), and each layer is equal to its
; fn-prc- twin when DUP is the twin's own test (fn-ppc-X-is-prc-X).
;
; KEYSTONE fn-ppc-pout-prepare-article-cat-is-pout-prepare-article: the
; function the host calls, fn-ppc-pout-prepare-article-cat, IS
; fn-pout-prepare-article (both values) under the visible-list relation and
; the trie's correspondence the reference's guard names (fn-pidx-view-okp)
; and the join (fn-scj-joinp); its host form
; fn-ppc-pout-prepare-article-cat-of-live-owner takes fn-ocl-relation,
; fn-scar-view-indexedp and fn-scj-invp, which fn-sjh-okp carries.  So every
; theorem about fn-pout-prepare-article (join-f2-2's
; fn-sjh-okp-at-owner-prepare-buffer among them) holds of the host's call.

(in-package "ACL2")

(include-book "post-identity-catalog")
(include-book "owner-prepare-outcome")
(include-book "owner-prepare-served")

; -----------------------------------------------------------------------------
; The layers.

(defun fn-ppc-accept-prepare (s generation msgid payload groups stamp dup)
  (declare (xargs :guard (fn-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-statep s)) :exec nil)
      s
    (if (or (equal (fn-state-fenced s) t)
            (consp (fn-state-pending s))
            (not (natp generation))
            (not (stringp msgid))
            (not (natp payload))
            (not (fn-record-stampp stamp))
            (not (fn-selection-validp groups (fn-state-groups s)))
            dup)
        s
      (fn-make-state
       (fn-state-groups s)
       (fn-state-nexts s)
       (fn-state-articles s)
       (1+ (fn-state-next-txid s))
       (fn-make-pending
        (fn-state-next-txid s)
        generation
        msgid
        payload
        groups
        (fn-allocate-memberships groups (fn-state-nexts s))
        t
        stamp)
       nil))))

(verify-guards fn-ppc-accept-prepare
  :hints (("Goal" :in-theory (enable fn-statep))))

(defcong iff equal (fn-ppc-accept-prepare s generation msgid payload groups stamp dup) 7
  :hints (("Goal" :in-theory (e/d (fn-ppc-accept-prepare)
                                  (fn-statep fn-make-state fn-make-pending
                                   fn-selection-validp)))))

(defthm fn-ppc-accept-prepare-is-pidx
  (equal (fn-ppc-accept-prepare s generation msgid payload groups stamp
                                (fn-pidx-find-article msgid (fn-state-articles s) view))
         (fn-pidx-accept-prepare s generation msgid payload groups stamp view))
  :hints (("Goal" :in-theory (e/d (fn-ppc-accept-prepare fn-pidx-accept-prepare)
                                  (fn-statep fn-make-state fn-make-pending
                                   fn-selection-validp fn-pidx-find-article)))))

; The reference: DUP the acceptance's own test.
(defthm fn-ppc-accept-prepare-is-accept-prepare
  (implies (iff dup (fn-acceptedp msgid (fn-state-articles s)))
           (equal (fn-ppc-accept-prepare s generation msgid payload groups stamp dup)
                  (fn-accept-prepare s generation msgid payload groups stamp)))
  :hints (("Goal" :in-theory (e/d (fn-ppc-accept-prepare fn-accept-prepare)
                                  (fn-statep fn-make-state fn-make-pending
                                   fn-selection-validp fn-acceptedp)))))

(in-theory (disable fn-ppc-accept-prepare))

(local (in-theory (enable (tau-system))))
(defun fn-ppc-node-prepare (s generation msgid payload groups
                              obligation-id subject evidence charge stamp
                              dup carry binding)
  (declare (xargs :guard (fn-node-statep s) :verify-guards nil))
  (if (or (not (fn-ab-p binding))
          (mbe :logic (not (fn-node-statep s)) :exec nil))
      s
    (let ((retention (fn-node-retention s)))
      (if (not (fn-prc-admissiblep retention obligation-id subject :archive
                                   evidence charge carry))
          s
        (let ((next-acceptance
               (fn-ppc-accept-prepare (fn-node-acceptance s)
                                      generation msgid payload groups stamp
                                      dup)))
          (if (equal next-acceptance (fn-node-acceptance s))
              s
            (fn-node-make-state
             next-acceptance
             retention
             (fn-node-make-stage
              msgid generation obligation-id subject evidence charge
              (fn-retain-make-state
               (fn-retain-capacity retention)
               (+ (fn-retain-reserved retention) charge)
               (cons (fn-retain-make-obligation obligation-id subject :archive
                                                evidence charge)
                     (fn-retain-pins retention))
               (fn-retain-releases retention)) binding)
             (fn-node-bindings s))))))))
(verify-guards fn-ppc-node-prepare
  :hints (("Goal" :in-theory (enable fn-node-statep))))
(local (in-theory (disable (tau-system))))

(defcong iff equal (fn-ppc-node-prepare s generation msgid payload groups
                                        obligation-id subject evidence charge stamp
                                        dup carry binding) 11
  :hints (("Goal" :in-theory (e/d (fn-ppc-node-prepare)
                                  (fn-node-statep fn-prc-admissiblep
                                   fn-retain-make-state fn-retain-make-obligation
                                   fn-node-make-state fn-node-make-stage)))))

(defthm fn-ppc-node-prepare-is-prc
  (equal (fn-ppc-node-prepare s generation msgid payload groups
                              obligation-id subject evidence charge stamp
                              (fn-pidx-find-article msgid
                                                    (fn-state-articles (fn-node-acceptance s))
                                                    view)
                              carry binding)
         (fn-prc-node-prepare s generation msgid payload groups
                              obligation-id subject evidence charge stamp view carry binding))
  :hints (("Goal" :in-theory (e/d (fn-ppc-node-prepare fn-prc-node-prepare
                                   fn-ppc-accept-prepare-is-pidx)
                                  (fn-node-statep fn-prc-admissiblep fn-pidx-find-article
                                   fn-pidx-accept-prepare
                                   fn-retain-make-state fn-retain-make-obligation
                                   fn-node-make-state fn-node-make-stage)))))

(defthm fn-ppc-node-prepare-is-node-prepare
  (implies (and (fn-prc-carryp carry)
                (iff dup (fn-acceptedp msgid (fn-state-articles (fn-node-acceptance s)))))
           (equal (fn-ppc-node-prepare s generation msgid payload groups
                                       obligation-id subject evidence charge stamp dup carry binding)
                  (fn-node-prepare s generation msgid payload groups
                                   obligation-id subject evidence charge stamp binding)))
  :hints (("Goal" :in-theory (e/d (fn-ppc-node-prepare fn-node-prepare fn-retain-admit
                                   fn-prc-admissiblep-is-admissiblep
                                   fn-ppc-accept-prepare-is-accept-prepare)
                                  (fn-node-statep fn-retain-admissiblep fn-prc-admissiblep
                                   fn-accept-prepare fn-retain-make-state fn-acceptedp
                                   fn-retain-make-obligation
                                   fn-node-make-state fn-node-make-stage)))))

(in-theory (disable fn-ppc-node-prepare))

(defun fn-ppc-sn-prepare-node (node record dup carry)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (fn-ppc-node-prepare (fn-replay-advance-txid node (fn-record-txid record))
                       (fn-record-generation record) (fn-record-msgid record)
                       (fn-record-payload record) (fn-record-groups record)
                       (fn-record-obligation-id record)
                       (fn-record-content-subject record)
                       (fn-record-release-evidence record)
                       (fn-record-charge record)
                       (fn-record-stamp record)
                       dup carry (fn-held-binding record)))

(verify-guards fn-ppc-sn-prepare-node)

(defcong iff equal (fn-ppc-sn-prepare-node node record dup carry) 3
  :hints (("Goal" :in-theory (e/d (fn-ppc-sn-prepare-node) (fn-replay-advance-txid)))))

; The txid advance keeps the article list.
(defthm fn-ppc-advance-txid-articles
  (equal (fn-state-articles (fn-node-acceptance (fn-replay-advance-txid node txid)))
         (fn-state-articles (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-ppc-sn-prepare-node-is-prc
  (equal (fn-ppc-sn-prepare-node node record
                                 (fn-pidx-find-article (fn-record-msgid record)
                                                       (fn-state-articles (fn-node-acceptance node))
                                                       view)
                                 carry)
         (fn-prc-sn-prepare-node node record view carry))
  :hints (("Goal" :in-theory (e/d (fn-ppc-sn-prepare-node fn-prc-sn-prepare-node)
                                  (fn-replay-advance-txid fn-pidx-find-article))
           :use ((:instance fn-ppc-node-prepare-is-prc
                            (s (fn-replay-advance-txid node (fn-record-txid record)))
                            (generation (fn-record-generation record))
                            (msgid (fn-record-msgid record))
                            (payload (fn-record-payload record))
                            (groups (fn-record-groups record))
                            (obligation-id (fn-record-obligation-id record))
                            (subject (fn-record-content-subject record))
                            (evidence (fn-record-release-evidence record))
                            (charge (fn-record-charge record))
                            (stamp (fn-record-stamp record)) (binding (fn-held-binding record)))))))

(defthm fn-ppc-sn-prepare-node-is-sn-prepare-node
  (implies (and (fn-prc-carryp carry)
                (iff dup (fn-acceptedp (fn-record-msgid record)
                                       (fn-state-articles (fn-node-acceptance node)))))
           (equal (fn-ppc-sn-prepare-node node record dup carry)
                  (fn-sn-prepare-node node record)))
  :hints (("Goal" :in-theory (e/d (fn-ppc-sn-prepare-node fn-sn-prepare-node
                                   fn-ppc-node-prepare-is-node-prepare)
                                  (fn-node-prepare fn-replay-advance-txid fn-acceptedp)))))

(in-theory (disable fn-ppc-sn-prepare-node))

; DUP is the acceptance's test of the record's Message-ID (the guard: the
; host computes it from the catalog, fn-ppc-pout-prepare-article-cat).
(defun fn-ppc-dup-okp (s record dup)
  (declare (xargs :guard t))
  (iff dup (fn-acceptedp (fn-record-msgid record)
                         (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))

(defun fn-ppc-spc-prepare (s record dup carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-prc-carryp carry)
                              (fn-ppc-dup-okp s record dup))
                  :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (null (fn-node-stage (fn-sn-node s)))
           (fn-held-p record)
           (equal (fn-hc-generation (fn-held-context record))
                  (fn-sn-keyring-generation s))
           (eq (car (fn-rcon-cpe-projection-step
                     (fn-sn-consumer s) record (fn-sn-identity-next s))) :ok))
      (let* ((node (fn-ppc-sn-prepare-node (fn-sn-node s) record dup carry))
             (files (fn-pcar-stage-record (fn-sn-files s) record)))
        (if (and (fn-rcon-sn-record-bindsp node record)
                 (equal (fn-sf-phase files) :record-staged))
            (fn-sn-update s files node)
          s))
    s))

(defcong iff equal (fn-ppc-spc-prepare s record dup carry) 3
  :hints (("Goal" :in-theory (e/d (fn-ppc-spc-prepare)
                                  (fn-sn-statep fn-pcar-stage-record fn-rcon-sn-record-bindsp
                                   fn-held-p fn-rcon-cpe-projection-step fn-sn-update)))))

(defthm fn-ppc-spc-prepare-is-prc
  (equal (fn-ppc-spc-prepare s record
                             (fn-pidx-find-article (fn-record-msgid record)
                                                   (fn-state-articles
                                                    (fn-node-acceptance (fn-sn-node s)))
                                                   view)
                             carry)
         (fn-prc-spc-prepare s record view carry))
  :hints (("Goal" :in-theory (e/d (fn-ppc-spc-prepare fn-prc-spc-prepare
                                   fn-ppc-sn-prepare-node-is-prc)
                                  (fn-sn-statep fn-pcar-stage-record fn-pidx-find-article
                                   fn-prc-sn-prepare-node fn-rcon-sn-record-bindsp
                                   fn-held-p fn-rcon-cpe-projection-step fn-sn-update)))))

(defthm fn-ppc-spc-prepare-is-pcar-spc-prepare
  (implies (and (fn-prc-carryp carry) (fn-ppc-dup-okp s record dup))
           (equal (fn-ppc-spc-prepare s record dup carry)
                  (fn-pcar-spc-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-ppc-spc-prepare fn-pcar-spc-prepare fn-ppc-dup-okp
                                   fn-ppc-sn-prepare-node-is-sn-prepare-node)
                                  (fn-sn-statep fn-pcar-stage-record fn-acceptedp
                                   fn-sn-prepare-node fn-rcon-sn-record-bindsp
                                   fn-held-p fn-rcon-cpe-projection-step
                                   fn-sn-update fn-pcar-spc-prepare-is-spc-prepare
                                   fn-rcon-cpe-projection-step-is-cpe-projection-step
                                   fn-rcon-sn-record-bindsp-is-sn-record-bindsp
                                   fn-pcar-stage-record-is-stage-record)))))

(verify-guards fn-ppc-spc-prepare
  :hints (("Goal" :use ((:instance fn-ppc-sn-prepare-node-is-sn-prepare-node
                                   (node (fn-sn-node s)))
                        (:instance fn-sn-prepare-node-preserves-state (node (fn-sn-node s))))
           :in-theory (e/d (fn-sn-statep fn-ppc-dup-okp)
                           (fn-sf-statep fn-node-statep fn-node-pending-matchesp
                            fn-sn-pending-record fn-sn-prepare-node fn-acceptedp
                            fn-ppc-sn-prepare-node-is-sn-prepare-node
                            fn-sn-prepare-node-preserves-state
                            fn-prc-carryp)))))

(in-theory (disable fn-ppc-spc-prepare))

(defun fn-ppc-opc-owner-prepare (o record dup carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store o))
                              (fn-prc-carryp carry)
                              (fn-ppc-dup-okp (fn-own-store o) record dup))))
  (fn-own-refresh
   (fn-own-make (fn-ppc-spc-prepare (fn-own-store o) record dup carry)
                (fn-own-view o) (fn-own-conns o)
                (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger-field o)
                (fn-own-clock o) (fn-own-facts o)
                (fn-own-config o) (fn-own-queue o)
                (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))

(defcong iff equal (fn-ppc-opc-owner-prepare o record dup carry) 3
  :hints (("Goal" :in-theory (e/d (fn-ppc-opc-owner-prepare) (fn-own-refresh)))))

(defun fn-ppc-dup-of (o record)
  ; The test the reference chain makes, over the Store node's articles.
  (declare (xargs :guard t :verify-guards nil))
  (fn-pidx-find-article (fn-record-msgid record)
                        (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store o))))
                        (fn-own-view o)))

(defthm fn-ppc-opc-owner-prepare-is-prc
  (equal (fn-ppc-opc-owner-prepare o record (fn-ppc-dup-of o record) carry)
         (fn-prc-opc-owner-prepare o record carry))
  :hints (("Goal" :in-theory (e/d (fn-ppc-opc-owner-prepare fn-prc-opc-owner-prepare
                                   fn-ppc-dup-of fn-ppc-spc-prepare-is-prc)
                                  (fn-own-refresh fn-pidx-find-article fn-prc-spc-prepare)))))

(in-theory (disable fn-ppc-opc-owner-prepare))

(defun fn-ppc-sbud-prepare (oc record budget dup carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-prc-carryp carry)
                              (fn-ppc-dup-okp (fn-sbud-oc-store oc) record dup))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))))
  (if (fn-sbud-admitp budget (fn-sbud-count (fn-sbud-oc-store oc)))
      (fn-ocfg-with-owner
       oc (fn-ppc-opc-owner-prepare (fn-ocfg-owner oc) record dup carry))
    oc))

(defcong iff equal (fn-ppc-sbud-prepare oc record budget dup carry) 4
  :hints (("Goal" :in-theory (e/d (fn-ppc-sbud-prepare)
                                  (fn-sbud-admitp fn-sbud-count fn-sbud-oc-store)))))

(defthm fn-ppc-sbud-prepare-is-prc
  (equal (fn-ppc-sbud-prepare oc record budget (fn-ppc-dup-of (fn-ocfg-owner oc) record) carry)
         (fn-prc-sbud-prepare oc record budget carry))
  :hints (("Goal" :in-theory (e/d (fn-ppc-sbud-prepare fn-prc-sbud-prepare fn-prc-opc-prepare
                                   fn-ppc-opc-owner-prepare-is-prc)
                                  (fn-sbud-admitp fn-sbud-count fn-sbud-oc-store
                                   fn-ppc-dup-of fn-prc-opc-owner-prepare)))))

(in-theory (disable fn-ppc-sbud-prepare))

(defun fn-ppc-psrv-prepare (oc record budget dup carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-prc-carryp carry)
                              (fn-ppc-dup-okp (fn-sbud-oc-store oc) record dup))))
  (if (and (fn-psrv-event-servedp (fn-ocfg-config oc) record)
           (fn-psrv-event-numberedp oc record))
      (fn-ppc-sbud-prepare oc record budget dup carry)
    oc))

(defcong iff equal (fn-ppc-psrv-prepare oc record budget dup carry) 4
  :hints (("Goal" :in-theory (e/d (fn-ppc-psrv-prepare) (fn-psrv-event-servedp fn-psrv-event-numberedp)))))

(defthm fn-ppc-psrv-prepare-is-psrv-prepare
  (equal (fn-ppc-psrv-prepare oc record budget (fn-ppc-dup-of (fn-ocfg-owner oc) record) carry)
         (fn-psrv-prepare oc record budget carry))
  :hints (("Goal" :in-theory (e/d (fn-ppc-psrv-prepare fn-psrv-prepare fn-ppc-sbud-prepare-is-prc)
                                  (fn-psrv-event-servedp fn-psrv-event-numberedp fn-ppc-dup-of
                                   fn-prc-sbud-prepare)))))

(in-theory (disable fn-ppc-psrv-prepare))

; -----------------------------------------------------------------------------
; The host's call: the duplicate test decided once, from the catalog.

(defun fn-ppc-pout-prepare-article-cat (oc record budget carry fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-prc-carryp carry)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                              ; The join's consequence for this Message-ID
                              ; (fn-ppc-pout-prepare-article-cat-is-pout-
                              ; prepare-article discharges it from the join).
                              (fn-ppc-dup-okp
                               (fn-sbud-oc-store oc) record
                               (fn-pidx-find-article-cat
                                (fn-record-msgid record)
                                (fn-state-articles
                                 (fn-node-acceptance
                                  (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
                                (fn-own-view (fn-ocfg-owner oc)) fn-arena fn-cat)))
                  :guard-hints (("Goal" :in-theory (enable fn-sbud-oc-store)))))
  (let* ((o (fn-ocfg-owner oc))
         (dup (fn-pidx-find-article-cat
               (fn-record-msgid record)
               (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store o))))
               (fn-own-view o) fn-arena fn-cat))
         (next (fn-ppc-psrv-prepare oc record budget dup carry)))
    (mv (if (fn-pout-stagedp (fn-sbud-oc-store oc) (fn-sbud-oc-store next))
            :prepared
          (fn-psrv-refusal-kind oc record budget))
        next)))

(in-theory (disable fn-ppc-dup-of))

(defthm fn-ppc-dup-of-is-find-article
  (implies (fn-pidx-view-okp (fn-own-view o))
           (equal (fn-ppc-dup-of o record)
                  (fn-find-article (fn-record-msgid record)
                                   (fn-state-articles
                                    (fn-node-acceptance (fn-sn-node (fn-own-store o)))))))
  :hints (("Goal" :in-theory (e/d (fn-ppc-dup-of) (fn-find-article fn-pidx-find-article)))))

(defthm fn-ppc-view-okp-gives-visible
  (implies (fn-pidx-view-okp view) (fn-ocl-view-visiblep view))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pidx-view-okp))))

; KEYSTONE.  The host's call is the reference prepare, both values.
(defthm fn-ppc-pout-prepare-article-cat-is-pout-prepare-article
  (implies (and (fn-pidx-view-okp (fn-own-view (fn-ocfg-owner oc)))
                (fn-scj-joinp (fn-own-view (fn-ocfg-owner oc)) fn-arena fn-cat))
           (and (equal (mv-nth 0 (fn-ppc-pout-prepare-article-cat oc record budget carry
                                                                  fn-arena fn-cat))
                       (mv-nth 0 (fn-pout-prepare-article oc record budget carry)))
                (equal (mv-nth 1 (fn-ppc-pout-prepare-article-cat oc record budget carry
                                                                  fn-arena fn-cat))
                       (mv-nth 1 (fn-pout-prepare-article oc record budget carry)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ppc-pout-prepare-article-cat fn-pout-prepare-article
                            fn-ppc-dup-of-is-find-article
                            fn-pidx-find-article-cat-is-find-article)
                           (fn-ppc-psrv-prepare fn-psrv-prepare fn-pout-stagedp fn-ppc-dup-of
                            fn-ppc-psrv-prepare-is-psrv-prepare
                            fn-psrv-refusal-kind fn-sbud-oc-store fn-find-article
                            fn-pidx-find-article-cat fn-pidx-view-okp fn-scj-joinp
                            fn-ocl-view-visiblep))
           :use ((:instance fn-pidx-find-article-cat-is-find-article
                            (msgid (fn-record-msgid record))
                            (arts (fn-state-articles
                                   (fn-node-acceptance
                                    (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))))
                            (view (fn-own-view (fn-ocfg-owner oc))))
                 (:instance fn-ppc-dup-of-is-find-article (o (fn-ocfg-owner oc)))
                 (:instance fn-ppc-psrv-prepare-is-psrv-prepare)
                 (:instance fn-ppc-view-okp-gives-visible (view (fn-own-view (fn-ocfg-owner oc))))))))

; The host's owner: fn-ocl-relation and fn-scar-view-indexedp give the view
; facts (fn-pidx-view-okp-of-live-owner), fn-scj-invp the join.
(defthm fn-ppc-pout-prepare-article-cat-of-live-owner
  (implies (and (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat))
           (and (equal (mv-nth 0 (fn-ppc-pout-prepare-article-cat oc record budget carry
                                                                  fn-arena fn-cat))
                       (mv-nth 0 (fn-pout-prepare-article oc record budget carry)))
                (equal (mv-nth 1 (fn-ppc-pout-prepare-article-cat oc record budget carry
                                                                  fn-arena fn-cat))
                       (mv-nth 1 (fn-pout-prepare-article oc record budget carry)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scj-invp)
                           (fn-ppc-pout-prepare-article-cat fn-pout-prepare-article
                            fn-scj-joinp fn-scj-rows-invp fn-scj-vvp fn-scj-live-okp
                            fn-scj-conns-pinp fn-pidx-view-okp fn-ocl-relation
                            fn-scar-view-indexedp))
           :use ((:instance fn-pidx-view-okp-of-live-owner)
                 (:instance fn-ppc-pout-prepare-article-cat-is-pout-prepare-article)))))
