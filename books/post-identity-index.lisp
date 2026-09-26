;; fn: a POST's Message-ID tests answered from the owner's view trie (PRF-191).
;
; A POST's owner CPU grew with the history (10.8 ms at N = 10,000 against
; 4.7 ms near N = 0; planning/performance-2026-09-26.md row 5) because three
; tests walked a list of N entries with EQUAL:
;
;   1. fn-rclb-existing-action (books/store-reclaim-buffer.lisp) finds the
;      held article with fn-find-article over the store node's article list.
;      host/owner-host.lisp fn-owner-existing-action-buffer and
;      fn-owner-prepare-buffer call it, both from host/native/owner.lisp
;      fnn-owner-attempt: twice per POST.
;   2. fn-accept-prepare (books/acceptance.lisp) refuses an accepted
;      Message-ID with fn-acceptedp over the same list.  It is reached from
;      fn-owner-prepare-buffer through fn-pcar-sbud-prepare ->
;      fn-pcar-opc-prepare -> fn-pcar-opc-owner-prepare ->
;      fn-pcar-spc-prepare -> fn-sn-prepare-node -> fn-node-prepare.
;   3. fn-node-prepare (books/node.lisp) tests retention admissibility
;      (fn-retain-admissiblep -> fn-retain-known-id-scanp over the pins), and
;      then fn-retain-admit tests it again on the same arguments.
;
; (1) and (2) are answered here from the Message-ID trie the owner already
; carries over its committed view (fn-own-view-index): the lookup walks the
; Message-ID's characters, not the history.  Two facts about the view make
; the trie's answer the scan's, for EVERY article list the view's raw list
; is found equal to at run time:
;
;   - fn-scar-view-indexedp (books/owner-served-carried.lisp): the trie is
;     fn-midx-build of the visible articles.  Established by fn-own-start and
;     kept by every owner transition the host installs
;     (books/owner-offer-indexed.lisp, fn-oix-*).
;   - fn-ocl-view-visiblep (books/config-owner-live.lisp): the visible list
;     is fn-ctl-visible-articles of the raw list.  A conjunct of
;     fn-ocl-relation through fn-ocl-view-historyp
;     (fn-ocl-view-historyp-is-visible), which the host's open establishes
;     and every configured-owner transition preserves.
;
; A raw article is hidden from the visible list only by a withdrawal record
; that targets its Message-ID (fn-ctl-withdrawn-by-p).  So when no record
; targets the Message-ID asked for, the visible list and the raw list find
; the same article (fn-pidx-find-in-visible-is-find), and the trie answers.
; When one does -- a cancelled article's Message-ID posted again -- the
; lookup takes the scan; so does a raw list that is not the view's (the
; test is EQUAL, which is one pointer comparison when the view was refreshed
; from this node, fn-own-refresh).  Its cost is the withdrawal records, not
; the history.
;
; Why not the Store's derived event index (fn-ceis-indexedp, PRF-144): its
; Message-ID half maps a Message-ID to the history's article RECORDS, while
; these tests read the node's ARTICLES (a reclaimed article's payload is a
; tombstone the record does not hold), so the equation would be a theorem
; about the whole replay.  The view trie is keyed by exactly the articles.
;
; (3) The second admissibility scan is removed: fn-pidx-node-prepare builds
; the admitted ledger directly in the branch where admissibility was just
; decided, which is fn-retain-admit's own body there.  The first scan stays:
; the ledger is keyed by obligation id, which no carried index answers
; (PKT-549).
;
; Every function is its reference with the test replaced, is guard-verified,
; and is proved EQUAL to the reference.  The prepare chain's guard carries
; the view facts (fn-pidx-view-okp) beside the reference's fn-sn-statep:
; the served host runs a :program wrapper's callees raw
; (specs/host.md "The served reader path"), so no guard is evaluated per
; POST, and the host's obligation for it is the pair of carried relations
; above (fn-pidx-view-okp-of-live-owner).

(in-package "ACL2")
(include-book "owner-prepare-carried")
(include-book "owner-served-carried")
(include-book "config-owner-live")
(include-book "store-reclaim-buffer")
(include-book "msgid-index-concrete")

; -----------------------------------------------------------------------------
; The lookup

; Some withdrawal record names MSGID as its target.  Any record: the fallback
; is exact, so the test may be generous.
(defun fn-pidx-targetedp (msgid withdrawals)
  (declare (xargs :guard t))
  (if (consp withdrawals)
      (or (equal (fn-ctl-w-target (car withdrawals)) msgid)
          (fn-pidx-targetedp msgid (cdr withdrawals)))
    nil))

; fn-find-article MSGID ARTS, through the view's trie when ARTS is the
; view's raw list and no withdrawal targets MSGID.
(defun fn-pidx-find-article (msgid arts view)
  (declare (xargs :guard t))
  (if (and (stringp msgid)
           (< 0 (length msgid))
           (equal arts (fn-own-view-raw view))
           (not (fn-pidx-targetedp msgid (fn-own-view-withdrawals view))))
      (fn-mxc-lookup msgid (fn-own-view-index view))
    (fn-find-article msgid arts)))

; The two carried view facts the lookup reads, named for the guards below.
(defun fn-pidx-view-okp (view)
  (declare (xargs :guard t))
  (and (fn-ocl-view-visiblep view)
       (fn-midx-correspondencep (fn-own-view-index view)
                                (fn-state-articles (fn-own-view-archive view)))))

(local
 (defthm fn-pidx-untargeted-article-is-not-withdrawn
   (implies (and (not (fn-pidx-targetedp msgid withdrawals))
                 (equal (fn-article-msgid article) msgid))
            (not (fn-ctl-withdrawn-by-p article withdrawals articles verdicts)))
   :hints (("Goal" :induct (fn-ctl-withdrawn-by-p article withdrawals
                                                   articles verdicts)
            :in-theory (disable fn-ctl-withdrawalp fn-ctl-withdrawal-effect
                                fn-ctl-has-msgid-p fn-ctl-lookup-verdict
                                fn-ctl-effect-withdrawsp)))))

; An untargeted Message-ID is found alike in the visible list and in the list
; it filters.
(defthm fn-pidx-find-in-visible-is-find
  (implies (not (fn-pidx-targetedp msgid withdrawals))
           (equal (fn-find-article msgid
                                   (fn-ctl-visible-filter xs withdrawals
                                                          articles verdicts))
                  (fn-find-article msgid xs)))
  :hints (("Goal" :induct (fn-ctl-visible-filter xs withdrawals articles verdicts)
           :in-theory (e/d (fn-find-article)
                           (fn-ctl-withdrawn-by-p)))))

(local
 (defthm fn-pidx-nonempty-string-has-key-chars
   (implies (stringp msgid)
            (equal (consp (fn-midx-key-chars msgid)) (< 0 (length msgid))))
   :hints (("Goal" :in-theory (enable fn-midx-key-chars length)
            :expand ((len (coerce msgid 'list)))))))

; KEYSTONE (the lookup).  Over a view whose trie is the index of its visible
; list and whose visible list filters its raw list, the lookup is the scan
; of ARTS, for every Message-ID and every article list.
(defthm fn-pidx-find-article-is-find-article
  (implies (and (fn-ocl-view-visiblep view)
                (fn-midx-correspondencep
                 (fn-own-view-index view)
                 (fn-state-articles (fn-own-view-archive view))))
           (equal (fn-pidx-find-article msgid arts view)
                  (fn-find-article msgid arts)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-find-article fn-ocl-view-visiblep
                                   fn-midx-correspondencep
                                   fn-midx-concrete-lookup-is-lookup
                                   fn-ctl-visible-articles)
                                  (fn-midx-lookup fn-midx-build fn-find-article
                                   fn-mxc-lookup fn-ctl-visible-filter
                                   fn-pidx-targetedp fn-midx-key-chars))
           :use ((:instance fn-midx-lookup-of-build-is-find-article-for-nonempty
                            (articles (fn-state-articles
                                       (fn-own-view-archive view))))))))

(defthm fn-pidx-find-article-under-view-okp
  (implies (fn-pidx-view-okp view)
           (equal (fn-pidx-find-article msgid arts view)
                  (fn-find-article msgid arts)))
  :hints (("Goal" :in-theory (disable fn-pidx-find-article
                                      fn-ocl-view-visiblep
                                      fn-midx-correspondencep))))

(in-theory (disable fn-pidx-find-article fn-pidx-view-okp))

; The host's owner satisfies the premise: fn-ocl-relation carries the
; visible list (fn-ocl-view-historyp-is-visible) and fn-scar-view-indexedp
; the trie.
(defthm fn-pidx-view-okp-of-live-owner
  (implies (and (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc)))
           (fn-pidx-view-okp (fn-own-view (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (e/d (fn-pidx-view-okp fn-ocl-relation
                                   fn-scar-view-indexedp)
                                  (fn-ocl-view-historyp fn-ocl-view-visiblep
                                   fn-midx-correspondencep))
           :use ((:instance fn-ocl-view-historyp-is-visible
                            (o (fn-ocfg-owner oc)))))))

; -----------------------------------------------------------------------------
; (1) The duplicate-versus-conflict decision the host asks before a prepare.

(defun fn-pidx-existing-action (msgid fn-octets groups o)
  ; fn-rclb-existing-action with the article found through the view trie.
  (declare (xargs :stobjs fn-octets :guard t))
  (let ((article (fn-pidx-find-article
                  msgid
                  (fn-state-articles
                   (fn-node-acceptance (fn-sn-node (fn-own-store o))))
                  (fn-own-view o))))
    (if article
        (if (and (fn-rclb-same-articlep (fn-record-string-octets msgid) fn-octets
                                        (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

; KEYSTONE (1).  The host's call is the buffer decision it replaced, and so,
; by fn-rclb-existing-action-is-rcl-existing-action, the tombstone-aware
; verdict of books/store-reclaim.lisp.
(defthm fn-pidx-existing-action-is-rclb-existing-action
  (implies (and (fn-ocl-view-visiblep (fn-own-view o))
                (fn-scar-view-indexedp o))
           (equal (fn-pidx-existing-action msgid fn-octets groups o)
                  (fn-rclb-existing-action msgid fn-octets groups
                                           (fn-own-store o))))
  :hints (("Goal" :in-theory (e/d (fn-pidx-existing-action
                                   fn-rclb-existing-action
                                   fn-scar-view-indexedp)
                                  (fn-rclb-same-articlep fn-ocl-view-visiblep
                                   fn-midx-correspondencep fn-find-article)))))

; -----------------------------------------------------------------------------
; (2) and (3) The prepare chain.

(local
 (defthm fn-pidx-find-article-iff-acceptedp
   (implies (stringp msgid)
            (iff (fn-find-article msgid articles)
                 (fn-acceptedp msgid articles)))
   :hints (("Goal" :in-theory (enable fn-find-article fn-acceptedp
                                      fn-article-msgid)))))

; fn-accept-prepare with the duplicate test through the view.
(defun fn-pidx-accept-prepare (s generation msgid payload groups stamp view)
  (declare (xargs :guard (fn-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-statep s)) :exec nil)
      s
    (if (or (equal (fn-state-fenced s) t)
            (consp (fn-state-pending s))
            (not (natp generation))
            (not (stringp msgid))
            (not (fn-octet-listp payload))
            (not (fn-record-stampp stamp))
            (not (fn-selection-validp groups (fn-state-groups s)))
            (fn-pidx-find-article msgid (fn-state-articles s) view))
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

(verify-guards fn-pidx-accept-prepare
  :hints (("Goal" :in-theory (enable fn-statep))))

(defthm fn-pidx-accept-prepare-is-accept-prepare
  (implies (fn-pidx-view-okp view)
           (equal (fn-pidx-accept-prepare s generation msgid payload groups
                                          stamp view)
                  (fn-accept-prepare s generation msgid payload groups stamp)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-accept-prepare fn-accept-prepare)
                                  (fn-statep fn-make-state fn-make-pending
                                   fn-selection-validp fn-find-article
                                   fn-acceptedp)))))

(in-theory (disable fn-pidx-accept-prepare))

; fn-node-prepare with the twin above, and with the admitted ledger built in
; the branch where fn-retain-admissiblep has just held (fn-retain-admit's
; body there), instead of fn-retain-admit deciding it a second time.
(defun fn-pidx-node-prepare (s generation msgid payload groups
                               obligation-id subject evidence charge stamp view)
  (declare (xargs :guard (fn-node-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-node-statep s)) :exec nil)
      s
    (let ((retention (fn-node-retention s)))
      (if (not (fn-retain-admissiblep retention obligation-id subject :archive
                                      evidence charge))
          s
        (let ((next-acceptance
               (fn-pidx-accept-prepare (fn-node-acceptance s)
                                       generation msgid payload groups stamp
                                       view)))
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
               (fn-retain-releases retention)))
             (fn-node-bindings s))))))))

(defthm fn-pidx-node-prepare-is-node-prepare
  (implies (fn-pidx-view-okp view)
           (equal (fn-pidx-node-prepare s generation msgid payload groups
                                        obligation-id subject evidence charge
                                        stamp view)
                  (fn-node-prepare s generation msgid payload groups
                                   obligation-id subject evidence charge
                                   stamp)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-node-prepare fn-node-prepare
                                   fn-retain-admit)
                                  (fn-node-statep fn-retain-admissiblep
                                   fn-accept-prepare fn-retain-make-state
                                   fn-retain-make-obligation
                                   fn-node-make-state fn-node-make-stage)))))

(verify-guards fn-pidx-node-prepare
  :hints (("Goal" :in-theory (enable fn-node-statep fn-retain-admissiblep))))

(in-theory (disable fn-pidx-node-prepare))

; fn-sn-prepare-node, through the twin.
(defun fn-pidx-sn-prepare-node (node record view)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (fn-pidx-node-prepare (fn-replay-advance-txid node (fn-record-txid record))
                        (fn-record-generation record) (fn-record-msgid record)
                        (fn-record-payload record) (fn-record-groups record)
                        (fn-record-obligation-id record)
                        (fn-record-content-subject record)
                        (fn-record-release-evidence record)
                        (fn-record-charge record)
                        (fn-record-stamp record)
                        view))

(verify-guards fn-pidx-sn-prepare-node)

(defthm fn-pidx-sn-prepare-node-is-sn-prepare-node
  (implies (fn-pidx-view-okp view)
           (equal (fn-pidx-sn-prepare-node node record view)
                  (fn-sn-prepare-node node record)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-sn-prepare-node fn-sn-prepare-node)
                                  (fn-node-prepare fn-replay-advance-txid)))))

(in-theory (disable fn-pidx-sn-prepare-node))

; fn-pcar-spc-prepare (books/owner-prepare-carried.lisp), through the twin.
(defun fn-pidx-spc-prepare (s record view)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-pidx-view-okp view))
                  :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (null (fn-node-stage (fn-sn-node s)))
           (fn-rcon-record-p record)
           (not (equal (fn-record-stamp record) :legacy))
           (eq (car (fn-rcon-cpe-projection-step
                     (fn-sn-consumer s) record (fn-sn-identity-next s))) :ok))
      (let* ((node (fn-pidx-sn-prepare-node (fn-sn-node s) record view))
             (files (fn-pcar-stage-record (fn-sn-files s) record)))
        (if (and (fn-rcon-sn-record-bindsp node record)
                 (equal (fn-sf-phase files) :record-staged))
            (fn-sn-update s files node)
          s))
    s))

(defthm fn-pidx-spc-prepare-is-pcar-spc-prepare
  (implies (fn-pidx-view-okp view)
           (equal (fn-pidx-spc-prepare s record view)
                  (fn-pcar-spc-prepare s record)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-spc-prepare fn-pcar-spc-prepare)
                                  (fn-sn-statep fn-pcar-stage-record
                                   fn-sn-prepare-node fn-rcon-sn-record-bindsp
                                   fn-rcon-record-p fn-rcon-cpe-projection-step
                                   fn-sn-update fn-pcar-spc-prepare-is-spc-prepare
                                   fn-rcon-record-p-is-record-p
                                   fn-rcon-cpe-projection-step-is-cpe-projection-step
                                   fn-rcon-sn-record-bindsp-is-sn-record-bindsp
                                   fn-pcar-stage-record-is-stage-record)))))

(verify-guards fn-pidx-spc-prepare
  :hints (("Goal" :use ((:instance fn-pidx-spc-prepare-is-pcar-spc-prepare)
                        (:instance fn-pcar-spc-prepare-is-spc-prepare))
           :in-theory (e/d (fn-sn-statep)
                           (fn-sf-statep fn-node-statep fn-node-pending-matchesp
                            fn-sn-pending-record fn-sn-prepare-node
                            fn-pidx-view-okp)))))

(in-theory (disable fn-pidx-spc-prepare))

; fn-pcar-opc-owner-prepare, fn-pcar-opc-prepare and fn-pcar-sbud-prepare,
; through the twin; the view is the owner's own.
(defun fn-pidx-opc-owner-prepare (o record)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store o))
                              (fn-pidx-view-okp (fn-own-view o)))))
  (fn-own-refresh
   (fn-own-make (fn-pidx-spc-prepare (fn-own-store o) record (fn-own-view o))
                (fn-own-view o) (fn-own-conns o)
                (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger o)
                (fn-own-clock o) (fn-own-facts o)
                (fn-own-config o) (fn-own-queue o)
                (fn-own-inflight o) (fn-own-feeds o))))

(defthm fn-pidx-opc-owner-prepare-is-pcar-opc-owner-prepare
  (implies (fn-pidx-view-okp (fn-own-view o))
           (equal (fn-pidx-opc-owner-prepare o record)
                  (fn-pcar-opc-owner-prepare o record)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-opc-owner-prepare
                                   fn-pcar-opc-owner-prepare)
                                  (fn-own-refresh fn-pcar-spc-prepare
                                   fn-pcar-opc-owner-prepare-is-opc-owner-prepare)))))

(in-theory (disable fn-pidx-opc-owner-prepare))

(defun fn-pidx-opc-prepare (oc record)
  (declare (xargs :guard (and (fn-sn-statep
                               (fn-own-store (fn-ocfg-owner oc)))
                              (fn-pidx-view-okp
                               (fn-own-view (fn-ocfg-owner oc))))))
  (fn-ocfg-with-owner
   oc (fn-pidx-opc-owner-prepare (fn-ocfg-owner oc) record)))

(defthm fn-pidx-opc-prepare-is-pcar-opc-prepare
  (implies (fn-pidx-view-okp (fn-own-view (fn-ocfg-owner oc)))
           (equal (fn-pidx-opc-prepare oc record)
                  (fn-pcar-opc-prepare oc record)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-opc-prepare fn-pcar-opc-prepare)
                                  (fn-pcar-opc-owner-prepare
                                   fn-pcar-opc-prepare-is-opc-prepare)))))

(in-theory (disable fn-pidx-opc-prepare))

; The function host/owner-host.lisp fn-owner-prepare-buffer installs.
(defun fn-pidx-sbud-prepare (oc record budget)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-pidx-view-okp
                               (fn-own-view (fn-ocfg-owner oc))))))
  (if (fn-sbud-admitp budget (fn-sbud-used (fn-sbud-oc-store oc)))
      (fn-pidx-opc-prepare oc record)
    oc))

; KEYSTONE (2, 3).  The host's prepare is the carried prepare it replaced,
; for every record and budget, on every configured owner whose view the two
; carried relations describe; so, by fn-pcar-sbud-prepare-is-sbud-prepare,
; every theorem about fn-sbud-prepare is a theorem about the host's call.
(defthm fn-pidx-sbud-prepare-is-pcar-sbud-prepare
  (implies (and (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner oc)))
                (fn-scar-view-indexedp (fn-ocfg-owner oc)))
           (equal (fn-pidx-sbud-prepare oc record budget)
                  (fn-pcar-sbud-prepare oc record budget)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-sbud-prepare fn-pcar-sbud-prepare
                                   fn-pidx-view-okp fn-scar-view-indexedp)
                                  (fn-pcar-opc-prepare fn-sbud-admitp
                                   fn-sbud-used fn-ocl-view-visiblep
                                   fn-midx-correspondencep
                                   fn-pcar-sbud-prepare-is-sbud-prepare)))))

(in-theory (disable fn-pidx-sbud-prepare))
