;; fn: a POST's Message-ID tests (PRF-191).
;
; A POST's owner CPU grew with the history (10.8 ms at N = 10,000 against
; 4.7 ms near N = 0; planning/performance-2026-09-26.md row 5) because three
; tests walked a list of N entries with EQUAL:
;
;   1. the buffer verdict (then fn-rclb-existing-action, retired since,
;      PKT-860) found the held article with fn-find-article over the store
;      node's article list.  host/owner-host.lisp
;      fn-owner-existing-action-buffer and fn-owner-prepare-buffer called it,
;      both from host/native/owner.lisp fnn-owner-attempt: twice per POST.
;   2. fn-accept-prepare (books/acceptance.lisp) refuses an accepted
;      Message-ID with fn-acceptedp over the same list.  It is reached from
;      fn-owner-prepare-buffer through fn-pcar-sbud-prepare ->
;      fn-pcar-opc-prepare -> fn-pcar-opc-owner-prepare ->
;      fn-pcar-spc-prepare -> fn-sn-prepare-node -> fn-node-prepare.
;   3. fn-node-prepare (books/node.lisp) tests retention admissibility
;      (fn-retain-admissiblep -> fn-retain-known-id-scanp over the pins), and
;      then fn-retain-admit tests it again on the same arguments.
;
; (1) and (2) once read a Message-ID trie the owner carried over its view.
; The view carries no trie any more (R4: the catalog's Message-ID column
; answers the host's lookups, books/post-identity-catalog.lisp), so the
; lookup here is the scan, fn-find-article, and no equation below has a
; premise on the view.  The chain keeps its `view' argument and the guard
; fn-pidx-view-okp (fn-ocl-view-visiblep) so that the catalog twins and the
; callers above share one argument list; neither is read by a result.
;
; (3) The second admissibility scan is removed: fn-pidx-node-prepare builds
; the admitted ledger directly in the branch where admissibility was just
; decided, which is fn-retain-admit's own body there.  The first scan stays:
; the ledger is keyed by obligation id, which no carried index answers
; (PKT-549).
;
; Every function is guard-verified and proved EQUAL to its reference; the
; one that is not its reference by definition is fn-pidx-node-prepare (3).
; The prepare chain's guard carries the view fact (fn-pidx-view-okp) beside
; the reference's fn-sn-statep: the served host runs a :program wrapper's
; callees raw (specs/host.md "The served reader path"), so no guard is
; evaluated per POST, and the host's obligation for it is the carried
; relation (fn-pidx-view-okp-of-live-owner).

(in-package "ACL2")
(include-book "owner-prepare-carried")
(include-book "owner-served-carried")
(include-book "config-owner-live")
(include-book "store-reclaim-buffer")
(include-book "msgid-index-concrete")
(include-book "store-intern")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-ctl-visible-articles)
                          (:definition fn-ctl-visible-filter)
                          (:definition fn-ctl-withdrawn-by-p))))

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

; fn-find-article MSGID ARTS: the scan.  VIEW is the owner's committed view,
; kept so the prepare chain and its catalog twins share one argument list;
; the lookup reads ARTS only.
(defun fn-pidx-find-article (msgid arts view)
  (declare (xargs :guard t) (ignore view))
  (fn-find-article msgid arts))

; The carried view fact the chain's guards name.
(defun fn-pidx-view-okp (view)
  (declare (xargs :guard t))
  (fn-ocl-view-visiblep view))

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

; The lookup is the scan, for every Message-ID, article list and view.
(defthm fn-pidx-find-article-is-find-article-by-definition
  (equal (fn-pidx-find-article msgid arts view)
         (fn-find-article msgid arts))
  :hints (("Goal" :in-theory (enable fn-pidx-find-article))))

(in-theory (disable fn-pidx-find-article fn-pidx-view-okp))

; The host's owner satisfies the premise: fn-ocl-relation carries the
; visible list (fn-ocl-view-historyp-is-visible).
(defthm fn-pidx-view-okp-of-live-owner
  (implies (fn-ocl-relation oc)
           (fn-pidx-view-okp (fn-own-view (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (e/d (fn-pidx-view-okp fn-ocl-relation)
                                  (fn-ocl-view-historyp fn-ocl-view-visiblep))
           :use ((:instance fn-ocl-view-historyp-is-visible
                            (o (fn-ocfg-owner oc)))))))

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
            ; PKT-635: the acceptance payload is the arena handle.
            (not (natp payload))
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
  (equal (fn-pidx-accept-prepare s generation msgid payload groups
                                 stamp view)
         (fn-accept-prepare s generation msgid payload groups stamp))
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
  (equal (fn-pidx-node-prepare s generation msgid payload groups
                               obligation-id subject evidence charge
                               stamp view)
         (fn-node-prepare s generation msgid payload groups
                          obligation-id subject evidence charge
                          stamp))
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
  (equal (fn-pidx-sn-prepare-node node record view)
         (fn-sn-prepare-node node record))
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
           (fn-held-p record)
           (equal (fn-hc-generation (fn-held-context record))
                  (fn-sn-keyring-generation s))
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
  (equal (fn-pidx-spc-prepare s record view)
         (fn-pcar-spc-prepare s record))
  :hints (("Goal" :in-theory (e/d (fn-pidx-spc-prepare fn-pcar-spc-prepare)
                                  (fn-sn-statep fn-pcar-stage-record
                                   fn-sn-prepare-node fn-rcon-sn-record-bindsp
                                   fn-held-p fn-rcon-cpe-projection-step
                                   fn-sn-update fn-pcar-spc-prepare-is-spc-prepare
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
                (fn-own-pending o) (fn-own-ledger-field o)
                (fn-own-clock o) (fn-own-facts o)
                (fn-own-config o) (fn-own-queue o)
                (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))

(defthm fn-pidx-opc-owner-prepare-is-pcar-opc-owner-prepare
  (equal (fn-pidx-opc-owner-prepare o record)
         (fn-pcar-opc-owner-prepare o record))
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
  (equal (fn-pidx-opc-prepare oc record)
         (fn-pcar-opc-prepare oc record))
  :hints (("Goal" :in-theory (e/d (fn-pidx-opc-prepare fn-pcar-opc-prepare)
                                  (fn-pcar-opc-owner-prepare
                                   fn-pcar-opc-prepare-is-opc-prepare)))))

(in-theory (disable fn-pidx-opc-prepare))
