; served-catalog-join-inv-tests.lisp -- teeth for books/served-catalog-join-
; inv.lisp, -frame.lisp and -read.lisp (lane sca-join-4, step 5: the
; catalog invariant fn-scj-invp at the opens, across the refresh and across
; the host's served read).
;
; The owner is served-catalog-join-entry-tests' replaying two-article open
; (*scje-oc*: catalog-entries-tests' journal under the default
; configuration, opened by fn-ock-recover-extended), the catalog the host's
; load of its rows under its view's index over an arena holding the
; payloads.  The invariant's five conjuncts are evaluated on live stobjs
; (scji-parts).
;
;   1. REACHABLE WITNESS of fn-scj-invp-at-recover: every antecedent, and the
;      five conjuncts of the conclusion (non-vacuous: two articles visible,
;      the live view's view-of is the count 2).
;   2. REACHABLE WITNESS of fn-scj-invp-of-refresh at that owner (idle, VV,
;      no record past the view): every antecedent and the conclusion.
;   3. HYPOTHESIS REMOVAL (fn-scj-live-okp-of-joined-view, the fact the open
;      keystone turns on): a view whose group index is not its articles'
;      build (the retained hypotheses checked, the omitted one false) is not
;      live over the catalog.
;   5. REACHABLE WITNESS of fn-scj-invp-at-host-article-finish-carried on
;      the T2 owner (catalog-entries-tests' POST run to :completing): the
;      carried hypotheses the pinned tests do not evaluate (the article
;      case, the acceptance's shape, fn-scjs-seenp's and fn-scjs-historyp's
;      bodies, the pin bound) and fn-scj-invp's five conjuncts before (at
;      the owner, over the load of the history before the in-flight event)
;      and after (at the finished owner, over the catalog fn-sca-finish
;      leaves); served-catalog-join-pinned-tests item 4 evaluates the rest.
;   4. WHY THE HOST ROUTES ARTICLES THROUGH THE CATALOG (labelled: a
;      corrupted pairing, not a reachable host state): the same owner paired
;      with the catalog of its FIRST row only -- what the catalog would be
;      had the second article completed without the catalog's finish --
;      fails the invariant's join and rows conjuncts while VV and the pins
;      hold.

(in-package "ACL2")

(include-book "served-catalog-join-entry-tests")
(include-book "served-catalog-join-pinned-tests")
(include-book "../../books/served-catalog-join-inv")

(defun scji-rows-of (i fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (if (< i (fn-cat-count fn-cat))
      (cons (fn-cat-at i fn-cat) (scji-rows-of (+ 1 i) fn-cat))
    nil))

(defun scji-load-list (events)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat
    (mv-let (r fn-cat)
      (let ((fn-cat (fn-sca-load-held-rows-from events nil fn-cat)))
        (mv (scji-rows-of 0 fn-cat) fn-cat))
      r)))

; fn-scr-catalogp's body, executed.
(defun scji-catalogp (archive index v fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (and (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
       (fn-statep archive)
       (fn-gidx-pin-correspondencep index archive)
       (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles archive))
       (fn-cnx-freshp (scji-rows-of 0 fn-cat))
       t))

(defun scji-conns-pinp (conns fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (if (consp conns)
      (let ((conn (car conns)))
        (and (scji-catalogp (fn-own-conn-archive conn)
                            (if (fn-own-conn-group-index conn)
                                (fn-gidx-pin-with-control (fn-own-conn-index conn)
                                                          (fn-own-conn-group-index conn)
                                                          (fn-own-conn-control conn))
                              (fn-own-conn-index conn))
                            (fn-scr-view-of (fn-own-conn-version conn) fn-cat) fn-arena fn-cat)
             (scji-conns-pinp (cdr conns) fn-arena fn-cat)))
    t))

; The five conjuncts of fn-scj-invp, and the live view's view-of.
(defun scji-parts (o fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((view (fn-own-view o))
         (s (fn-own-store o))
         (c (scji-rows-of 0 fn-cat))
         (records (fn-sf-records (fn-sn-files s)))
         (idx (if (fn-own-view-group-index view)
                  (fn-gidx-pin-with-control (fn-own-view-index view) (fn-own-view-group-index view)
                                            (fn-own-view-control view))
                (fn-own-view-index view))))
    (list (and (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
                      (fn-state-articles (fn-own-view-archive view)))
               (fn-scj-marks-below c (fn-cat-count fn-cat))
               (fn-scj-seqs-below c (fn-own-view-version view))
               t)
          (equal (fn-scj-arts-map c)
                 (fn-scj-arts-map (scji-load-list (fn-own-take (fn-own-view-version view) records))))
          (and (equal (fn-own-view-raw view) (fn-state-articles (fn-node-acceptance (fn-sn-node s))))
               (equal (fn-own-view-verdicts view) (fn-sn-verdicts s)))
          (scji-catalogp (fn-own-view-archive view) idx
                         (fn-scr-view-of (fn-own-view-version view) fn-cat) fn-arena fn-cat)
          (scji-conns-pinp (fn-own-conns o) fn-arena fn-cat)
          (fn-scr-view-of (fn-own-view-version view) fn-cat))))

; Load ROWS under the view's index of O2 into the arena of the payloads and
; evaluate the parts at O.
(defun scji-run (o rows fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many *scje-payloads* fn-arena))
         (fn-cat (fn-sca-load-held-rows rows (fn-own-view-index (fn-own-view o)) fn-arena fn-cat)))
    (mv (list (scji-parts o fn-arena fn-cat)
              (and (fn-arena-p fn-arena)
                   (fn-rows-handles-inp rows fn-arena)
                   (fn-rows-composites-okp rows fn-arena)
                   t))
        fn-arena fn-cat)))

(defun scji-exec (o rows)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scji-run o rows fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

; -----------------------------------------------------------------------------
; 1. fn-scj-invp-at-recover at the two-article open (prefix nil, suffix the rows).

(assert-event (not (equal *scje-oc* :fault)))
(assert-event (fn-scj-rows-clearp (append nil *scje-rows*)))
(assert-event (true-listp *scje-rows*))
(assert-event (fn-statep (fn-own-view-archive *scje-view*)))
(assert-event (equal (fn-own-conns *scje-o*) nil))
(assert-event (equal (scji-exec *scje-o* *scje-srows*)
                     (list (list t t t t t 2) t)))

; -----------------------------------------------------------------------------
; 2. fn-scj-invp-of-refresh at that owner.

(defconst *scji-refreshed* (fn-own-refresh *scje-o*))
(assert-event (fn-scar-view-indexedp *scje-o*))
(assert-event (natp (fn-own-view-version *scje-view*)))
(assert-event (<= (fn-own-view-version *scje-view*) (len *scje-srows*)))
(assert-event (fn-scj-no-rowsp (nthcdr (fn-own-view-version *scje-view*) *scje-srows*)))
(assert-event (fn-statep (fn-own-view-archive (fn-own-view *scji-refreshed*))))
(assert-event (fn-own-store-idlep (fn-own-store *scje-o*)))
(assert-event (equal (scji-exec *scji-refreshed* *scje-srows*)
                     (list (list t t t t t 2) t)))

; -----------------------------------------------------------------------------
; 3. Removal: the group index not the articles' build.

(defconst *scji-bad-gidx* (update-nth 5 '((:none)) *scje-view*))
(assert-event (not (equal (fn-own-view-group-index *scji-bad-gidx*)
                          (fn-gidx-build (fn-state-articles (fn-own-view-archive *scji-bad-gidx*))))))
(assert-event (equal (fn-own-view-index *scji-bad-gidx*)
                     (fn-midx-build (fn-state-articles (fn-own-view-archive *scji-bad-gidx*)))))
(assert-event (fn-statep (fn-own-view-archive *scji-bad-gidx*)))
(assert-event (equal (scji-exec (update-nth 1 *scji-bad-gidx* *scje-o*) *scje-srows*)
                     (list (list t t t nil t 2) t)))

; -----------------------------------------------------------------------------
; 4. The catalog of the first row only, against the two-article owner.

(assert-event (equal (scji-exec *scje-o* (take 1 *scje-srows*))
                     (list (list nil nil t nil t 1) t)))

; -----------------------------------------------------------------------------
; 5. fn-scj-invp-at-host-article-finish-carried on the T2 owner.

(defun scji-t2-run (oc payloads fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (o (fn-ocfg-owner oc))
         (view (fn-own-view o))
         (s (fn-own-store o))
         (r (fn-ccar-completion-record s))
         (rows (fn-sf-records (fn-sn-files s)))
         (v (fn-own-view-version view))
         (seen (butlast rows 1))
         (fn-cat (fn-sca-load-held-rows seen (fn-own-view-index view) fn-arena fn-cat))
         (row (fn-sn-completion-record s))
         (w (fn-held-wire-of row fn-arena))
         (pending (fn-cat-prepare-sealed w row nil nil nil fn-arena fn-cat))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (o2 (cdr (fn-ccar-own-finish o (fn-ocfg-config oc) fn-arena)))
         (view2 (fn-own-view o2))
         (hyps (list (not (or (fn-evc-retentionp r) (fn-evc-consumerp r) (fn-evc-topicp r)
                              (fn-evc-stxep r) (fn-evc-stxkp r) (fn-evc-stxap r)))
                     (if (fn-statep (fn-node-acceptance (fn-sn-node s))) t nil)
                     (equal (fn-sf-phase (fn-sn-files s)) :completing)
                     (and (<= v (len seen)) (fn-scj-no-rowsp (nthcdr v seen)))
                     (and (natp v) (<= v (len rows)) (true-listp rows))
                     (consp rows)
                     (fn-scj-conns-versions-atmostp (fn-own-conns o) v)
                     (equal (fn-scj-load-h (car (last rows))) (fn-pc-held pending))
                     (equal token (fn-pc-token pending))))
         (before (scji-parts o fn-arena fn-cat)))
    (mv-let (word pending2 fn-cat)
      (fn-sca-finish token pending (fn-own-view-index view2)
                     (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                        (fn-own-view-withdrawals view2))
                     fn-cat)
      (declare (ignore word pending2))
      (mv (list hyps before (scji-parts o2 fn-arena fn-cat)
                (len (fn-state-articles (fn-own-view-archive view)))
                (len (fn-state-articles (fn-own-view-archive view2))))
          fn-arena fn-cat))))

(defun scji-t2-exec (oc payloads)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scji-t2-run oc payloads fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event (equal (scji-t2-exec *cet-t2-oc* *cet-t2-payloads*)
                     (list (make-list 9 :initial-element t)
                           (list t t t t t 0)
                           (list t t t t t 1)
                           0 1)))
