; served-catalog-join-finish-tests.lisp -- teeth for books/served-catalog-
; join-finish.lisp (the join and the rows invariant across the host's
; finish; lane sca-join-3, step 2).
;
; The owner is catalog-entries-tests' T2 owner (*cet-t2-oc*: the configured
; owner of owner-advance-carried-tests, one POST run through fn-ocfg-step to
; :completing; its history two retention rows and the completing article
; row, handle 2), over an arena holding the payloads.  The catalog is the
; host's load of the rows before the completing one, the pending is the
; store's row prepared after the seal (fn-cat-prepare-sealed), the token the
; host's; the owner after the finish is fn-ccar-own-finish's and the targets
; and index are its view's, as host/owner-host.lisp fn-owner-finish-
; submission passes them.
;
;   1. REACHABLE WITNESS of fn-scj-joinp-at-host-finish: every hypothesis
;      and both conjuncts of the conclusion evaluated (the join's three
;      conjuncts and the rows invariant over the new history); non-vacuous:
;      the refreshed view shows the article and so does the catalog.
;   2. HYPOTHESIS REMOVAL (every retained hypothesis evaluated, the removed
;      one false, the conclusion false): the finish link (a pending row
;      naming another Message-ID).  The rows invariant only JOINTLY with the
;      join before (a catalog already holding the completing row fails
;      both); labelled so.

(in-package "ACL2")

(include-book "catalog-entries-tests")
(include-book "../../books/served-catalog-join-finish")

(defun scjf-rows-of (i fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (if (< i (fn-cat-count fn-cat))
      (cons (fn-cat-at i fn-cat) (scjf-rows-of (+ 1 i) fn-cat))
    nil))

; fn-scj-joinp's body over live stobjs.
(defun scjf-joinp (view fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let ((c (scjf-rows-of 0 fn-cat)))
    (and (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
                (fn-state-articles (fn-own-view-archive view)))
         (fn-scj-marks-below c (fn-cat-count fn-cat))
         (fn-scj-seqs-below c (fn-own-view-version view))
         t)))

; fn-scj-rows-invp's body.
(defun scjf-rows-invp (c events)
  (declare (xargs :mode :program))
  (equal (fn-scj-arts-map c)
         (fn-scj-arts-map (with-local-stobj fn-cat
                            (mv-let (r fn-cat)
                              (let ((fn-cat (fn-sca-load-held-rows-from events nil fn-cat)))
                                (mv (scjf-rows-of 0 fn-cat) fn-cat))
                              r)))))

;; NCAT: the catalog is the load of the first NCAT rows.  MSGID: when
;; non-nil, the pending row names that Message-ID instead.
(defun scjf-run (oc payloads ncat msgid fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (o (fn-ocfg-owner oc))
         (view (fn-own-view o))
         (s (fn-own-store o))
         (rows (fn-sf-records (fn-sn-files s)))
         (events0 (take (- (len rows) 1) rows))
         (event (car (last rows)))
         (fn-cat (fn-sca-load-held-rows (take ncat rows) (fn-own-view-index view) fn-arena fn-cat))
         (row0 (fn-sn-completion-record s))
         (row (if msgid (fn-held-make (fn-record-sequence row0) (fn-record-txid row0)
                                      (fn-record-generation row0) msgid (fn-record-payload row0)
                                      (fn-record-groups row0) (fn-record-obligation-id row0)
                                      (fn-record-content-subject row0) (fn-record-release-evidence row0)
                                      (fn-record-charge row0) (fn-record-stamp row0)
                                      (fn-held-facts row0) (fn-held-context row0) nil nil)
                row0))
         (w (fn-held-wire-of row fn-arena))
         (pending (fn-cat-prepare-sealed w row nil nil nil fn-arena fn-cat))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (o2 (cdr (fn-ccar-own-finish o (fn-ocfg-config oc) fn-arena)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (a (car (fn-state-articles acc2)))
         (verdict (cdr (car (fn-sn-verdicts s2))))
         (c0 (scjf-rows-of 0 fn-cat))
         (hyps (list (if (fn-ccar-completion-enabledp s) t nil)
                     (scjf-joinp view fn-arena fn-cat)
                     (fn-scar-view-indexedp o)
                     (scjf-rows-invp c0 events0)
                     (if (fn-cst-relation s2) t nil)
                     (if (fn-own-store-idlep s2) t nil)
                     (equal (fn-sf-records (fn-sn-files s2)) (append events0 (list event)))
                     (fn-rows-composites-okp (append events0 (list event)) fn-arena)
                     (fn-scj-rows-clearp (append events0 (list event)))
                     (equal (fn-scj-load-h event) (fn-pc-held pending))
                     (fn-pc-p pending)
                     (equal token (fn-pc-token pending))
                     (equal (fn-pc-expected pending) (len c0))
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
                     (<= (nfix (fn-own-view-version view)) (len events0)))))
    (mv-let (word pending2 fn-cat)
      (fn-sca-finish token pending (fn-own-view-index view2)
                     (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                        (fn-own-view-withdrawals view2))
                     fn-cat)
      (declare (ignore word pending2))
      (mv (list hyps
                (list (scjf-joinp view2 fn-arena fn-cat)
                      (scjf-rows-invp (scjf-rows-of 0 fn-cat) (append events0 (list event))))
                (len (fn-state-articles (fn-own-view-archive view2)))
                (fn-cat-count fn-cat))
          fn-arena fn-cat))))

(defun scjf-exec (oc payloads ncat msgid)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scjf-run oc payloads ncat msgid fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(defconst *scjf-all* (make-list 18 :initial-element t))

; 1. Reachable positive witness: all eighteen hypotheses and both conjuncts;
; the refreshed view shows one article, the catalog holds one row.
(assert-event (equal (scjf-exec *cet-t2-oc* *cet-t2-payloads* 2 nil)
                     (list *scjf-all* (list t t) 1 1)))

; 2. The finish link removed: the pending row names <y>, the store's row
; <x>.  Every other hypothesis holds; the catalog commits <y>: the join and
; the rows invariant fail.
(assert-event (equal (scjf-exec *cet-t2-oc* *cet-t2-payloads* 2 "<y@example>")
                     (list (update-nth 9 nil *scjf-all*) (list nil nil) 1 1)))

; The rows invariant removed, JOINTLY with the join before: the catalog is
; the load of all three rows (it already holds the article, which the old
; view does not show; the pending expects its count, 1); the finish commits
; it a second time: both conjuncts fail.
(assert-event (equal (car (scjf-exec *cet-t2-oc* *cet-t2-payloads* 3 nil))
                     (update-nth 1 nil (update-nth 3 nil *scjf-all*))))
(assert-event (equal (cadr (scjf-exec *cet-t2-oc* *cet-t2-payloads* 3 nil)) (list nil nil)))
