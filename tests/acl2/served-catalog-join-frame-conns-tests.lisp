; served-catalog-join-frame-conns-tests.lisp -- teeth for books/served-
; catalog-join-frame-conns.lisp (the connection arms keep fn-scj-invp; lane
; sca-join-4, sub-lane F-conn).
;
; fn-scj-invp's five conjuncts are evaluated on live stobjs by their bodies
; (scjfc-invp: the join, the rows invariant, VV, the live view, every
; connection's pin).
;
;   1. REACHABLE WITNESS of fn-scj-invp-of-ocfg-open (and of the keystone
;      fn-scj-conn-pinp-of-view-pinned at the new record): the host's full
;      open of catalog-entries-tests' journal extended to two articles
;      (fn-ock-recover-extended; the catalog the host's load of its rows
;      under the view's index); the antecedent (all five conjuncts) and the
;      conclusion (all five, over one more connection) evaluated; the new
;      record's pin fields are the view's and it is pinned.
;   2. HYPOTHESIS REMOVAL for the keystone: the same owner with a view that
;      is not live over the catalog (its two articles oldest first, the
;      index built from that list): the retained hypothesis (the record's
;      pin fields are the view's) holds, live-okp is false, and the opened
;      record is not pinned.
;   3. REACHABLE WITNESS of fn-scj-invp-of-ocfg-advance: catalog-entries-
;      tests' T2 owner after the host's finish (fn-ccar-own-finish, the
;      catalog finished by fn-sca-finish as host/owner-host.lisp does); its
;      two connections (the fixture's and the POST one) are pinned at the
;      version before the article; the POST connection's
;      advance moves it to the refreshed view's: the antecedent and the
;      conclusion evaluated, the version moving from 2 to 3 (non-vacuous: a
;      re-pin, not an identity).

(in-package "ACL2")

(include-book "catalog-entries-tests")
(include-book "../../books/served-catalog-join-frame-conns")

(defun scjfc-rows-of (i fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (if (< i (fn-cat-count fn-cat))
      (cons (fn-cat-at i fn-cat) (scjfc-rows-of (+ 1 i) fn-cat))
    nil))

; fn-scr-catalogp's body.
(defun scjfc-catalogp (archive index v fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (and (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
       (fn-nntp-projectionp archive)
       (fn-gidx-pin-correspondencep index archive)
       (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles archive))
       (fn-cnx-freshp (scjfc-rows-of 0 fn-cat))
       t))

(defun scjfc-pinned-index (index buckets control)
  (declare (xargs :mode :program))
  (if buckets (fn-gidx-pin-with-control index buckets control) index))

; fn-scj-conn-pinp's body.
(defun scjfc-conn-pinp (conn fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (scjfc-catalogp (fn-own-conn-archive conn)
                  (scjfc-pinned-index (fn-own-conn-index conn) (fn-own-conn-group-index conn)
                                      (fn-own-conn-control conn))
                  (fn-scr-view-of (fn-own-conn-version conn) fn-cat)
                  fn-arena fn-cat))

(defun scjfc-conns-pinp (conns fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (if (consp conns)
      (and (scjfc-conn-pinp (car conns) fn-arena fn-cat)
           (scjfc-conns-pinp (cdr conns) fn-arena fn-cat))
    t))

; fn-scj-live-okp's body (fn-scr-live-catalogp of fn-own-view-live).
(defun scjfc-live-okp (view fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (scjfc-catalogp (fn-own-view-archive view)
                  (scjfc-pinned-index (fn-own-view-index view) (fn-own-view-group-index view)
                                      (fn-own-view-control view))
                  (fn-scr-view-of (fn-own-view-version view) fn-cat)
                  fn-arena fn-cat))

; fn-scj-view-pinned-connp's body.
(defun scjfc-view-pinned-connp (conn view)
  (declare (xargs :mode :program))
  (and (equal (fn-own-conn-version conn) (fn-own-view-version view))
       (equal (fn-own-conn-archive conn) (fn-own-view-archive view))
       (equal (fn-own-conn-index conn) (fn-own-view-index view))
       (equal (fn-own-conn-group-index conn) (fn-own-view-group-index view))
       (equal (fn-own-conn-control conn) (fn-own-view-control view))))

; fn-scj-invp's body, conjunct by conjunct.
(defun scjfc-invp (o fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((view (fn-own-view o))
         (s (fn-own-store o))
         (c (scjfc-rows-of 0 fn-cat))
         (events (fn-own-take (fn-own-view-version view) (fn-sf-records (fn-sn-files s)))))
    (list (and (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
                      (fn-state-articles (fn-own-view-archive view)))
               (fn-scj-marks-below c (fn-cat-count fn-cat))
               (fn-scj-seqs-below c (fn-own-view-version view))
               t)
          (equal (fn-scj-arts-map c)
                 (fn-scj-arts-map (with-local-stobj fn-cat
                                    (mv-let (r fn-cat)
                                      (let ((fn-cat (fn-sca-load-held-rows-from events nil fn-cat)))
                                        (mv (scjfc-rows-of 0 fn-cat) fn-cat))
                                      r))))
          (and (equal (fn-own-view-raw view)
                      (fn-state-articles (fn-node-acceptance (fn-sn-node s))))
               (equal (fn-own-view-verdicts view) (fn-sn-verdicts s)))
          (scjfc-live-okp view fn-arena fn-cat)
          (scjfc-conns-pinp (fn-own-conns o) fn-arena fn-cat))))

(defconst *scjfc-all* (list t t t t t))

; -----------------------------------------------------------------------------
; 1 and 2.  The open.

(defconst *scjfc-w1* (cet-record 1 1 "<two@example>"))
(defconst *scjfc-ws* (list *cet-w0* *scjfc-w1*))
(defconst *scjfc-payloads* (list (fn-record-payload *cet-w0*) (fn-record-payload *scjfc-w1*)))
(defconst *scjfc-oc*
  (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture *cet-configs* nil) *cet-configs*
                                          (cet-rows *scjfc-ws*))
                           *cet-configs* 8 4))

;; The catalog is the host's load of the store's rows under the view's index
;; (OC's own); OC2 is the configured owner the open runs on.
(defun scjfc-open-run (oc oc2 fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many *scjfc-payloads* fn-arena))
         (o (fn-ocfg-owner oc))
         (fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                        (fn-own-view-index (fn-own-view o)) fn-arena fn-cat))
         (o2 (fn-ocfg-owner oc2))
         (after (fn-ocfg-owner (cdr (fn-ocfg-open oc2 nil))))
         (conn (car (fn-own-conns after))))
    (mv (list (scjfc-invp o2 fn-arena fn-cat)
              (scjfc-invp after fn-arena fn-cat)
              (len (fn-own-conns o2))
              (len (fn-own-conns after))
              (scjfc-view-pinned-connp conn (fn-own-view o2))
              (scjfc-live-okp (fn-own-view o2) fn-arena fn-cat)
              (scjfc-conn-pinp conn fn-arena fn-cat))
        fn-arena fn-cat)))

(defun scjfc-open-exec (oc oc2)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scjfc-open-run oc oc2 fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

; The fixture replays, two articles visible, no connection yet.
(assert-event (not (equal *scjfc-oc* :fault)))
(assert-event (fn-ocl-relation *scjfc-oc*))
(assert-event (equal (fn-article-msgids (fn-state-articles (fn-own-view-archive
                                                             (fn-own-view (fn-ocfg-owner *scjfc-oc*)))))
                     '("<two@example>" "<one@example>")))

; 1. The antecedent (all five conjuncts), the conclusion (all five over one
; more connection), the new record at the view's pin, the view live and the
; record pinned.
(assert-event (equal (scjfc-open-exec *scjfc-oc* *scjfc-oc*)
                     (list *scjfc-all* *scjfc-all* 0 1 t t t)))

; 2. The view not live over the catalog: the same owner, its two articles
; oldest first and the trie built from that list.
(defconst *scjfc-view* (fn-own-view (fn-ocfg-owner *scjfc-oc*)))
(defconst *scjfc-arts* (fn-state-articles (fn-own-view-archive *scjfc-view*)))
(defconst *scjfc-reversed*
  (update-nth 2 (fn-ctl-visible-state-of (fn-node-acceptance (fn-sn-node (fn-own-store (fn-ocfg-owner *scjfc-oc*))))
                                         (reverse *scjfc-arts*))
              (update-nth 4 (fn-midx-build (reverse *scjfc-arts*)) *scjfc-view*)))
(defconst *scjfc-oc-rev*
  (fn-ocfg-with-owner *scjfc-oc* (update-nth 1 *scjfc-reversed* (fn-ocfg-owner *scjfc-oc*))))
(assert-event (equal (fn-own-view (fn-ocfg-owner *scjfc-oc-rev*)) *scjfc-reversed*))
(assert-event (equal (fn-state-articles (fn-own-view-archive *scjfc-reversed*)) (reverse *scjfc-arts*)))
; Retained: the record's pin fields are the view's.  Omitted: the view is
; live.  Conclusion: the record is pinned -- false.
(assert-event (equal (nthcdr 4 (scjfc-open-exec *scjfc-oc* *scjfc-oc-rev*))
                     (list t nil nil)))

; -----------------------------------------------------------------------------
; 3. The advance after the host's finish.

(defun scjfc-advance-run (oc payloads fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (rows (fn-sf-records (fn-sn-files s)))
         (fn-cat (fn-sca-load-held-rows (take (- (len rows) 1) rows)
                                        (fn-own-view-index (fn-own-view o)) fn-arena fn-cat))
         (row (fn-sn-completion-record s))
         (w (fn-held-wire-of row fn-arena))
         (pending (fn-cat-prepare-sealed w row nil nil nil fn-arena fn-cat))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (finished (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish o (fn-ocfg-config oc) fn-arena))))
         (fo (fn-ocfg-owner finished))
         (id (fn-own-conn-id (car (fn-own-conns fo))))
         (targets (fn-sca-targets-of (fn-record-msgid row)
                                     (fn-own-view-withdrawals (fn-own-view fo)))))
    (mv-let (word pending2 fn-cat)
      (fn-sca-finish token pending (fn-own-view-index (fn-own-view fo)) targets fn-cat)
      (declare (ignore word pending2))
      (let* ((advanced (fn-ocfg-advance finished id))
             (ao (fn-ocfg-owner advanced)))
        (mv (list (scjfc-invp fo fn-arena fn-cat)
                  (car (fn-own-advance-result fo id))
                  (scjfc-invp ao fn-arena fn-cat)
                  (len (fn-own-conns fo))
                  (fn-own-conn-version (car (fn-own-conns fo)))
                  (fn-own-conn-version (fn-own-find-conn id (fn-own-conns ao)))
                  (fn-own-view-version (fn-own-view fo)))
            fn-arena fn-cat)))))

(defun scjfc-advance-exec (oc payloads)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scjfc-advance-run oc payloads fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event (equal (scjfc-advance-exec *cet-t2-oc* *cet-t2-payloads*)
                     (list *scjfc-all* :advanced *scjfc-all* 2 2 3 3)))
