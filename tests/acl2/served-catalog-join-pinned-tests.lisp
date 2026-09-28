; served-catalog-join-pinned-tests.lisp -- teeth for books/served-catalog-
; join-pinned.lisp (pinned readers across the host's finish; lane sca-join-4,
; sub-lane P, PRF-302 step 3).
;
; Two fixtures:
;
;   A. LIST LEVEL, small concrete catalogs.  Rows are the T2 store's
;      completion row (catalog-entries-tests' *cet-t2-oc*) with the sequence
;      and Message-ID replaced, committed in order over an arena holding
;      their payloads; the pending row is fn-cat-prepare-sealed of one more
;      such row, the token its own, the view index one showing the completed
;      row (so T2 commits it visible), no targets.  For every
;      pinned version V the view fn-scr-view-of V and the view's articles
;      are evaluated before and after fn-sca-finish.
;        1. REACHABLE WITNESS of fn-scj-view-of-of-finish and of the
;           catalog half of fn-scj-catalogp-of-finish (the view articles at
;           the pin and fn-cnx-freshp; its other three conjuncts read no
;           catalog) with fn-scj-seqs-sortedp-of-finish: sequences
;           (0 1 4), completed row 5, every V in 0..5: all hypotheses true,
;           the view and its articles unchanged, the rows still sorted.
;           Non-vacuous: the pins name 0, 1, 2 and 3 rows.
;        2. HYPOTHESIS REMOVAL, sortedness: sequences (0 5 0), completed
;           row 6, V = 1.  Every row's sequence is below 6 and V <= 6
;           (retained, true), the rows are not sorted (omitted, false), and
;           the pinned view moves from 1 row to 3.
;        3. HYPOTHESIS REMOVAL, the bound V <= the completed row's
;           sequence: the sorted catalog of 1 at V = 6: sorted and every
;           row below 5 (retained, true), 6 > 5 (omitted, false), and the
;           view moves from 3 rows to 4 (the new row).
;
;   B. HOST LEVEL, the T2 owner at :completing (two connections pinned at
;      the view's version 2, a history of three rows whose last is the
;      completing article), the catalog the load of the first two rows, the
;      pending the store's row, the owner after the finish
;      fn-ccar-own-finish's, index and targets its view's (as
;      served-catalog-join-finish-tests).
;        4. REACHABLE WITNESS of fn-scj-owner-catalogp-at-host-finish: all
;           twenty-four hypotheses and its five conclusions (the chain
;           premise at both connection identifiers, the pinned connections,
;           the live view, sortedness and freshness) evaluated on live
;           stobjs; and every hypothesis and both conclusions of
;           fn-scj-conns-pinp-at-host-finish (a subset).  Non-vacuous: the
;           catalog after holds the completed row, which both pinned
;           connections (version 2, the row's sequence 2) do not see and the
;           live view (version 3) does.
;
; The defun-nx predicates are evaluated through program-mode twins that
; spell out their bodies over the live stobj (scjp-*), as
; served-catalog-join-finish-tests does.

(in-package "ACL2")

(include-book "catalog-entries-tests")
(include-book "../../books/served-catalog-join-pinned")

(defun scjp-rows-of (i fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (if (< i (fn-cat-count fn-cat))
      (cons (fn-cat-at i fn-cat) (scjp-rows-of (+ 1 i) fn-cat))
    nil))

; fn-scr-catalogp's body.
(defun scjp-catalogp (archive index v fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (and (equal (fn-state-articles archive) (fn-cat-view-articles v fn-arena fn-cat))
       (fn-statep archive)
       (fn-gidx-pin-correspondencep index archive)
       (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles archive))
       (fn-cnx-freshp (scjp-rows-of 0 fn-cat))
       t))

; fn-scr-fields-catalogp's body.
(defun scjp-fields-catalogp (archive index group-index control pinned fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (scjp-catalogp archive
                 (if group-index (fn-gidx-pin-with-control index group-index control) index)
                 (fn-scr-view-of (fn-served-pinned-version pinned) fn-cat)
                 fn-arena fn-cat))

; fn-scr-live-catalogp's body.
(defun scjp-live-catalogp (live fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (scjp-fields-catalogp (fn-served-live-archive live) (fn-served-live-index live)
                        (fn-served-live-buckets live) (fn-served-live-control live)
                        (fn-served-pinned-make (fn-served-live-version live)
                                               (fn-served-live-frontier live) t)
                        fn-arena fn-cat))

; fn-scj-live-okp's body.
(defun scjp-live-okp (view fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (scjp-live-catalogp (fn-own-view-live view) fn-arena fn-cat))

; fn-scj-conn-pinp's body (fn-scj-conn-pinned-index spelled out).
(defun scjp-conn-pinp (conn fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (scjp-catalogp (fn-own-conn-archive conn)
                 (if (fn-own-conn-group-index conn)
                     (fn-gidx-pin-with-control (fn-own-conn-index conn)
                                               (fn-own-conn-group-index conn)
                                               (fn-own-conn-control conn))
                   (fn-own-conn-index conn))
                 (fn-scr-view-of (fn-own-conn-version conn) fn-cat)
                 fn-arena fn-cat))

(defun scjp-conns-pinp (conns fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (if (consp conns)
      (and (scjp-conn-pinp (car conns) fn-arena fn-cat)
           (scjp-conns-pinp (cdr conns) fn-arena fn-cat))
    t))

; fn-scr-owner-catalogp's body (fn-scr-conn-okp and fn-scr-conn-catalogp
; spelled out) at connection ID.
(defun scjp-owner-catalogp (o id fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let ((sc (fn-own-tls-served-conn o conn)))
          (and (scjp-fields-catalogp (fn-served-conn-archive sc) (fn-served-conn-index sc)
                                     (fn-served-conn-group-index sc) (fn-served-conn-control sc)
                                     (fn-served-conn-pinned sc) fn-arena fn-cat)
               (if (fn-served-conn-live sc)
                   (scjp-live-catalogp (fn-served-conn-live sc) fn-arena fn-cat)
                 t)))
      t)))

; fn-scj-joinp's body.
(defun scjp-joinp (view fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let ((c (scjp-rows-of 0 fn-cat)))
    (and (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
                (fn-state-articles (fn-own-view-archive view)))
         (fn-scj-marks-below c (fn-cat-count fn-cat))
         (fn-scj-seqs-below c (fn-own-view-version view))
         t)))

; fn-scj-rows-invp's body.
(defun scjp-rows-invp (c events)
  (declare (xargs :mode :program))
  (equal (fn-scj-arts-map c)
         (fn-scj-arts-map (with-local-stobj fn-cat
                            (mv-let (r fn-cat)
                              (let ((fn-cat (fn-sca-load-held-rows-from events nil fn-cat)))
                                (mv (scjp-rows-of 0 fn-cat) fn-cat))
                              r)))))

; -----------------------------------------------------------------------------
; A. List level.

(defconst *scjp-row0*
  (fn-sn-completion-record (fn-own-store (fn-ocfg-owner *cet-t2-oc*))))

(defun scjp-row (seq i)
  (declare (xargs :mode :program))
  (let ((r *scjp-row0*))
    (fn-held-make seq (fn-record-txid r) (fn-record-generation r)
                  (concatenate 'string "<p" (coerce (explode-atom i 10) 'string) "@example>")
                  i (fn-record-groups r) (fn-record-obligation-id r)
                  (fn-record-content-subject r) (fn-record-release-evidence r)
                  (fn-record-charge r) (fn-record-stamp r)
                  (fn-held-facts r) (fn-held-context r) nil nil)))

(defun scjp-commit-seqs (seqs i fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (if (consp seqs)
      (let ((fn-cat (fn-cat-commit (scjp-row (car seqs) i) fn-cat)))
        (scjp-commit-seqs (cdr seqs) (+ 1 i) fn-cat))
    fn-cat))

;; For each V in VS: the pin fn-scr-view-of V and its articles.
(defun scjp-views-at (vs fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (if (consp vs)
      (let ((k (fn-scr-view-of (car vs) fn-cat)))
        (cons (list k (fn-cat-view-articles k fn-arena fn-cat))
              (scjp-views-at (cdr vs) fn-arena fn-cat)))
    nil))

; (view-of before, view-of after, articles unchanged) per V.
(defun scjp-zip-views (before after)
  (declare (xargs :mode :program))
  (if (consp before)
      (cons (list (car (car before)) (car (car after))
                  (equal (cadr (car before)) (cadr (car after))))
            (scjp-zip-views (cdr before) (cdr after)))
    nil))

; => (list hyps-before per-view after-facts): hyps-before is (sorted,
; every row below the completed row's sequence, fresh); after-facts is
; (sorted, fresh, count).
(defun scjp-list-run (seqs held-seq vs fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((n (len seqs))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many (make-list (+ 1 n) :initial-element *cet-p*) fn-arena))
         (fn-cat (fn-cat-clear fn-cat))
         (fn-cat (scjp-commit-seqs seqs 0 fn-cat))
         (c1 (scjp-rows-of 0 fn-cat))
         (row (scjp-row held-seq n))
         (w (fn-held-wire-of row fn-arena))
         (pending (fn-cat-prepare-sealed w row nil nil nil fn-arena fn-cat))
         (hyps (list (fn-scj-seqs-sortedp c1)
                     (fn-scj-seqs-below c1 (fn-record-sequence (fn-pc-held pending)))
                     (fn-cnx-freshp c1)
                     (fn-pc-p pending)))
         (before (scjp-views-at vs fn-arena fn-cat)))
    (mv-let (word pending2 fn-cat)
      ;; The view index shows the completed row, so T2 commits it visible.
      (fn-sca-finish (fn-pc-token pending) pending
                     (fn-midx-build (list (fn-make-article (fn-record-msgid row) n nil nil t nil)))
                     nil fn-cat)
      (declare (ignore word pending2))
      (let ((c2 (scjp-rows-of 0 fn-cat)))
        (mv (list hyps
                  (scjp-zip-views before (scjp-views-at vs fn-arena fn-cat))
                  (list (fn-scj-seqs-sortedp c2) (fn-cnx-freshp c2) (len c2)))
            fn-arena fn-cat)))))

(defun scjp-list-exec (seqs held-seq vs)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scjp-list-run seqs held-seq vs fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

; 1. Reachable witness: sorted (0 1 4), the completed row 5, every pin V
; at most 5.  The pins show 0, 1, 2, 2, 2 and 3 rows, before and after.
(assert-event (equal (scjp-list-exec '(0 1 4) 5 '(0 1 2 3 4 5))
                     (list (list t t t t)
                           (list (list 0 0 t) (list 1 1 t) (list 2 2 t)
                                 (list 2 2 t) (list 2 2 t) (list 3 3 t))
                           (list t t 4))))

; 2. Sortedness removed: (0 5 0), the completed row 6, V = 1.  Every row is
; below 6 and 1 <= 6; the rows are unsorted; the bisection's pin moves from
; 1 row to 3 and the pinned articles change.
(assert-event (equal (scjp-list-exec '(0 5 0) 6 '(1))
                     (list (list nil t t t)
                           (list (list 1 3 nil))
                           (list nil t 4))))

; 3. The bound removed: the catalog of 1 at V = 6 > 5.  Sorted, every row
; below 5; the pin moves from 3 rows to 4 (it now shows the completed row).
(assert-event (equal (scjp-list-exec '(0 1 4) 5 '(6))
                     (list (list t t t t)
                           (list (list 3 4 nil))
                           (list t t 4))))

; -----------------------------------------------------------------------------
; B. Host level: the T2 owner.

(defun scjp-conn-ids-okp (ids o fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (if (consp ids)
      (and (scjp-owner-catalogp o (car ids) fn-arena fn-cat)
           (scjp-conn-ids-okp (cdr ids) o fn-arena fn-cat))
    t))

(defun scjp-host-run (oc payloads ncat fn-arena fn-cat)
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
         (row (fn-sn-completion-record s))
         (w (fn-held-wire-of row fn-arena))
         (pending (fn-cat-prepare-sealed w row nil nil nil fn-arena fn-cat))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (o2 (cdr (fn-ccar-own-finish o (fn-ocfg-config oc) fn-arena)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (a (car (fn-state-articles acc2)))
         (verdict (cdr (car (fn-sn-verdicts s2))))
         (c0 (scjp-rows-of 0 fn-cat))
         (hyps (list (if (fn-ccar-completion-enabledp s) t nil)
                     (scjp-joinp view fn-arena fn-cat)
                     (fn-scar-view-indexedp o)
                     (scjp-rows-invp c0 events0)
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
                     (<= (nfix (fn-own-view-version view)) (len events0))
                     ;; step 3
                     (fn-scj-seqs-sortedp c0)
                     (fn-cnx-freshp c0)
                     (scjp-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                     (fn-scj-conns-versions-atmostp (fn-own-conns o) (fn-own-view-version view))
                     (fn-own-view-okp view2 (fn-sn-groups s2) (fn-sn-capacity s2)
                                      (fn-sf-records (fn-sn-files s2)))
                     (if (fn-statep (fn-own-view-archive view2)) t nil))))
    (mv-let (word pending2 fn-cat)
      (fn-sca-finish token pending (fn-own-view-index view2)
                     (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                        (fn-own-view-withdrawals view2))
                     fn-cat)
      (declare (ignore word pending2))
      (let ((c2 (scjp-rows-of 0 fn-cat)))
        (mv (list hyps
                  (list (scjp-conn-ids-okp (strip-cars (fn-own-conns o2)) o2 fn-arena fn-cat)
                        (scjp-conns-pinp (fn-own-conns o2) fn-arena fn-cat)
                        (scjp-live-okp view2 fn-arena fn-cat)
                        (fn-scj-seqs-sortedp c2)
                        (fn-cnx-freshp c2))
                  ;; non-vacuity: two connections pinned at 2, the live view
                  ;; at 3; the catalog holds one row (sequence 2), which the
                  ;; pins do not show and the live view does.
                  (list (strip-cars (fn-own-conns o2))
                        (fn-own-conn-version (car (fn-own-conns o2)))
                        (fn-own-conn-version (cadr (fn-own-conns o2)))
                        (fn-own-view-version view2)
                        (len c2)
                        (fn-record-sequence (car c2))
                        (len (fn-cat-view-articles (fn-scr-view-of 2 fn-cat) fn-arena fn-cat))
                        (len (fn-cat-view-articles (fn-scr-view-of (fn-own-view-version view2) fn-cat)
                                                   fn-arena fn-cat))))
            fn-arena fn-cat)))))

(defun scjp-host-exec (oc payloads ncat)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scjp-host-run oc payloads ncat fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

; 4. Reachable witness of fn-scj-owner-catalogp-at-host-finish (all 24
; hypotheses, all five conclusions); fn-scj-conns-pinp-at-host-finish's ten
; hypotheses are among them (2, 5, 7, 8, 10, 11, 18, 19, 21 and 22 of the
; list) and its two conclusions are the second and fourth.
(assert-event (equal (scjp-host-exec *cet-t2-oc* *cet-t2-payloads* 2)
                     (list (make-list 24 :initial-element t)
                           (list t t t t t)
                           (list '(1 0) 2 2 3 1 2 0 1))))
