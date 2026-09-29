; served-catalog-join-host-tests.lisp -- executable-twin teeth for the host
; protocol's carried predicate fn-sjh-okp (books/served-catalog-join-host.lisp)
; and its finish keystones (lane join-f2-2, 2026-09-29; PRF-302).
;
; fn-sjh-okp is fn-scj-invp, six carried side facts, S and LINK.  Its store
; side (S and LINK) is evaluated through its proved twin
; fn-sjh-files-okp-exec (books/served-catalog-join-host-exec.lisp,
; fn-sjh-files-okp-exec-is-files-okp); fn-scj-invp's five conjuncts through
; served-catalog-join-inv-tests' scji-parts; the side facts' bodies directly.
;
; The state is the one the host holds between its catalog prepare and its
; finish: catalog-entries-tests' T2 owner (one POST run through the owner's
; steps to :completing, its history two retention rows and the completing
; article row), the catalog the host's load of the rows before the completing
; one, the pending row fn-cat-prepare-sealed of the completing row (the host's
; fn-owner-cat-prepare-sealed), over an arena holding the payloads.
;
;   1. REACHABLE WITNESS of fn-sjh-okp-at-owner-finish-identity at an article
;      row (the branch fn-sjh-idf-okp-with-row takes through
;      fn-sjh-idf-article-premises-of-okp): every antecedent (the owner
;      relation, every conjunct of fn-sjh-okp with the host's pending row,
;      the host's own :durable -- :completing before, :ready after), and the
;      conclusion (no pending row left; every conjunct of fn-sjh-okp at the
;      finished owner over the catalog fn-sca-finish leaves; the owner
;      relation after, Q3c's).  NOT witnessed here: fn-own-finish's own
;      :durable (fn-sjh-okp-at-host-article-finish's antecedent) -- this
;      owner's in-flight slot names no submission, so its word is :fault.
;   2. HYPOTHESIS REMOVAL (fn-sjh-okp's LINK, the conjunct the finish turns
;      on): the same owner with a pending row expecting one more catalog row
;      than the catalog holds -- every other conjunct of fn-sjh-okp holds,
;      LINK fails, and the conclusion fails (the catalog refuses the
;      completion: a pending row is left, the catalog does not grow).
;   3. HYPOTHESIS REMOVAL (LINK's no-row arm): no pending row at a
;      completing article row -- LINK fails; the host's finish then runs no
;      catalog step, and the finished owner is not joined with the catalog
;      (fn-scj-invp's join fails: the view shows the article, the catalog
;      does not).
;   4. REACHABLE WITNESS of fn-sjh-idf-finish-equations (the signed
;      composite's acceptance and verdict equations, the identity finish's
;      (I)): owner-signed-post-tests' store at :completing with its retained
;      composite row, over an arena holding the composite article's payload:
;      every hypothesis and both equations.
;   5. CORRUPTED STATE (labelled; not reachable: the intern builds the held
;      row from the composite's own record): the composite row with a held
;      row of another Message-ID -- the node and identity steps still
;      succeed, the composite fact fails, and the Message-ID the node
;      installs is not the one the verdict names (the verdict equation's
;      pair).

(in-package "ACL2")

(include-book "served-catalog-join-inv-tests")
(include-book "owner-signed-post-tests")
(include-book "../../books/served-catalog-join-host-exec")
(include-book "../../books/served-catalog-join-host-identity-finish")

; Every conjunct of fn-sjh-okp at owner O with pending row PENDING, over the
; live catalog.
(defun sjht-okp-parts (o pending fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((view (fn-own-view o))
         (s (fn-own-store o))
         (files (fn-sn-files s))
         (v (fn-own-view-version view))
         (records (fn-sf-records files))
         (seen (if (equal (fn-sf-phase files) :completing) (butlast records 1) records))
         (c (scji-rows-of 0 fn-cat)))
    (list (scji-parts o fn-arena fn-cat)
          (list (and (<= v (len seen)) (fn-scj-no-rowsp (nthcdr v seen)))    ; fn-scjs-seenp
                (and (natp v) (<= v (len records)) (true-listp records))     ; fn-scjs-historyp
                (fn-scar-view-indexedp o)
                (fn-scj-seqs-sortedp c)
                (fn-cnx-freshp c)
                (fn-scj-conns-versions-atmostp (fn-own-conns o) v))           ; fn-scj-versions-okp
          (fn-sjh-files-okp-exec files pending fn-arena fn-cat))))

(defconst *sjht-okp* (list (list t t t t t) (list t t t t t t) t))

(defun sjht-strip (parts)
  ; scji-parts ends with the live view's view-of; the teeth compare it apart.
  (declare (xargs :mode :program))
  (list (take 5 (car parts)) (cadr parts) (caddr parts)))

;; MODE: nil the host's pending; (:expected E) a pending made directly with
;; expected E; :none no pending row.
(defun sjht-run (oc payloads mode fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (rows (fn-sf-records (fn-sn-files s)))
         (fn-cat (fn-sca-load-held-rows (butlast rows 1) (fn-own-view-index (fn-own-view o))
                                        fn-arena fn-cat))
         (row (fn-sn-completion-record s))
         (w (fn-held-wire-of row fn-arena))
         (pending (cond ((eq mode :none) nil)
                        ((and (consp mode) (eq (car mode) :expected))
                         (fn-pc-make (cons (nfix (fn-record-txid row)) (cadr mode)) (cadr mode)
                                     row nil nil))
                        (t (fn-cat-prepare-sealed w row nil nil nil fn-arena fn-cat))))
         (before (sjht-strip (sjht-okp-parts o pending fn-arena fn-cat)))
         (res (fn-ccar-own-finish o (fn-ocfg-config oc) fn-arena))
         (o2 (cdr res))
         (view2 (fn-own-view o2))
         (count0 (fn-cat-count fn-cat))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (antecedent (list (fn-ocl-relation oc) (equal before *sjht-okp*)
                          ; the host's :durable (fn-owner-finish-synced)
                          (and (equal (fn-sf-phase (fn-sn-files s)) :completing)
                               (equal (fn-sf-phase (fn-sn-files (fn-own-store o2))) :ready)))))
    (if (null pending)
        ; the host runs no catalog step without a pending row
        (mv (list antecedent before
                  (list nil (sjht-strip (sjht-okp-parts o2 nil fn-arena fn-cat)) count0
                        (fn-ocl-relation (fn-ocfg-with-owner oc o2))))
            fn-arena fn-cat)
      (mv-let (word pending2 fn-cat)
        (fn-sca-finish token pending (fn-own-view-index view2)
                       (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                          (fn-own-view-withdrawals view2))
                       fn-cat)
        (declare (ignore word))
        (mv (list antecedent before
                  (list (if pending2 :pending-left nil)
                        (sjht-strip (sjht-okp-parts o2 pending2 fn-arena fn-cat))
                        (fn-cat-count fn-cat)
                        (fn-ocl-relation (fn-ocfg-with-owner oc o2))))
            fn-arena fn-cat)))))

(defun sjht-exec (oc payloads mode)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (sjht-run oc payloads mode fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

; -----------------------------------------------------------------------------
; 1. fn-sjh-okp-at-owner-finish-identity's article branch, reachable: the
; antecedent (the owner relation, fn-sjh-okp with the host's pending row, the
; host's :durable), and the conclusion: no pending row left, fn-sjh-okp at the
; finished owner with none (the catalog grown to the history's one article),
; the relation after.

(assert-event (equal (sjht-exec *cet-t2-oc* *cet-t2-payloads* nil)
                     (list (list t t t)
                           *sjht-okp*
                           (list nil *sjht-okp* 1 t))))

; -----------------------------------------------------------------------------
; 2. LINK removed: a pending row expecting one more row than the catalog
; holds.  Every other conjunct holds; the store side fails; the catalog
; refuses the completion -- a pending row is left and the catalog does not
; grow, so the finished owner's view is not joined with it.

(assert-event (equal (sjht-exec *cet-t2-oc* *cet-t2-payloads* '(:expected 1))
                     (list (list t nil t)
                           (list (list t t t t t) (list t t t t t t) nil)
                           (list :pending-left
                                 (list (list nil nil t nil t) (list t t t t t t) nil)
                                 0 t))))

; -----------------------------------------------------------------------------
; 3. LINK's no-row arm removed: no pending row at the completing article row.
; The host's finish runs no catalog step; the finished owner's view shows the
; article the catalog lacks.

(assert-event (equal (sjht-exec *cet-t2-oc* *cet-t2-payloads* :none)
                     (list (list t nil t)
                           (list (list t t t t t) (list t t t t t t) nil)
                           (list nil
                                 (list (list nil nil t nil t) (list t t t t t t) t)
                                 0 t))))

; -----------------------------------------------------------------------------
; 4. The identity finish's (I) equations, reachable: owner-signed-post-tests'
; store at :completing, its completion record the retained composite row.

(defconst *sjht-id-store* (fn-own-store *ospt-completing*))
(defconst *sjht-id-row* (fn-ccar-completion-record *sjht-id-store*))
(make-event
 `(defconst *sjht-id-payloads*
    ',(list (fn-record-payload (fn-replay-composite-record (fn-hstxa-stxa *sjht-id-row*))))))

(defun sjht-id-run (s payloads fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (r (fn-ccar-completion-record s))
         (s2 (fn-ccar-sn-finish s))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (a (car (fn-state-articles acc2))))
    (mv (list (list (if (fn-ccar-completion-enabledp s) t nil)
                    (if (fn-evc-stxap r) t nil)
                    (if (fn-row-composite-okp r fn-arena) t nil))
              (list (equal (fn-state-articles acc2)
                           (cons a (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
                    (equal (fn-sn-verdicts s2)
                           (cons (cons (fn-article-msgid a) (cdr (car (fn-sn-verdicts s2))))
                                 (fn-sn-verdicts s)))
                    (len (fn-state-articles acc2))))
        fn-arena)))

(defun sjht-id-exec (s payloads)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (sjht-id-run s payloads fn-arena)
      result)))

(assert-event (fn-hstxa-p *sjht-id-row*))
(assert-event (equal (sjht-id-exec *sjht-id-store* *sjht-id-payloads*)
                     (list (list t t t)
                           (list t t (+ 1 (len (fn-state-articles
                                                (fn-node-acceptance (fn-sn-node *sjht-id-store*)))))))))

; -----------------------------------------------------------------------------
;; 5. CORRUPTED STATE: the composite row holding a held row of another
; Message-ID (the intern never builds it: fn-intern-event interns the
; composite's own record).  The node step and the identity step the finish
; takes (fn-sjh-idf-node-of-finish, fn-sjh-idf-verdicts-of-finish) both still
; succeed on it, but the composite fact fails and the article the node
; installs is not the one the verdict names.

(make-event
 `(defconst *sjht-id-rec* ',(fn-replay-composite-record (fn-hstxa-stxa *sjht-id-row*))))
(make-event
 `(defconst *sjht-id-bad-row*
    ',(let ((r *sjht-id-rec*))
        (fn-hstxa-make (fn-hstxa-stxa *sjht-id-row*)
                       (fn-held-plain
                        (fn-record-make (fn-record-sequence r) (fn-record-txid r)
                                        (fn-record-generation r) "<other@example.invalid>"
                                        (fn-record-payload r) (fn-record-groups r)
                                        (fn-record-obligation-id r) (fn-record-content-subject r)
                                        (fn-record-release-evidence r) (fn-record-charge r)
                                        (fn-record-stamp r))
                        0)))))

(defun sjht-id-step-run (s row payloads fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (node2 (fn-replay-apply-record (fn-sn-node s) row))
         (ctx (fn-replay-identity-step (fn-sn-identity-context s) row))
         (a (car (fn-state-articles (fn-node-acceptance node2))))
         (pair (car (fn-replay-verdict-pairs (fn-stxk-context-verdicts ctx)))))
    (mv (list (if (consp node2) t nil)
              (fn-stxk-context-kind ctx)
              (if (fn-row-composite-okp row fn-arena) t nil)
              (equal (fn-article-msgid a) (car pair)))
        fn-arena)))

(defun sjht-id-step-exec (s row payloads)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (sjht-id-step-run s row payloads fn-arena)
      result)))

; The row the store holds: both steps succeed, the fact holds, the Message-IDs agree.
(assert-event (equal (sjht-id-step-exec *sjht-id-store* *sjht-id-row* *sjht-id-payloads*)
                     (list t :ok t t)))
; The corrupted row: both steps succeed, the fact fails, the Message-IDs differ.
(assert-event (equal (sjht-id-step-exec *sjht-id-store* *sjht-id-bad-row* *sjht-id-payloads*)
                     (list t :ok nil nil)))
