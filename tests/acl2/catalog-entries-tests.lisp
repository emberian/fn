; fn: teeth for books/catalog-entries.lisp (wave 5, lane catalog-boundary-owner,
; 2026-09-26).
;
; What this book is evidence FOR (restated over the flipped store by lane
; catalog-columns, 2026-09-27; the relation reads ALPHA of the store's rows,
; books/store-intern.lisp fn-rows-wire-of, and the entries are the host's):
;
; books/served-catalog-owner.lisp fn-sca-ocl-relation-at-full-open (E1/E2):
; the host's full open on live stobjs -- the arena cleared, the one-article
; journal interned, the owner installed over the rows, the catalog loaded by
; fn-sca-load-held-rows -- with every hypothesis and conclusion conjunct
; evaluated (the catalog holds the article); removal witnesses for (true-listp
; ws) and (not :fault); the :bad check labelled (no witness constructible).
; fn-sca-ocl-relation-at-recover (E3, any prefix/suffix split): the two
; splits install the same owner at an idle store holding the rows; removal
; witnesses for fn-rows-handles-inp and fn-arena-p (evaluated) and for
; fn-wire-event-listp (symbolic: its only falsifier under the others is a
; payload over *fn-record-max-payload* octets).
; fn-sca-ocl-relation-of-finish (T2 at fn-owner-finish-submission): a
; configured owner at :completing (owner-advance-carried-tests' recipe)
; over an arena holding its payloads, the host's catalog, pending, token and
; targets: every hypothesis and conclusion conjunct evaluated; removal
; witnesses for the token, the expected count, the catalog's relation, the
; articles equation and the handle; fn-ocl-relation and the completion gate
; only jointly (the node-replaced owner closes the gate too); fn-pc-p and
; fn-record-p of W labelled below.
; fn-cat-load-of-append: loading the prefix then the suffix on live stobjs
; materializes the same rows as loading the history.
; The model-level T2 (fn-cat-ocl-relation-of-article-finish, over
; fn-cat-complete) on owner-tests' recipe: the store side evaluated, the
; catalog side on the logical side with the stale-token and
; mismatched-expected witnesses.

(in-package "ACL2")
(include-book "../../books/catalog-entries")
(include-book "../../books/served-catalog-owner")   ; the host's E load over rows; store-intern
(include-book "../../books/crypto-attach")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-advance-carried-tests")   ; T2: a configured owner at :completing

(assert-event
 (and (eq (symbol-class 'fn-cat-history-prefix-relation (w state)) :ideal)
      (eq (symbol-class 'fn-cat-load (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ocl-relation (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; E2 and E3: a one-article history under the default configuration, opened
; :ok as the full replay (prefix nil) and as a checkpoint (prefix the article,
; suffix nil).

(defun cet-record (sequence txid msgid)
  (fn-record-make sequence txid txid msgid
                  (list 77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10
                        72 105 13 10)
                  '("fn.letters")
                  (concatenate 'string "own-pin:" msgid)
                  (concatenate 'string "own-content:" msgid)
                  (concatenate 'string "own-release:" msgid)
                  2 841000000))

(defconst *cet-configs* (list *fn-cfg-default-record*))
(defconst *cet-w0* (cet-record 0 0 "<one@example>"))
(defconst *cet-h* (list *cet-w0*))
;; The arena's payloads (handle 0: the article's bytes).
(defconst *cet-payloads* (list (fn-record-payload *cet-w0*)))

;; The wire history interned as the owner's recovery interns it (keyring nil,
;; generation 0, a fresh arena): the ROWS the store's history holds.
(defun cet-rows (ws)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (fn-intern-events ws nil 0 fn-arena)
      rows)))

;; ALPHA: the wire events ROWS stand for over the arena holding PAYLOADS.
(defun cet-wires (payloads rows)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let ((fn-arena (fn-arn-seal-many payloads fn-arena)))
        (mv (fn-rows-wire-of rows fn-arena) fn-arena))
      r)))

(defconst *cet-hr* (cet-rows *cet-h*))
(defconst *cet-r0* (car *cet-hr*))
(assert-event (and (equal (len *cet-hr*) 1)
                   (fn-held-p *cet-r0*)
                   (equal (fn-record-payload *cet-r0*) 0)
                   (equal *cet-r0* (fn-intern-row-at *cet-w0* nil 0 0))
                   (equal (cet-wires *cet-payloads* *cet-hr*) *cet-h*)))

(defconst *cet-full*
  (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture *cet-configs* nil) *cet-configs* *cet-hr*)
                           *cet-configs* 8 4))
(defconst *cet-ckpt*
  (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture *cet-configs* *cet-hr*) *cet-configs* nil)
                           *cet-configs* 8 4))

; The owner's conjuncts of the conclusion, on both entries.
(assert-event (and (not (equal *cet-full* :fault)) (not (equal *cet-ckpt* :fault))))
(assert-event (and (fn-ocl-relation *cet-full*) (fn-ocl-relation *cet-ckpt*)))
(assert-event (and (fn-own-store-idlep (fn-own-store (fn-ocfg-owner *cet-full*)))
                   (fn-own-store-idlep (fn-own-store (fn-ocfg-owner *cet-ckpt*)))))
(assert-event (and (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner *cet-full*)))) *cet-hr*)
                   (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner *cet-ckpt*)))) *cet-hr*)))
(assert-event (equal *cet-full* *cet-ckpt*))
;; The octet history is refused: the flipped store takes rows only.
(assert-event (equal (fn-ock-recover-extended
                      (fn-sco-extend (fn-sco-capture *cet-configs* nil) *cet-configs* *cet-h*)
                      *cet-configs* 8 4)
                     :fault))

;; The host's catalog at recovery: fn-sca-load-held-rows over the recovered
;; store's rows under its view index, over the arena holding the payload.
;; R holds over ALPHA of the rows (the keystone's hypotheses asserted too),
;; the one row materializes to the wire record, and it is visible at the
;; owner's view version.
(defun cet-held-run (records view fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many *cet-payloads* fn-arena))
         (fn-cat (fn-sca-load-held-rows records (fn-own-view-index view) fn-arena fn-cat)))
    (mv (list (fn-cat-count fn-cat)
              (and (fn-arena-p fn-arena) (fn-sf-record-valuesp records)
                   (fn-rows-handles-inp records fn-arena)
                   (fn-wire-event-listp (fn-rows-wire-of records fn-arena)) t)
              (fn-cat-history-relation (fn-rows-wire-of records fn-arena) fn-arena fn-cat)
              (fn-cat-wire-list 0 fn-arena fn-cat)
              (fn-scr-view-of (fn-own-view-version view) fn-cat))
        fn-arena fn-cat)))

(defun cet-held-exec (records view)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (cet-held-run records view fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(defconst *cet-own* (fn-ocfg-owner *cet-full*))
(assert-event (equal (cet-held-exec (fn-sf-records (fn-sn-files (fn-own-store *cet-own*)))
                                    (fn-own-view *cet-own*))
                     (list 1 t t *cet-h* 1)))

;; Why R reads ALPHA of the rows (the vacuity catalog-columns removed): a
;; held row is never fn-record-p, so fn-sf-article-records of the raw rows
;; is empty, while ALPHA of the rows reads the one article.
(assert-event (and (not (fn-record-p *cet-r0*))
                   (equal (fn-sf-article-records *cet-hr*) nil)
                   (equal (fn-sf-article-records (cet-wires *cet-payloads* *cet-hr*)) *cet-h*)))

; The catalog's conjunct: the exec fold over the same history, on live
; stobjs, and the load in two parts (fn-cat-load-of-append).
(defun cet-run (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load *cet-h* nil 0 fn-arena fn-cat)
      (let ((whole (list (fn-cat-count fn-cat)
                         (fn-cat-history-relation *cet-h* fn-arena fn-cat)
                         (fn-cat-wire-list 0 fn-arena fn-cat))))
        (let* ((fn-arena (fn-arena-clear fn-arena))
               (fn-cat (fn-cat-clear fn-cat)))
          (mv-let (fn-arena fn-cat)
            (fn-cat-load *cet-h* nil 0 fn-arena fn-cat)
            (mv-let (fn-arena fn-cat)
              (fn-cat-load nil nil 0 fn-arena fn-cat)
              (mv (list whole (fn-cat-wire-list 0 fn-arena fn-cat)) fn-arena fn-cat))))))))

(defun cet-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (cet-run fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event (equal (cet-exec)
                     (list (list 1 t *cet-h*) *cet-h*)))

; Hypothesis removal: the host refuses the install (connection bound not
; natural): :fault, and :fault is in no relation.
(assert-event (equal (fn-ock-recover-extended
                      (fn-sco-extend (fn-sco-capture *cet-configs* nil) *cet-configs* *cet-h*)
                      *cet-configs* 8 nil)
                     :fault))
(assert-event (not (fn-ocl-relation :fault)))

; Hypothesis removal: a generation that is not natural.  The interned row's
; context fails fn-hc-p, the catalog fails fn-cat-p, the relation is false;
; with a natural generation it holds (the logical side, by evaluation: a
; stobj creator's value is nil).
(defthm cet-w-generation-needed
  (and (mv-let (a c)
         (fn-cat-load *cet-h* nil 0 nil nil)
         (fn-cat-history-relation *cet-h* a c))
       (not (natp -1))
       (mv-let (a c)
         (fn-cat-load *cet-h* nil -1 nil nil)
         (not (fn-cat-history-relation *cet-h* a c))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; E at the host's entries over the flipped store (catalog-columns,
; 2026-09-27): books/served-catalog-owner.lisp fn-sca-ocl-relation-at-full-open
; and fn-sca-ocl-relation-at-recover, over the catalog the host loads
; (fn-sca-load-held-rows).  fn-cat-ocl-relation is non-executable
; (defun-nx); its conjuncts at an idle store are evaluated: the owner's live
; relation, the idle phase, and R over ALPHA of the store's rows.

;; The host's full open, on live stobjs: the arena cleared, the decoded
;; journal WS interned (keyring nil, generation 0), the owner installed over
;; the rows, the catalog loaded from the installed store's rows.
(defun cet-open-run (ws max-conns fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let ((fn-arena (fn-arena-clear fn-arena)))
    (mv-let (rows fn-arena)
      (fn-intern-events ws nil 0 fn-arena)
      (if (equal rows :bad)
          (mv :bad fn-arena fn-cat)
        (let ((oc (fn-ock-recover-extended
                   (fn-sco-extend (fn-sco-capture *cet-configs* nil) *cet-configs* rows)
                   *cet-configs* 8 max-conns)))
          (if (equal oc :fault)
              (mv :fault fn-arena fn-cat)
            (let* ((s (fn-own-store (fn-ocfg-owner oc)))
                   (srows (fn-sf-records (fn-sn-files s)))
                   (fn-cat (fn-sca-load-held-rows
                            srows (fn-own-view-index (fn-own-view (fn-ocfg-owner oc)))
                            fn-arena fn-cat)))
              (mv (list (equal (fn-rows-wire-of srows fn-arena) ws)
                        (fn-ocl-relation oc)
                        (if (fn-own-store-idlep s) t nil)
                        (fn-cat-history-relation (fn-rows-wire-of srows fn-arena) fn-arena fn-cat)
                        (fn-cat-count fn-cat)
                        (fn-cat-wire-list 0 fn-arena fn-cat))
                  fn-arena fn-cat))))))))

(defun cet-open-exec (ws max-conns)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (cet-open-run ws max-conns fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

; fn-sca-ocl-relation-at-full-open, reachable positive witness (non-vacuous:
; the catalog holds the one article, materialized to the journal's record):
; every hypothesis (WS a true list, the intern not :bad, the install not
; :fault) and every conjunct of the conclusion.
(assert-event (true-listp *cet-h*))
(assert-event (not (equal (cet-rows *cet-h*) :bad)))
(assert-event (equal (cet-open-exec *cet-h* 4) (list t t t t 1 *cet-h*)))
; Hypothesis removal, (true-listp ws): a journal with an improper tail.  The
; intern stops at the tail (not :bad), the install is not :fault, R holds,
; and the conclusion's first conjunct fails: the store's history is not WS.
(defconst *cet-improper* (cons *cet-w0* 'tail))
(assert-event (not (true-listp *cet-improper*)))
(assert-event (not (equal (cet-rows *cet-improper*) :bad)))
(assert-event (equal (cet-open-exec *cet-improper* 4) (list nil t t t 1 *cet-h*)))
; Hypothesis removal, (not (equal oc :fault)): the host refuses the install
; (connection bound not natural); the intern and WS hold, and :fault is in
; no relation (fn-cat-ocl-relation's first conjunct).
(assert-event (equal (cet-open-exec *cet-h* nil) :fault))
(assert-event (not (fn-ocl-relation :fault)))
; (not (equal rows :bad)) is the host's own check before the install; no
; removal witness is constructible here: every refused intern tried makes the
; install :fault (the retained hypothesis fails too), and the weakened
; theorem is NOT proved (a failed proof search is not a counterexample).
(assert-event (equal (cet-open-exec (list *cet-w0* 17) 4) :bad))
(assert-event (equal (fn-ock-recover-extended
                      (fn-sco-extend (fn-sco-capture *cet-configs* nil) *cet-configs* :bad)
                      *cet-configs* 8 4)
                     :fault))

; fn-sca-ocl-relation-at-recover, the checkpoint split (prefix the rows,
; suffix nil) and the full split: the installed store holds exactly the rows
; at an idle store (asserted above: *cet-full*, *cet-ckpt*), and over the
; arena holding the payload the three row hypotheses and R hold
; (cet-held-exec above: (1 t t ...) -- its second element is the conjunction
; of fn-arena-p, the rows' values, the handles and the wire events).
; Hypothesis removal (logical side: the arena is its list of payloads):
;  (fn-rows-handles-inp): the empty arena.  The arena is one, ALPHA of the
;  row is a wire record (its payload read as no octets), the handle is
;  outside, and R fails (its handle conjunct).
;  (fn-arena-p): a second, unreferenced payload that is no octet list.  The
;  handle is inside, ALPHA of the row is the record, and R fails (its arena
;  conjunct).
(defthm cet-w-at-recover-handles-and-arena-needed
  (let* ((own (fn-ocfg-owner *cet-ckpt*))
         (rows (fn-sf-records (fn-sn-files (fn-own-store own))))
         (idx (fn-own-view-index (fn-own-view own)))
         (bad-arena (list (fn-record-payload *cet-w0*) 'not-octets)))
    (and (equal rows (append *cet-hr* nil))
         (fn-arena-p nil)
         (fn-wire-event-listp (fn-rows-wire-of rows nil))
         (not (fn-rows-handles-inp rows nil))
         (not (fn-cat-history-relation (fn-rows-wire-of rows nil) nil
                                       (fn-sca-load-held-rows rows idx nil nil)))
         (fn-rows-handles-inp rows bad-arena)
         (equal (fn-rows-wire-of rows bad-arena) *cet-h*)
         (fn-wire-event-listp (fn-rows-wire-of rows bad-arena))
         (not (fn-arena-p bad-arena))
         (not (fn-cat-history-relation (fn-rows-wire-of rows bad-arena) bad-arena
                                       (fn-sca-load-held-rows rows idx bad-arena nil)))))
  :rule-classes nil)

;  (fn-wire-event-listp (fn-rows-wire-of ...)): with the arena an arena and
;  the handle inside, ALPHA of a held row fails to be a wire record only when
;  its payload exceeds *fn-record-max-payload* (4,261,412,864 octets), too
;  long to evaluate; the witness is symbolic over any such payload P: the
;  retained hypotheses hold, the removed one fails, and R fails (the catalog
;  commits the row, the history's articles are empty).
(defthm cet-w-at-recover-wire-events-needed
  (let* ((own (fn-ocfg-owner *cet-ckpt*))
         (rows (fn-sf-records (fn-sn-files (fn-own-store own))))
         (idx (fn-own-view-index (fn-own-view own))))
    (implies (and (fn-cbor-octet-listp p) (< *fn-record-max-payload* (len p)))
             (and (fn-arena-p (list p))
                  (fn-rows-handles-inp rows (list p))
                  (not (fn-wire-event-listp (fn-rows-wire-of rows (list p))))
                  (not (fn-cat-history-relation (fn-rows-wire-of rows (list p)) (list p)
                                                (fn-sca-load-held-rows rows idx (list p) nil))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rows-wire-of fn-row-wire-of fn-row-bytes fn-held-wire
                                     fn-rows-handles-inp fn-row-handle-inp fn-wire-event-listp
                                     fn-wire-event-p fn-record-p fn-record-payloadp
                                     fn-cat-history-relation fn-sf-article-records
                                     fn-record-shapep fn-store-retention-event-p
                                     fn-stxe-p fn-stxe-shapep fn-stxk-p fn-stxk-shapep
                                     fn-stxa-p fn-stxa-shapep fn-cpe-eventp
                                     fn-th-topic-eventp fn-th-local-admin-eventp
                                     fn-record-internals fn-store-event-nth
                                     fn-arena-p-is-payload-listp fn-arn-payload-listp))))

; -----------------------------------------------------------------------------
; T2: the article completion.  owner-tests' recipe: the model owner, one
; reader, a CLI connection posting one article up to :completing.

(defconst *cet-groups* '("fn.letters" "fn.test"))

(defun cet-post-events (record)
  (list '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare record))
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))
        '(:complete)))

(defconst *cet-0* (fn-own-start (fn-sn-initial *cet-groups* 10) 4))
(defconst *cet-a* (cdr (fn-own-open *cet-0* nil)))
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: the article's bytes at
;; handle 0, as after the host's seal of the POST (the store prepares the
;; ROW, fn-intern-row-at at the arena's count before the seal).
(defconst *cet-sr-arena* *cet-payloads*)
(bpr-lift fn-own-run 2)
(bpr-lift fn-own-step 2)
(defconst *cet-begun* (in-arena-fn-own-step *cet-sr-arena* (in-arena-fn-own-step *cet-sr-arena* *cet-a* '(:open)) '(:begin 1)))
(defconst *cet-completing* (in-arena-fn-own-run *cet-sr-arena* *cet-begun* (butlast (cet-post-events *cet-r0*) 1)))
(defconst *cet-s* (fn-own-store *cet-completing*))
(defconst *cet-records* (fn-sf-records (fn-sn-files *cet-s*)))

; The store-side antecedent: :completing with the article's row the newest
; (and only) article of the history, alpha of it the wire record; the
; (empty) catalog covers all before it.
(assert-event (fn-sn-completion-enabledp *cet-s*))
(assert-event (equal (fn-sn-completion-record *cet-s*) *cet-r0*))
(assert-event (equal (cet-wires *cet-payloads* (list (fn-sn-completion-record *cet-s*)))
                     (list *cet-w0*)))
(assert-event (equal (fn-sf-article-records (cet-wires *cet-payloads* *cet-records*))
                     (append (fn-sf-article-records nil) (list *cet-w0*))))
(assert-event (fn-record-p *cet-w0*))
;; The octet record's prepare is refused: the store stays short of :completing.
(assert-event (not (fn-sn-completion-enabledp
                    (fn-own-store (in-arena-fn-own-run *cet-sr-arena* *cet-begun*
                                                       (butlast (cet-post-events *cet-w0*) 1))))))
;; (as above) the raw rows read no article; ALPHA of them the one.
(assert-event (equal (fn-sf-article-records *cet-records*) nil))

; The store-side conclusion: the host's finish keeps the records and leaves
; the store idle.
; (the owner the host installs: fn-ccar-own-finish-installs-ccar-own-complete-by-definition)
(defconst *cet-finished* (fn-ccar-own-complete *cet-completing*))
(assert-event (equal (fn-sf-records (fn-sn-files (fn-own-store *cet-finished*))) *cet-records*))
(assert-event (fn-own-store-idlep (fn-own-store *cet-finished*)))
(assert-event (equal (fn-own-view-version (fn-own-view *cet-finished*)) 1))

; The catalog side, on the logical side: the pending PreparedCommit the POST
; stages (fn-cat-prepare-sealed over the row the store prepared, after the
; seal), completed by its token at expected 0, materializes the history's
; articles (ALPHA of the store's rows); a stale token or a mismatched
; expected leaves the catalog behind the history (the equality fails; the
; prefix form still holds: the state before T2).
; (The intern takes the arena stobj, so the held record and its arena are
; built on the logical side, inside the theorem.)
(defthm cet-w-article-finish-catalog-side
  (mv-let (held arena)
    (fn-cat-intern-list *cet-w0* nil 0 nil)
    (let ((pending (fn-cat-prepare-sealed *cet-w0* (fn-sn-completion-record *cet-s*)
                                          nil nil nil arena nil))
          (history (fn-rows-wire-of *cet-records* arena)))
      (and (equal held (fn-sn-completion-record *cet-s*))
           (equal pending (fn-pc-make (cons 0 0) 0 held nil nil))
           (fn-cat-history-relation nil arena nil)
           (fn-pc-p pending)
           (equal (fn-pc-expected pending) (fn-cat-count nil))
           (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count arena))
           (equal (fn-held-wire-of (fn-pc-held pending) arena) *cet-w0*)
           (fn-cat-history-relation history arena
                                    (mv-nth 2 (fn-cat-complete (fn-pc-token pending) pending nil)))
           ; stale token: refused, the catalog stays behind the history (the
           ; prefix form, the state before T2, still holds)
           (not (fn-cat-history-relation history arena
                                         (mv-nth 2 (fn-cat-complete (cons 9 0) pending nil))))
           (fn-cat-history-prefix-relation history arena
                                           (mv-nth 2 (fn-cat-complete (cons 9 0) pending nil)))
           ; mismatched expected: refused likewise
           (not (fn-cat-history-relation history arena
                                         (mv-nth 2 (fn-cat-complete (cons 0 0)
                                                                    (fn-pc-make (cons 0 0) 1 held nil nil)
                                                                    nil)))))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; T2 at the host's finish over the flipped store (catalog-columns,
; 2026-09-27): books/served-catalog-owner.lisp fn-sca-ocl-relation-of-finish.
; The configured owner of owner-advance-carried-tests (config-owner-live's
; opened owner, one POST run through fn-ocfg-step to :completing; its three
; article rows name handles 0, 1, 2, each the same bytes), over an arena
; holding those payloads.  The catalog is the host's load of the rows before
; the completing one; the pending is the store's own row prepared after the
; seal (fn-cat-prepare-sealed); the token is the host's, read off the
; store's completion; the targets are the host's (fn-sca-targets-of over the
; finished view's withdrawals).  Every hypothesis and every conjunct of the
; conclusion (fn-cat-ocl-relation's, at the idle store) is evaluated.

(defconst *cet-p* (fn-record-payload (own-record-wire 0 0 "<x>")))
(defconst *cet-t2-payloads* (list *cet-p* *cet-p* *cet-p*))
(defconst *cet-t2-oc*
  (in-arena-acar-t-ocfg-run *cet-t2-payloads* *scar-t-oc*
                            (osi-drop-last (own-post-events *acar-t-record*))))

;; MODE: nil the host's pending; (:expected E) a pending made directly with
;; expected E (same token shape); (:token T) the host's pending, token T.
;; NCAT, NREC: the catalog is loaded from the first NCAT rows, RECORDS0 is
;; ALPHA of the first NREC rows.
(defun cet-t2-run (oc payloads ncat nrec mode fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (rows (fn-sf-records (fn-sn-files s)))
         (records0 (fn-rows-wire-of (take nrec rows) fn-arena))
         (fn-cat (fn-sca-load-held-rows (take ncat rows) (fn-own-view-index (fn-own-view o))
                                        fn-arena fn-cat))
         (row (fn-sn-completion-record s))
         (w (fn-held-wire-of row fn-arena))
         (pending (if (and (consp mode) (eq (car mode) :expected))
                      (fn-pc-make (cons (nfix (fn-record-txid row)) (cadr mode)) (cadr mode)
                                  row nil nil)
                    (fn-cat-prepare-sealed w row nil nil nil fn-arena fn-cat)))
         (token (if (and (consp mode) (eq (car mode) :token))
                    (cadr mode)
                  (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending))))
         (hyps (list (fn-ocl-relation oc)
                     (fn-cat-history-relation records0 fn-arena fn-cat)
                     (fn-sn-completion-enabledp s)
                     (equal (fn-sf-article-records (fn-rows-wire-of rows fn-arena))
                            (append (fn-sf-article-records records0) (list w)))
                     (fn-pc-p pending)
                     (equal token (fn-pc-token pending))
                     (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                     (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count fn-arena))
                     (fn-record-p w)))
         (finished (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish o (fn-ocfg-config oc) fn-arena))))
         (fo (fn-ocfg-owner finished))
         (targets (fn-sca-targets-of (fn-record-msgid row)
                                     (fn-own-view-withdrawals (fn-own-view fo)))))
    (mv-let (word pending2 fn-cat)
      (fn-sca-finish token pending (fn-own-view-index (fn-own-view fo)) targets fn-cat)
      (declare (ignore word pending2))
      (mv (list hyps
                (list (fn-ocl-relation finished)
                      (if (fn-own-store-idlep (fn-own-store fo)) t nil)
                      (fn-cat-history-relation
                       (fn-rows-wire-of (fn-sf-records (fn-sn-files (fn-own-store fo))) fn-arena)
                       fn-arena fn-cat)
                      (fn-cat-count fn-cat)))
          fn-arena fn-cat))))

(defun cet-t2-exec (oc payloads ncat nrec mode)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (cet-t2-run oc payloads ncat nrec mode fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(defconst *cet-t2-n* (len (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner *cet-t2-oc*))))))
(defconst *cet-t2-all* (list t t t t t t t t t))

; The history: two retention events, then the completing article (handle 2).
(assert-event (equal *cet-t2-n* 3))
(assert-event (equal (fn-record-payload (fn-sn-completion-record
                                         (fn-own-store (fn-ocfg-owner *cet-t2-oc*))))
                     2))

; Reachable positive witness: all nine hypotheses, and the conclusion (the
; owner's live relation after the finish, the idle store, R as the
; equality), the catalog holding the history's one article (non-vacuous: R
; reads ALPHA of the rows, and the retention rows are skipped).
(assert-event (equal (cet-t2-exec *cet-t2-oc* *cet-t2-payloads* 2 2 nil)
                     (list *cet-t2-all* (list t t t 1))))

; Hypothesis removal (each: every retained hypothesis holds, the removed one
; fails, and the conclusion fails -- here its R conjunct).
;  (equal token (fn-pc-token pending)): a stale token; the catalog refuses.
(assert-event (equal (cet-t2-exec *cet-t2-oc* *cet-t2-payloads* 2 2 '(:token (99 . 0)))
                     (list (list t t t t t nil t t t) (list t t nil 0))))
;  (equal (fn-pc-expected pending) (fn-cat-count fn-cat)): a pending that
;  expected one more row than the catalog holds.
(assert-event (equal (cet-t2-exec *cet-t2-oc* *cet-t2-payloads* 2 2 '(:expected 1))
                     (list (list t t t t t t nil t t) (list t t nil 0))))
;  (fn-cat-history-relation records0 fn-arena fn-cat): the catalog already
;  holds the article (loaded from all three rows) while RECORDS0 does not.
(assert-event (equal (cet-t2-exec *cet-t2-oc* *cet-t2-payloads* 3 2 nil)
                     (list (list t nil t t t t t t t) (list t t nil 2))))
;  the articles equation: RECORDS0 already holds the article (and the
;  catalog with it), so the history is not RECORDS0 followed by W.
(assert-event (equal (cet-t2-exec *cet-t2-oc* *cet-t2-payloads* 3 3 nil)
                     (list (list t t t nil t t t t t) (list t t nil 2))))
;  (< handle (fn-arena-count fn-arena)): an arena of two payloads; the row's
;  handle is outside (ALPHA reads no octets for it, still a record, the
;  equation holds), the pending made at the count directly, and R fails
;  (its handle conjunct).
(assert-event (equal (cet-t2-exec *cet-t2-oc* (list *cet-p* *cet-p*) 2 2 '(:expected 0))
                     (list (list t t t t t t t nil t) (list t t nil 1))))

;  (fn-ocl-relation oc), JOINTLY with the completion gate: the same owner
;  with its store's node replaced (owner-advance-carried-tests'
;  *scar-t-bad-node*) fails both, and the owner after the finish is in no
;  relation.  No owner tried here fails the relation alone.
;  NOT witnessed alone: (fn-pc-p pending) (the host's pending is always
;  fn-cat-prepare-sealed's, a pc when it is not refused by name) and
;  (fn-record-p W) (its only falsifier under the rest is a payload over
;  *fn-record-max-payload* octets); the gate (fn-sn-completion-enabledp)
;  only jointly, above.
(defconst *cet-t2-bad*
  (let* ((oc *cet-t2-oc*) (o (fn-ocfg-owner oc)))
    (fn-ocfg-make
     (fn-own-make (update-nth 3 *scar-t-bad-node* (fn-own-store o)) (fn-own-view o) (fn-own-conns o)
                  (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                  (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                  (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)
                  (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))
     (fn-ocfg-config oc) (fn-ocfg-pins oc) (fn-ocfg-staged oc))))
(assert-event (equal (cet-t2-exec *cet-t2-bad* *cet-t2-payloads* 2 2 nil)
                     (list (list nil t nil t t t t t t) (list nil nil t 1))))
