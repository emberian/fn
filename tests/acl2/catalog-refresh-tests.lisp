; fn: teeth for books/catalog-refresh.lisp (PRF-202; wave 5, lane
; catalog-boundary-owner, 2026-09-26).
;
; What this book is evidence FOR.  `fn-view-apply-is-refresh': on a reachable
; owner (owner-tests' recipe: the owner over the initial store, a reader
; open, a CLI connection that posts one article through the real kernel
; events up to :completing), the store the finish produces satisfies the
; two hypotheses (its acceptance's articles are the new article consed onto
; the view's raw list; its verdicts are the article's verdict consed onto
; the view's) and the refreshed view IS the delta's application, field for
; field; and the owner's own fn-own-complete produces that view.  One
; hypothesis-removal witness per falsifiable hypothesis: a store that is not
; idle (the refresh does nothing, the apply advances); a view whose raw list
; already holds the article (the refresh finds no change, the apply conses
; it again); a view whose verdicts already hold the pair (the two verdict
; lists differ).  The `(consp a)' hypothesis: every acceptance article is a
; cons (fn-article-listp), no reachable state falsifies it, and the theorem
; may hold without it; it is NOT removed because the weakened theorem is not
; proved (AGENTS.md: failed proof search is not a counterexample) and NOT
; witnessed, and this sentence is the label.
;
; On the catalog: the mixed history of the relation tests loaded on live
; stobjs, then a commit (`fn-cat-view-articles-of-commit-advanced' and
; `-pinned' by evaluation), then the cancel's composed transaction in the
; order that reproduces the refresh (`fn-cat-withdraw-then-commit-view').
; The `(null (fn-held-withdrawn h))' hypothesis of the commit theorem is
; witnessed by committing an already-withdrawn row: the new version does not
; show it.  The same hypothesis on the target in
; `fn-cat-view-below-of-withdraw-advanced' may be redundant (an already
; withdrawn target is invisible at every later version anyway) and is not
; removed for the same reason.

(in-package "ACL2")
(include-book "../../books/catalog-refresh")
(include-book "../../books/crypto-attach")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (and (eq (symbol-class 'fn-crf-apply-article (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-crf-with-store (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-view-below-except (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The owner: owner-tests' recipe, up to :completing, then the finish.

(defconst *crt-groups* '("fn.letters" "fn.test"))

(defun crt-record (sequence txid msgid)
  (fn-record-make sequence txid txid msgid
                  (list 77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10
                        72 105 13 10)
                  '("fn.letters")
                  (concatenate 'string "own-pin:" msgid)
                  (concatenate 'string "own-content:" msgid)
                  (concatenate 'string "own-release:" msgid)
                  2 841000000))

(defun crt-post-events (record)
  (list '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare record))
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))
        '(:complete)))

(defconst *crt-0* (fn-own-start (fn-sn-initial *crt-groups* 10) 4))
(defconst *crt-a* (cdr (fn-own-open *crt-0* nil)))
(defconst *crt-begun* (fn-own-step (fn-own-step *crt-a* '(:open)) '(:begin 1)))
(defconst *crt-completing*
  (fn-own-run *crt-begun* (butlast (crt-post-events (crt-record 0 0 "<one@example>")) 1)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store *crt-completing*))) :completing))
(assert-event (fn-sn-completion-enabledp (fn-own-store *crt-completing*)))

; The finish's store, the article it installed and its verdict.
(defconst *crt-s* (fn-sn-finish (fn-own-store *crt-completing*)))
(defconst *crt-view* (fn-own-view *crt-completing*))
(defconst *crt-a1* (car (fn-state-articles (fn-node-acceptance (fn-sn-node *crt-s*)))))
(defconst *crt-verdict* (cdr (car (fn-sn-verdicts *crt-s*))))

; The complete antecedent, on the reachable state.
(assert-event (fn-own-store-idlep *crt-s*))
(assert-event (consp *crt-a1*))
(assert-event (equal (fn-state-articles (fn-node-acceptance (fn-sn-node *crt-s*)))
                     (cons *crt-a1* (fn-own-view-raw *crt-view*))))
(assert-event (equal (fn-sn-verdicts *crt-s*)
                     (cons (cons (fn-article-msgid *crt-a1*) *crt-verdict*)
                           (fn-own-view-verdicts *crt-view*))))
(assert-event (equal (fn-article-msgid *crt-a1*) "<one@example>"))

; The conclusion: the refresh is the delta's application, and it is the view
; fn-own-complete installs; the version advanced by the one record, the raw
; list and the visible list gained the article, the trie answers it.
(defconst *crt-refreshed* (fn-own-view (fn-own-refresh (fn-crf-with-store *crt-completing* *crt-s*))))
(defconst *crt-applied* (fn-crf-apply-article *crt-view* *crt-a1* *crt-verdict* *crt-s*))
(assert-event (equal *crt-refreshed* *crt-applied*))
(assert-event (equal (fn-own-view (fn-own-complete *crt-completing*)) *crt-applied*))
(assert-event (equal (fn-own-view-version *crt-applied*) (+ 1 (fn-own-view-version *crt-view*))))
(assert-event (equal (fn-own-view-raw *crt-applied*) (cons *crt-a1* (fn-own-view-raw *crt-view*))))
(assert-event (equal (fn-state-articles (fn-own-view-archive *crt-applied*))
                     (cons *crt-a1* (fn-state-articles (fn-own-view-archive *crt-view*)))))
(assert-event (equal (fn-midx-lookup "<one@example>" (fn-own-view-index *crt-applied*)) *crt-a1*))
(assert-event (null (fn-own-view-withdrawn *crt-applied*)))

; Hypothesis removal: the store is NOT idle (its files are the completing
; store's, everything else the finish's).  The refresh leaves the view; the
; apply advances it.
(defconst *crt-s-busy*
  (fn-sn-make-v6 (fn-sn-groups *crt-s*) (fn-sn-capacity *crt-s*)
                 (fn-sn-files (fn-own-store *crt-completing*)) (fn-sn-node *crt-s*)
                 (fn-sn-keyring *crt-s*) (fn-sn-index *crt-s*) (fn-sn-keyring-generation *crt-s*)
                 (fn-sn-verdicts *crt-s*) (fn-sn-keyring-snapshots *crt-s*)
                 (fn-sn-identity-next *crt-s*) (fn-sn-config-history *crt-s*)
                 (fn-sn-consumer *crt-s*) (fn-sn-topic *crt-s*) (fn-sn-event-index *crt-s*)))
(assert-event (not (fn-own-store-idlep *crt-s-busy*)))
(assert-event (and (consp *crt-a1*)
                   (equal (fn-state-articles (fn-node-acceptance (fn-sn-node *crt-s-busy*)))
                          (cons *crt-a1* (fn-own-view-raw *crt-view*)))
                   (equal (fn-sn-verdicts *crt-s-busy*)
                          (cons (cons (fn-article-msgid *crt-a1*) *crt-verdict*)
                                (fn-own-view-verdicts *crt-view*)))))
(assert-event (not (equal (fn-own-view (fn-own-refresh (fn-crf-with-store *crt-completing* *crt-s-busy*)))
                          (fn-crf-apply-article *crt-view* *crt-a1* *crt-verdict* *crt-s-busy*))))

; Hypothesis removal: the view's raw list already holds the article (the
; acceptance did not grow over it).  The other hypotheses hold.
(defun crt-view-with-raw (view raw)
  (fn-own-view-make-visible (fn-own-view-version view) (fn-own-view-frontier view)
                            (fn-own-view-archive view) (fn-own-view-verdicts view)
                            (fn-own-view-index view) (fn-own-view-group-index view)
                            (fn-own-view-withdrawals view) raw (fn-own-view-withdrawn view)
                            (fn-own-view-keyring view)))
(defun crt-view-with-verdicts (view verdicts)
  (fn-own-view-make-visible (fn-own-view-version view) (fn-own-view-frontier view)
                            (fn-own-view-archive view) verdicts
                            (fn-own-view-index view) (fn-own-view-group-index view)
                            (fn-own-view-withdrawals view) (fn-own-view-raw view)
                            (fn-own-view-withdrawn view) (fn-own-view-keyring view)))
(defun crt-owner-with-view (o view)
  (fn-own-make (fn-own-store o) view (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
               (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
               (fn-own-config o) (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))

(defconst *crt-view-raw* (crt-view-with-raw *crt-view* (cons *crt-a1* (fn-own-view-raw *crt-view*))))
(defconst *crt-o-raw* (crt-owner-with-view *crt-completing* *crt-view-raw*))
(assert-event (and (fn-own-store-idlep *crt-s*) (consp *crt-a1*)
                   (not (equal (fn-state-articles (fn-node-acceptance (fn-sn-node *crt-s*)))
                               (cons *crt-a1* (fn-own-view-raw *crt-view-raw*))))
                   (equal (fn-sn-verdicts *crt-s*)
                          (cons (cons (fn-article-msgid *crt-a1*) *crt-verdict*)
                                (fn-own-view-verdicts *crt-view-raw*)))))
(assert-event (not (equal (fn-own-view (fn-own-refresh (fn-crf-with-store *crt-o-raw* *crt-s*)))
                          (fn-crf-apply-article *crt-view-raw* *crt-a1* *crt-verdict* *crt-s*))))

; Hypothesis removal: the view's verdicts already hold the pair.
(defconst *crt-view-v* (crt-view-with-verdicts *crt-view* (fn-sn-verdicts *crt-s*)))
(defconst *crt-o-v* (crt-owner-with-view *crt-completing* *crt-view-v*))
(assert-event (and (fn-own-store-idlep *crt-s*) (consp *crt-a1*)
                   (equal (fn-state-articles (fn-node-acceptance (fn-sn-node *crt-s*)))
                          (cons *crt-a1* (fn-own-view-raw *crt-view-v*)))
                   (not (equal (fn-sn-verdicts *crt-s*)
                               (cons (cons (fn-article-msgid *crt-a1*) *crt-verdict*)
                                     (fn-own-view-verdicts *crt-view-v*))))))
(assert-event (not (equal (fn-own-view (fn-own-refresh (fn-crf-with-store *crt-o-v* *crt-s*)))
                          (fn-crf-apply-article *crt-view-v* *crt-a1* *crt-verdict* *crt-s*))))

; The plain case (fn-crf-apply-article-plain) on the same state: the article
; withdraws nothing and is not withdrawn, so the trie is extended and the
; raw and visible lists gain the article (asserted above).  This state's
; view carries NO group index (the initial owner's empty archive builds
; none), which is the hypothesis-removal witness for the theorem's
; `(fn-own-view-group-index view)': the apply builds the buckets from the
; visible list instead of putting the article's entries.
(assert-event (and (null (fn-own-view-group-index *crt-view*))
                   (equal (fn-own-view-index *crt-applied*)
                          (fn-midx-extend *crt-a1* (fn-own-view-index *crt-view*)))
                   (equal (fn-own-view-group-index *crt-applied*)
                          (fn-gidx-build (fn-state-articles (fn-own-view-archive *crt-applied*))))))

; -----------------------------------------------------------------------------
; The catalog: the mixed history, a commit, and the cancel's transaction.

(defconst *crt-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *crt-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *crt-w0* (fn-record-make 0 1 1 "<a@x>" *crt-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *crt-r1* (fn-store-retention-event-make :undertake 1 2 2 "id" "subject" "evidence" 3))
(defconst *crt-w2* (fn-record-make 2 3 3 "<c@x>" *crt-p2* '("fn.test") "o" "s" "e" 1 5))
(defconst *crt-h* (list *crt-w0* *crt-r1* *crt-w2*))
(defconst *crt-w3* (fn-record-make 3 4 4 "<d@x>" *crt-p0* '("fn.test") "o" "s" "e" 1 5))

(defun crt-run (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load *crt-h* nil 0 fn-arena fn-cat)
      (let* ((v2 (fn-cat-view-articles 2 fn-arena fn-cat))
             (below-2-at-3 (fn-cat-view-below 2 3 fn-arena fn-cat)))
        (mv-let (h3 fn-arena)
          (fn-cat-intern-list *crt-w3* nil 0 fn-arena)
          ; the :article delta: commit row 2 (the third article)
          (let* ((fn-cat (fn-cat-commit h3 fn-cat))
                 (commit (list (equal (fn-cat-view-articles 2 fn-arena fn-cat) v2)          ; pinned: unchanged
                               (equal (fn-cat-view-articles 3 fn-arena fn-cat)
                                      (cons (fn-cat-row-article 2 fn-arena fn-cat) below-2-at-3))
                               (fn-article-msgid (car (fn-cat-view-articles 3 fn-arena fn-cat)))))
                 ; the cancel's transaction on the loaded three rows: withdraw
                 ; row 0 (version 3), then commit the cancel row (row 3)
                 (fn-cat (fn-cat-withdraw 0 3 fn-cat))
                 (except (fn-cat-view-below-except 0 3 4 fn-arena fn-cat)))
            (mv-let (h4 fn-arena)
              (fn-cat-intern-list (fn-record-make 4 5 5 "<cancel@x>" *crt-p2* '("fn.test") "o" "s" "e" 1 5)
                                  nil 0 fn-arena)
              (let* ((fn-cat (fn-cat-commit h4 fn-cat))
                     (cancel (list (len (fn-cat-view-articles 3 fn-arena fn-cat))             ; version 3: 3 rows
                                   (len (fn-cat-view-articles 4 fn-arena fn-cat))             ; version 4: cancel + 2
                                   (equal (fn-cat-view-articles 4 fn-arena fn-cat)
                                          (cons (fn-cat-row-article 3 fn-arena fn-cat) except))
                                   (fn-cat-view-find "<a@x>" 4 3 fn-cat)                       ; target at version 3
                                   (fn-cat-view-find "<a@x>" 4 4 fn-cat)                       ; gone at version 4
                                   (fn-cat-view-find "<cancel@x>" 4 4 fn-cat))))
                (mv (list commit cancel) fn-arena fn-cat)))))))))

(defun crt-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (crt-run fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event
 (equal (crt-exec)
        (list (list t t "<d@x>")
              (list 3 3 t 0 nil 3))))

; Hypothesis removal for fn-cat-view-articles-of-commit-advanced: a row
; committed already withdrawn is not on top of the new version.
(defun crt-run-withdrawn (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load *crt-h* nil 0 fn-arena fn-cat)
      (mv-let (h3 fn-arena)
        (fn-cat-intern-list *crt-w3* nil 0 fn-arena)
        (let* ((h3w (fn-held-with-withdrawn h3 (cons 1 0)))
               (below (fn-cat-view-below 2 3 fn-arena fn-cat))
               (fn-cat (fn-cat-commit h3w fn-cat)))
          (mv (list (fn-held-withdrawn h3w)
                    (equal (fn-cat-view-articles 3 fn-arena fn-cat)
                           (cons (fn-cat-row-article 2 fn-arena fn-cat) below))
                    (equal (fn-cat-view-articles 3 fn-arena fn-cat) below))
              fn-arena fn-cat))))))

(defun crt-exec-withdrawn ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (crt-run-withdrawn fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event (equal (crt-exec-withdrawn) (list (cons 1 0) nil t)))
