; fn: teeth for books/catalog-entries.lisp (wave 5, lane catalog-boundary-owner,
; 2026-09-26).
;
; What this book is evidence FOR.  `fn-cat-ocl-relation-at-recover': the owner
; host/owner-host.lisp fn-owner-recover-extended installs from the capture of
; a prefix extended over a suffix -- here a one-article history under the
; default configuration record, opened :ok on both splits -- is in R with
; the catalog the load fold builds from the creators over the same history:
; every conjunct evaluated (fn-ocl-relation, the idle phase, the records,
; and the exec fold's fn-cat-history-relation on live stobjs).  Hypothesis
; removal: an install the host refuses (connection bound not natural) is
; :fault and :fault satisfies no relation; a generation that is not natural
; makes the interned rows fail fn-held-p and the relation false (on the
; logical side, by evaluation).  `fn-cat-load-of-append': loading the prefix
; then the suffix on live stobjs materializes the same rows as loading the
; history.
;
; `fn-cat-ocl-relation-of-article-finish' (T2): on owner-tests' recipe (the
; model owner posting one article up to :completing) every store-side
; conjunct is evaluated -- the completion is enabled, the history's articles
; are the (empty) catalog's rows followed by the completing record, the
; finish keeps the records and returns an idle store -- and the catalog side
; on the logical side: fn-cat-complete by the pending's token over the
; interned record restores the equality, and a stale token or a mismatched
; expected leaves the catalog behind the history.  NOT witnessed here: the
; `fn-ocl-relation' conjunct itself on a :completing owner (the configured
; owner the host installs opens at :recovering and needs the recovery
; barriers and fn-ocfg-open before a post; tests/acl2/owner-checkpoint-open-
; tests.lisp witnesses fn-ocl-relation of the installed owner, and
; books/owner-commit-ocl.lisp's keystone carries it across the commit);
; this sentence is the label.

(in-package "ACL2")
(include-book "../../books/catalog-entries")
(include-book "../../books/crypto-attach")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

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

(defconst *cet-full*
  (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture *cet-configs* nil) *cet-configs* *cet-h*)
                           *cet-configs* 8 4))
(defconst *cet-ckpt*
  (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture *cet-configs* *cet-h*) *cet-configs* nil)
                           *cet-configs* 8 4))

; The owner's conjuncts of the conclusion, on both entries.
(assert-event (and (not (equal *cet-full* :fault)) (not (equal *cet-ckpt* :fault))))
(assert-event (and (fn-ocl-relation *cet-full*) (fn-ocl-relation *cet-ckpt*)))
(assert-event (and (fn-own-store-idlep (fn-own-store (fn-ocfg-owner *cet-full*)))
                   (fn-own-store-idlep (fn-own-store (fn-ocfg-owner *cet-ckpt*)))))
(assert-event (and (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner *cet-full*)))) *cet-h*)
                   (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner *cet-ckpt*)))) *cet-h*)))
(assert-event (equal *cet-full* *cet-ckpt*))

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
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift fn-own-run 2)
(bpr-lift fn-own-step 2)
(defconst *cet-begun* (in-arena-fn-own-step *sr-arena* (in-arena-fn-own-step *sr-arena* *cet-a* '(:open)) '(:begin 1)))
(defconst *cet-completing* (in-arena-fn-own-run *sr-arena* *cet-begun* (butlast (cet-post-events *cet-w0*) 1)))
(defconst *cet-s* (fn-own-store *cet-completing*))
(defconst *cet-records* (fn-sf-records (fn-sn-files *cet-s*)))

; The store-side antecedent: :completing with the article record the newest
; (and only) article of the history; the (empty) catalog covers all before it.
(assert-event (fn-sn-completion-enabledp *cet-s*))
(assert-event (equal (fn-sn-completion-record *cet-s*) *cet-w0*))
(assert-event (equal (fn-sf-article-records *cet-records*)
                     (append (fn-sf-article-records nil) (list *cet-w0*))))
(assert-event (fn-record-p *cet-w0*))

; The store-side conclusion: the host's finish keeps the records and leaves
; the store idle.
; (the owner the host installs: fn-ccar-own-finish-installs-ccar-own-complete-by-definition)
(defconst *cet-finished* (fn-ccar-own-complete *cet-completing*))
(assert-event (equal (fn-sf-records (fn-sn-files (fn-own-store *cet-finished*))) *cet-records*))
(assert-event (fn-own-store-idlep (fn-own-store *cet-finished*)))
(assert-event (equal (fn-own-view-version (fn-own-view *cet-finished*)) 1))

; The catalog side, on the logical side: the pending PreparedCommit over the
; interned record, completed by its token at expected 0, materializes the
; history's articles; a stale token or a mismatched expected leaves the
; catalog behind the history (the equality fails; the prefix form still
; holds: the state before T2).
; (The intern takes the arena stobj, so the held record and its arena are
; built on the logical side, inside the theorem.)
(defthm cet-w-article-finish-catalog-side
  (mv-let (held arena)
    (fn-cat-intern-list *cet-w0* nil 0 nil)
    (let ((pending (fn-pc-make (cons 0 0) 0 held nil nil)))
      (and (fn-cat-history-relation nil arena nil)
           (fn-pc-p pending)
           (equal (fn-pc-expected pending) (fn-cat-count nil))
           (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count arena))
           (equal (fn-held-wire-of (fn-pc-held pending) arena) *cet-w0*)
           (fn-cat-history-relation *cet-records* arena
                                    (mv-nth 2 (fn-cat-complete (fn-pc-token pending) pending nil)))
           ; stale token: refused, the catalog stays behind the history (the
           ; prefix form, the state before T2, still holds)
           (not (fn-cat-history-relation *cet-records* arena
                                         (mv-nth 2 (fn-cat-complete (cons 9 0) pending nil))))
           (fn-cat-history-prefix-relation *cet-records* arena
                                           (mv-nth 2 (fn-cat-complete (cons 9 0) pending nil)))
           ; mismatched expected: refused likewise
           (not (fn-cat-history-relation *cet-records* arena
                                         (mv-nth 2 (fn-cat-complete (cons 0 0)
                                                                    (fn-pc-make (cons 0 0) 1 held nil nil)
                                                                    nil)))))))
  :rule-classes nil)
