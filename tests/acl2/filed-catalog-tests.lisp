; Witnesses and teeth for books/filed-catalog (O1 packet 3, the catalog
; half): a two-record history loaded into live stobjs by fn-cat-load meets
; every hypothesis of FN-O1-CATALOG-ROWS-WITHIN-HEADER and its conclusion at
; both rows (two groups at row 0); removing FN-O1-RECORDS-FILEDP (the
; catalog-entries fixture, whose payload names no group) or the history
; relation (a mismatched claimed history) falsifies the conclusion.
; FN-O1-CAT-POSITIONALP has no live removal witness: every executable
; catalog is built by fn-cat-commit, positional by
; FN-O1-ASSIGN-IS-POSITIONAL (labelled, not witnessed).
(in-package "ACL2")
(include-book "../../books/filed-catalog")
(include-book "../../books/crypto-attach")
(include-book "../../books/codec-attach")

(defconst *o1-src*
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" (coerce '(#\Return #\Newline) 'string)
                "Newsgroups: fn.test,fn.letters" (coerce '(#\Return #\Newline) 'string)
                "Subject: s" (coerce '(#\Return #\Newline) 'string)
                "Message-ID: <w1@b.example>" (coerce '(#\Return #\Newline) 'string)
                (coerce '(#\Return #\Newline) 'string) "body" (coerce '(#\Return #\Newline) 'string))))
(defun p3-record (sequence msgid payload groups)
  (fn-record-make sequence sequence sequence msgid payload groups
                  (concatenate 'string "own-pin:" msgid)
                  (concatenate 'string "own-content:" msgid)
                  (concatenate 'string "own-release:" msgid)
                  2 841000000))
(defconst *p3-w0* (p3-record 0 "<w1@b.example>" *o1-src* '("fn.test" "fn.letters")))
(defconst *p3-w1* (p3-record 1 "<w2@b.example>" *o1-src* '("fn.letters")))
; the catalog-entries fixture: groups ("fn.letters"), payload names no group
(defconst *p3-bad* (p3-record 2 "<x@example>"
                    (list 77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10 72 105 13 10)
                    '("fn.letters")))
(defconst *p3-h* (list *p3-w0* *p3-w1*))
(defconst *p3-hbad* (list *p3-w0* *p3-bad*))
(defun p3-run (records claimed i fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load records nil 0 fn-arena fn-cat)
      (let ((article (fn-cat-row-article i fn-arena fn-cat)))
        (mv (list (fn-cat-count fn-cat)
                  (fn-cat-history-relation claimed fn-arena fn-cat)
                  (fn-o1-records-filedp claimed)
                  (fn-o1-cat-positionalp fn-cat)
                  (fn-o1-article-within-headerp article (fn-nntp-article-bytes article fn-arena))
                  (fn-article-groups article) (fn-article-memberships article))
            fn-arena fn-cat)))))
(defun p3-exec (records claimed i)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-arena fn-cat) (p3-run records claimed i fn-arena fn-cat) (mv r fn-arena)))
      r)))

(defconst *p3-good-0* (p3-exec *p3-h* *p3-h* 0))
(defconst *p3-good-1* (p3-exec *p3-h* *p3-h* 1))
; satisfiable: count 2, relation, filed, positional, conclusion; two groups
(assert-event (and (equal (take 5 *p3-good-0*) '(2 t t t t))
                   (equal (nth 5 *p3-good-0*) '("fn.test" "fn.letters"))
                   (equal (nth 6 *p3-good-0*) '(("fn.test" . 1) ("fn.letters" . 1)))))
(assert-event (equal (take 5 *p3-good-1*) '(2 t t t t)))
; removal of FN-O1-RECORDS-FILEDP: the other hypotheses hold, the conclusion fails
(assert-event (equal (take 5 (p3-exec *p3-hbad* *p3-hbad* 1)) '(2 t nil t nil)))
; removal of the history relation
(assert-event (equal (take 5 (p3-exec *p3-hbad* *p3-h* 1)) '(2 nil t t nil)))
; no bound on I: past the count the conclusion holds
(assert-event (equal (take 5 (p3-exec *p3-h* *p3-h* 5)) '(2 t t t t)))
; P3-1 on a concrete commit: the assigned row is positional
(assert-event (fn-membership-listp (fn-record-groups (fn-cat-assign *p3-w0* nil))
                                   (fn-held-numbers (fn-cat-assign *p3-w0* nil))))
; P3-2 on live stobjs: after the load, a withdrawal and a redecision keep the
; catalog positional with its two rows; a clear leaves it positional and empty.
(defun p3-updaters (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load *p3-h* nil 0 fn-arena fn-cat)
      (let* ((a (list (fn-cat-count fn-cat) (fn-o1-cat-positionalp fn-cat)))
             (fn-cat (fn-cat-withdraw 0 1 fn-cat))
             (b (list (fn-cat-count fn-cat) (fn-o1-cat-positionalp fn-cat)
                      (fn-held-withdrawn (fn-cat-at 0 fn-cat))))
             (fn-cat (fn-cat-redecide 1 (fn-held-context (fn-cat-at 1 fn-cat)) fn-cat))
             (c (list (fn-cat-count fn-cat) (fn-o1-cat-positionalp fn-cat)))
             (fn-cat (fn-cat-clear fn-cat))
             (d (list (fn-cat-count fn-cat) (fn-o1-cat-positionalp fn-cat))))
        (mv (list a b c d) fn-arena fn-cat)))))
(defun p3-updaters-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-arena fn-cat) (p3-updaters fn-arena fn-cat) (mv r fn-arena)))
      r)))
(assert-event (let ((r (p3-updaters-exec)))
                (and (equal (nth 0 r) '(2 t))
                     (equal (take 2 (nth 1 r)) '(2 t)) (consp (nth 2 (nth 1 r)))
                     (equal (nth 2 r) '(2 t))
                     (equal (nth 3 r) '(0 t)))))
; The positional hypothesis of FN-O1-CATALOG-ROWS-WITHIN-HEADER is independent
; only in the logical domain (Codex p3 F8): the singleton catalog
; (fn-held-with-numbers (fn-held-plain *p3-w0* 0) '(("other" . 1) ("fn.letters" . 1)))
; over an arena holding *o1-src* meets the relation and the filed history for
; (list *p3-w0*) at I = 0 and fails the conclusion; no public updater builds it.
