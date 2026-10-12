; Witnesses and teeth for books/filed-catalog (O1 packet 3, the catalog
; half): a two-record history loaded into live stobjs by fn-cat-load meets
; every hypothesis of FN-O1-CATALOG-ROWS-WITHIN-HEADER and its conclusion at
; both rows (two groups at row 0); removing FN-O1-RECORDS-FILEDP (the
; catalog-entries fixture, whose payload names no group) or the history
; relation (a mismatched claimed history) falsifies the conclusion.
; FN-O1-CAT-POSITIONALP has no live removal witness: every executable
; catalog is built by fn-cat-commit, positional by
; FN-O1-ASSIGN-IS-POSITIONAL (labelled, not witnessed).
; Packet 4: FN-O1-CATALOG-ROWS-WITHIN-HEADER-AT-A-PREFIX on a catalog holding
; one row of a two-record history (the prefix relation holds and the
; history relation does not), with removals of the filed history and of the
; prefix relation; FN-O1-SERVED-CATALOG-ROWS-WITHIN-HEADER's idle arm on the
; owner recovered over the interned rows and the host's catalog load, its
; conjuncts evaluated, with the removal of the filed history (an unfiled row
; recovery accepts).
(in-package "ACL2")
(include-book "../../books/filed-catalog")
(include-book "../../books/served-catalog-owner")   ; the host's load over rows; store-intern
(include-book "../../books/store-reclaim-pack")   ; fn-rclp-tombstoned: the reclaimed record
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

; -----------------------------------------------------------------------------
; Packet 4.  P4-0a (FN-O1-CATALOG-ROWS-WITHIN-HEADER-AT-A-PREFIX): the
; catalog holds the first record of a two-record history, the state between
; the durable write of the second and the finish; the prefix relation holds
; where the history relation does not.
(defun p4-prefix-run (loaded claimed i fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load loaded nil 0 fn-arena fn-cat)
      (let ((article (fn-cat-row-article i fn-arena fn-cat)))
        (mv (list (fn-cat-count fn-cat)
                  (fn-cat-history-prefix-relation claimed fn-arena fn-cat)
                  (fn-o1-records-filedp claimed)
                  (fn-o1-cat-positionalp fn-cat)
                  (fn-o1-article-within-headerp article (fn-nntp-article-bytes article fn-arena))
                  (fn-cat-history-relation claimed fn-arena fn-cat))
            fn-arena fn-cat)))))
(defun p4-prefix-exec (loaded claimed i)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-arena fn-cat) (p4-prefix-run loaded claimed i fn-arena fn-cat) (mv r fn-arena)))
      r)))
; satisfiable: one row of two, prefix, filed, positional, conclusion; not the history relation
(assert-event (equal (p4-prefix-exec (list *p3-w0*) *p3-h* 0) '(1 t t t t nil)))
; removal of FN-O1-RECORDS-FILEDP: two rows of three, the second unfiled
(assert-event (equal (p4-prefix-exec *p3-hbad* (append *p3-hbad* (list *p3-w1*)) 1)
                     '(2 t nil t nil nil)))
; removal of the prefix relation: the catalog is not a prefix of the claim
(assert-event (equal (take 5 (p4-prefix-exec *p3-hbad* *p3-h* 1)) '(2 nil t t nil)))

; P4-0b (FN-O1-SERVED-CATALOG-ROWS-WITHIN-HEADER) at the idle arm: the
; owner recovered over the interned rows of a history, the host's catalog
; loaded by fn-sca-load-held-rows over the arena holding the payloads.
; fn-cat-ocl-relation is non-executable (defun-nx); its conjuncts are
; evaluated: fn-ocl-relation, the idle store and the history relation over
; the served articles of the store's rows.  The non-idle arm is P4-0a's.
(defconst *p4-configs* (list *fn-cfg-default-record*))
(defun p4-rows (ws)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena) (fn-intern-events ws nil 0 fn-arena) rows)))
(defun p4-open (ws)
  (declare (xargs :verify-guards nil))
  (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture *p4-configs* nil) *p4-configs* (p4-rows ws))
                           *p4-configs* 8 4))
(defun p4-payloads (ws)
  (declare (xargs :mode :program))
  (if (consp ws) (cons (fn-record-payload (car ws)) (p4-payloads (cdr ws))) nil))
(defun p4-served-run (oc payloads i fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((own (fn-ocfg-owner oc))
         (rows (fn-sf-records (fn-sn-files (fn-own-store own))))
         (view (fn-own-view own))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (fn-cat (fn-sca-load-held-rows rows (fn-midx-build (fn-state-articles (fn-own-view-archive view)))
                                        fn-arena fn-cat))
         (history (fn-cat-history-articles rows fn-arena))
         (article (fn-cat-row-article i fn-arena fn-cat)))
    (mv (list (fn-cat-count fn-cat)
              (fn-ocl-relation oc)
              (if (fn-own-store-idlep (fn-own-store own)) t nil)
              (fn-cat-history-relation history fn-arena fn-cat)
              (fn-o1-records-filedp history)
              (fn-o1-cat-positionalp fn-cat)
              (fn-o1-article-within-headerp article (fn-nntp-article-bytes article fn-arena)))
        fn-arena fn-cat)))
(defun p4-served-exec (ws i)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-arena fn-cat) (p4-served-run (p4-open ws) (p4-payloads ws) i fn-arena fn-cat) (mv r fn-arena)))
      r)))
; an unfiled record that recovery accepts: its groups name the source's two
; groups out of order (the catalog-entries payload with no Newsgroups is
; refused by the recovery itself, (p4-open *p3-hbad*) = :fault)
(defconst *p4-swap* (p3-record 1 "<w3@b.example>" *o1-src* '("fn.letters" "fn.test")))
(assert-event (and (not (equal (p4-open *p3-h*) :fault))
                   (not (equal (p4-open (list *p3-w0* *p4-swap*)) :fault))
                   (equal (p4-open *p3-hbad*) :fault)))
; satisfiable at both rows
(assert-event (equal (p4-served-exec *p3-h* 0) '(2 t t t t t t)))
(assert-event (equal (p4-served-exec *p3-h* 1) '(2 t t t t t t)))
; removal of FN-O1-RECORDS-FILEDP over the served history: the swapped row fails
(assert-event (equal (p4-served-exec (list *p3-w0* *p4-swap*) 1) '(2 t t t nil t nil)))

; -----------------------------------------------------------------------------
; The reclaim-aware conclusions (K1a FN-O1-CATALOG-ROWS-ARE-RECLAIMED-OR-
; WITHIN-HEADER, K1b ... -AT-A-PREFIX, K1c FN-O1-SERVED-CATALOG-ROWS-ARE-
; RECLAIMED-OR-WITHIN-HEADER) and their premise FN-O1-RECORDS-FILED-OR-
; RECLAIMEDP.  The reclaimed record *p5-z1* is the reclaim rewrite of *p3-w1*
; (FN-RCLP-TOMBSTONED: the groups kept, the payload a tombstone): the history
; (*p3-w0* *p5-z1*) is not filed (FN-O1-RECORDS-FILEDP is NIL of it), is
; filed-or-reclaimed, and its row 1 is a tombstone whose header fact fails.
; The conclusion with the tombstone disjunct removed (within the header only)
; is false of this satisfiable instance (the checked mutation).
(defconst *p5-z1* (fn-rclp-tombstoned *p3-w1*))
(defconst *p5-hz* (list *p3-w0* *p5-z1*))
(defun p5-run (records claimed i fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load records nil 0 fn-arena fn-cat)
      (let* ((article (fn-cat-row-article i fn-arena fn-cat))
             (tomb (fn-nntp-article-tombstonep article fn-arena))
             (within (fn-o1-article-within-headerp article (fn-nntp-article-bytes article fn-arena))))
        (mv (list (fn-cat-count fn-cat)                                  ; 0
                  (fn-cat-history-relation claimed fn-arena fn-cat)      ; 1 K1a relation
                  (fn-o1-records-filed-or-reclaimedp claimed)            ; 2 the premise
                  (fn-o1-cat-positionalp fn-cat)                         ; 3
                  (if tomb t nil)                                        ; 4 the tombstone disjunct
                  (if within t nil)                                      ; 5 the header disjunct
                  (if (or tomb within) t nil)                            ; 6 the conclusion
                  (fn-o1-records-filedp claimed))                        ; 7 the old premise
            fn-arena fn-cat)))))
(defun p5-exec (records claimed i)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-arena fn-cat) (p5-run records claimed i fn-arena fn-cat) (mv r fn-arena)))
      r)))
; K1a satisfiable at the reclaimed row: relation, premise, positional, tombstone, conclusion;
; not within the header, not filed-only
(assert-event (equal (p5-exec *p5-hz* *p5-hz* 1) '(2 t t t t nil t nil)))
; ... and at the filed row of the same history (the header disjunct, not the tombstone)
(assert-event (equal (p5-exec *p5-hz* *p5-hz* 0) '(2 t t t nil t t nil)))
; the mutation (conclusion = within the header only) is false of the satisfiable instance
(assert-event (not (nth 5 (p5-exec *p5-hz* *p5-hz* 1))))
; removal of the premise: the unfiled non-tombstone record of the catalog-entries fixture
(assert-event (equal (p5-exec *p3-hbad* *p3-hbad* 1) '(2 t nil t nil nil nil nil)))
; removal of the history relation: a claimed history that is not the loaded one
(assert-event (equal (take 7 (p5-exec *p3-hbad* *p5-hz* 1)) '(2 nil t t nil nil nil)))
; the positional hypothesis has no live removal witness (as FN-O1-CATALOG-ROWS-WITHIN-HEADER's: no
; executable updater builds a non-positional catalog; Codex p3 F8).

; K1b: the catalog holds the first record of the reclaimed history, then the
; reclaimed record, under the prefix relation (not the history relation).
(defun p5-prefix-run (loaded claimed i fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load loaded nil 0 fn-arena fn-cat)
      (let* ((article (fn-cat-row-article i fn-arena fn-cat))
             (tomb (fn-nntp-article-tombstonep article fn-arena))
             (within (fn-o1-article-within-headerp article (fn-nntp-article-bytes article fn-arena))))
        (mv (list (fn-cat-count fn-cat)
                  (fn-cat-history-prefix-relation claimed fn-arena fn-cat)   ; 1
                  (fn-o1-records-filed-or-reclaimedp claimed)                ; 2
                  (fn-o1-cat-positionalp fn-cat)                             ; 3
                  (if tomb t nil)                                            ; 4
                  (if within t nil)                                          ; 5
                  (if (or tomb within) t nil)                                ; 6
                  (fn-cat-history-relation claimed fn-arena fn-cat))         ; 7 not the history relation
            fn-arena fn-cat)))))
(defun p5-prefix-exec (loaded claimed i)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-arena fn-cat) (p5-prefix-run loaded claimed i fn-arena fn-cat) (mv r fn-arena)))
      r)))
; the loaded catalog is the reclaimed record alone, a prefix of (z1 w0)
(assert-event (equal (p5-prefix-exec (list *p5-z1*) (list *p5-z1* *p3-w0*) 0) '(1 t t t t nil t nil)))
; removal of the premise: two rows of three, the second unfiled non-tombstone
(assert-event (equal (p5-prefix-exec *p3-hbad* (append *p3-hbad* (list *p3-w1*)) 1)
                     '(2 t nil t nil nil nil nil)))
; removal of the prefix relation
(assert-event (equal (take 7 (p5-prefix-exec *p3-hbad* *p5-hz* 1)) '(2 nil t t nil nil nil)))

; K1c at the idle arm, on the owner recovered over the reclaimed history
; (the p4-served machinery: the interned rows, the host's catalog load over the
; arena holding the payloads, fn-cat-ocl-relation's conjuncts evaluated).
; CATALOG-RECORDS non-nil loads that history into the catalog instead of the
; owner's rows (the relation removal): the premise is evaluated first, on the
; owner's rows through the owner's arena.
(defun p5-served-run (oc payloads catalog-records i fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((own (fn-ocfg-owner oc))
         (rows (fn-sf-records (fn-sn-files (fn-own-store own))))
         (view (fn-own-view own))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many payloads fn-arena))
         (history (fn-cat-history-articles rows fn-arena))
         (premise (fn-o1-records-filed-or-reclaimedp history))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (if catalog-records
          (let ((fn-arena (fn-arena-clear fn-arena)))
            (fn-cat-load catalog-records nil 0 fn-arena fn-cat))
        (let ((fn-cat (fn-sca-load-held-rows rows (fn-midx-build (fn-state-articles (fn-own-view-archive view)))
                                             fn-arena fn-cat)))
          (mv fn-arena fn-cat)))
      (let* ((article (fn-cat-row-article i fn-arena fn-cat))
             (tomb (fn-nntp-article-tombstonep article fn-arena))
             (within (fn-o1-article-within-headerp article (fn-nntp-article-bytes article fn-arena))))
        (mv (list (fn-cat-count fn-cat)                                   ; 0
                  (fn-ocl-relation oc)                                    ; 1
                  (if (fn-own-store-idlep (fn-own-store own)) t nil)      ; 2
                  (fn-cat-history-relation history fn-arena fn-cat)       ; 3
                  premise                                                 ; 4 the premise
                  (fn-o1-cat-positionalp fn-cat)                          ; 5
                  (if tomb t nil)                                         ; 6
                  (if within t nil)                                       ; 7
                  (if (or tomb within) t nil)                             ; 8 the conclusion
                  (fn-o1-records-filedp history))                         ; 9 the old premise
            fn-arena fn-cat)))))
(defun p5-served-exec (ws catalog-records i)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-arena fn-cat)
          (p5-served-run (p4-open ws) (p4-payloads ws) catalog-records i fn-arena fn-cat)
          (mv r fn-arena)))
      r)))
; satisfiable at the reclaimed row: the old premise fails, the new one holds, the row is a tombstone
(assert-event (equal (p5-served-exec *p5-hz* nil 1) '(2 t t t t t t nil t nil)))
(assert-event (equal (p5-served-exec *p5-hz* nil 0) '(2 t t t t t nil t t nil)))
; the mutation (within the header only) is false of the satisfiable instance
(assert-event (not (nth 7 (p5-served-exec *p5-hz* nil 1))))
; removal of the premise: the swapped (unfiled, non-tombstone) record recovery accepts
(assert-event (equal (p5-served-exec (list *p3-w0* *p4-swap*) nil 1) '(2 t t t nil t nil nil nil nil)))
; removal of the relation: the catalog is loaded from another history (the unfiled record)
(assert-event (equal (p5-served-exec *p5-hz* *p3-hbad* 1) '(2 t t nil t t nil nil nil nil)))
