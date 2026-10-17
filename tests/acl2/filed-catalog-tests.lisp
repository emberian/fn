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

; P3-1 on a concrete commit: the assigned row is positional
(assert-event (fn-membership-listp (fn-record-groups (fn-cat-assign *p3-w0* nil))
                                   (fn-held-numbers (fn-cat-assign *p3-w0* nil))))

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

; an unfiled record that recovery accepts: its groups name the source's two
; groups out of order (the catalog-entries payload with no Newsgroups is
; refused by the recovery itself, (p4-open *p3-hbad*) = :fault)
(defconst *p4-swap* (p3-record 1 "<w3@b.example>" *o1-src* '("fn.letters" "fn.test")))
(assert-event (and (not (equal (p4-open *p3-h*) :fault))
                   (not (equal (p4-open (list *p3-w0* *p4-swap*)) :fault))
                   (equal (p4-open *p3-hbad*) :fault)))

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

