; The pinned reader dispatcher, generated from the protocol table's :arms
; column, IS the host-called one (lane defprotocol-2; p4 of lane
; defprotocol's plan).
;
; books/protocol-table.lisp gives each reader row an :arms column: the
; clauses fn-nntp-command-pinned tries when a command line's first token is
; that row's command, in order.  From the rows this book generates
; fn-proto-command-pinned, ONE flat cond: the syntax pseudo-row, then one
; clause per row, then the unrecognized pseudo-row.  The served dispatcher
; is layered instead (the command layer fn-nntp-command-dispatch, itself
; generated from the table; the pinned arms fn-nntp-archive-command-pinned
; with its Xref prelude; the reference arms fn-nntp-archive-command and
; fn-nntp-session-command), so the flat reading is not true by
; construction: the arms of one command are spread over four functions and
; an arm for another command, tried first, must fall away.
;
; KEYSTONE fn-proto-command-pinned-is-command-pinned: for every token list
; the generated dispatcher equals fn-nntp-command-pinned.  The subject is
; fn-nntp-command-pinned, the reader dispatcher of the served path
; (host/native/owner.lisp fnn-owner-handle-chunk-read -> fn-owner-chunk-span
; -> fn-scr-step -> fn-scr-command, equal to fn-nntp-command-pinned under
; fn-scr-command-is-command-pinned).  A reordered arm, a dropped one or a
; row whose :arms says another thing refuses this theorem: the table's
; :arms column is the dispatcher's text for each command, checked.
;
; Shape of the proof, as in books/protocol-codes.lisp: one generated lemma
; per row with :arms opens both sides under that row's keyword (the other
; commands' arms fall away by fn-proto-dispatch-keywordp-exclusive), one
; for a keyword token no row names, one for a first token that is not a
; keyword; the keystone is their case split.

(in-package "ACL2")
(include-book "nntp")
(include-book "protocol-table")

; -----------------------------------------------------------------------------
; The generated dispatcher

(make-event
 `(defun fn-proto-command-pinned (session archive index verdicts env tokens fn-arena)
    (declare (xargs :stobjs fn-arena :verify-guards nil))
    (let ((keyword (car tokens))
          (args (cdr tokens)))
      (cond
       ((not (fn-nntp-keyword-tokenp keyword))
        (fn-nntp-single session (fn-proto-text "(syntax)" :syntax)))
       ,@(fn-proto-flat-clauses *fn-proto-table*)
       (t (fn-nntp-single session (fn-proto-text "(unrecognized)" :unknown)))))))

; -----------------------------------------------------------------------------
; Keyword exclusivity (books/protocol-codes.lisp proves the same fact as
; fn-proto-keywordp-exclusive; that book includes the response-builder
; lemmas, which this one does not need).

(local
 (defthm fn-proto-dispatch-keywordp-exclusive
   (implies (and (fn-nntp-keywordp keyword a)
                 (syntaxp (quotep b))
                 (not (equal (fn-nntp-string-octets a) (fn-nntp-string-octets b))))
            (not (fn-nntp-keywordp keyword b)))
   :hints (("Goal" :in-theory (enable fn-nntp-keywordp)))))

(defconst *fn-proto-dispatch-open*
  '(fn-proto-command-pinned fn-nntp-command-pinned fn-nntp-archive-command-pinned
    fn-nntp-archive-command fn-nntp-session-command fn-nntp-archive-keywordp))

; Closed: the token recognizers (an arm for another command falls away by
; exclusivity, not by computing) and the arms' argument tests and pin
; accessors, which both sides share uninterpreted; and the Xref prelude
; (fn-nntp-xref-reply, fn-rcompat-reply), which the nested side calls for
; every archive command and the flat side only in the rows it answers:
; fn-nntp-xref-reply-only-for-over-and-list and
; fn-rcompat-reply-only-for-its-commands drop it elsewhere.  Opening these
; cost the LIST/OVER/XOVER rows 1,600,000 prover steps.
(defconst *fn-proto-dispatch-closed*
  '(fn-nntp-keywordp fn-nntp-keyword-tokenp fn-nntp-upcase-keyword
    fn-nntp-parse-range fn-nntp-range-okp fn-nntp-xref-server fn-gidx-pinp
    fn-rcompat-list-keywordp fn-nntp-message-id-tokenp fn-nntp-number-tokenp
    fn-nntp-printable-tokenp fn-gidx-pin-buckets fn-gidx-pin-trie
    fn-nntp-xref-reply fn-rcompat-reply))

(defun fn-proto-dispatch-row-names (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (fn-proto-row-arms (car rows))
          (cons (car (car rows)) (fn-proto-dispatch-row-names (cdr rows)))
        (fn-proto-dispatch-row-names (cdr rows)))
    nil))

(defconst *fn-proto-dispatch-rows* (fn-proto-dispatch-row-names *fn-proto-table*))

(defun fn-proto-dispatch-thm-name (name)
  (declare (xargs :guard (stringp name)))
  (intern-in-package-of-symbol
   (concatenate 'string "FN-PROTO-DISPATCH-ROW-" (string-upcase name))
   'fn-proto-command-pinned))

(defun fn-proto-dispatch-row-events (names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (cons `(local
              (defthm ,(fn-proto-dispatch-thm-name (car names))
                (implies (fn-nntp-keywordp (car tokens) ,(car names))
                         (equal (fn-proto-command-pinned session archive index verdicts
                                                         env tokens fn-arena)
                                (fn-nntp-command-pinned session archive index verdicts
                                                        env tokens fn-arena)))
                :hints (("Goal" :in-theory (e/d ,*fn-proto-dispatch-open*
                                                ,*fn-proto-dispatch-closed*)))))
            (fn-proto-dispatch-row-events (cdr names)))
    nil))

(make-event (cons 'progn (fn-proto-dispatch-row-events *fn-proto-dispatch-rows*)))

(defun fn-proto-dispatch-not-any (names term)
  (declare (xargs :guard t))
  (if (consp names)
      (cons `(not (fn-nntp-keywordp ,term ,(car names)))
            (fn-proto-dispatch-not-any (cdr names) term))
    nil))

(defun fn-proto-dispatch-cases (names term)
  (declare (xargs :guard t))
  (if (consp names)
      (cons `(fn-nntp-keywordp ,term ,(car names))
            (fn-proto-dispatch-cases (cdr names) term))
    nil))

(make-event
 `(local
   (defthm fn-proto-dispatch-row-none
     (implies (and (fn-nntp-keyword-tokenp (car tokens))
                   ,@(fn-proto-dispatch-not-any *fn-proto-dispatch-rows* '(car tokens)))
              (equal (fn-proto-command-pinned session archive index verdicts
                                              env tokens fn-arena)
                     (fn-nntp-command-pinned session archive index verdicts
                                             env tokens fn-arena)))
     :hints (("Goal" :in-theory (e/d ,*fn-proto-dispatch-open*
                                     ,*fn-proto-dispatch-closed*))))))

(local
 (defthm fn-proto-dispatch-row-syntax
   (implies (not (fn-nntp-keyword-tokenp (car tokens)))
            (equal (fn-proto-command-pinned session archive index verdicts
                                            env tokens fn-arena)
                   (fn-nntp-command-pinned session archive index verdicts
                                           env tokens fn-arena)))
   :hints (("Goal" :in-theory (enable fn-proto-command-pinned fn-nntp-command-pinned)))))

(make-event
 `(local
   (defthm fn-proto-command-pinned-is-command-pinned-by-rows
     (equal (fn-proto-command-pinned session archive index verdicts env tokens fn-arena)
            (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena))
     :hints (("Goal"
              :cases ((not (fn-nntp-keyword-tokenp (car tokens)))
                      ,@(fn-proto-dispatch-cases *fn-proto-dispatch-rows* '(car tokens)))
              :in-theory (disable fn-proto-command-pinned fn-nntp-command-pinned
                                  ,@*fn-proto-dispatch-closed*))))))

; -----------------------------------------------------------------------------
; KEYSTONE.  The dispatcher generated from the table's :arms column is the
; host-called reader dispatcher.

(defthm fn-proto-command-pinned-is-command-pinned
  (equal (fn-proto-command-pinned session archive index verdicts env tokens fn-arena)
         (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena))
  :hints (("Goal" :by fn-proto-command-pinned-is-command-pinned-by-rows)))
