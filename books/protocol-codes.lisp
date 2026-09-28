; Every reply code the reader dispatcher emits for a command is in that
; command's row of the protocol table (lane defprotocol; books/protocol-table.lisp).
;
; The subject is fn-nntp-command-pinned (books/nntp.lisp), the reader
; dispatcher of the served path: host/native/owner.lisp
; fnn-owner-handle-chunk-read calls fn-owner-chunk-span, whose served step
; reaches fn-scr-step (books/served-catalog-chain.lisp) and fn-scr-command,
; which fn-scr-command-is-command-pinned equates with fn-nntp-command-pinned
; under the catalog relation.  The keystone is
; fn-proto-command-pinned-replies-are-in-the-row: for every token list, every
; :reply effect of the dispatcher's result carries a status code that the
; table's row for the first token lists at layer :reader
; (fn-proto-reader-codes).  No hypothesis: an unreachable defensive branch
; keeps its code in the row, marked :unreachable there.
;
; Shape of the proof.  A reply's code is the natural number its first three
; octets spell (fn-proto-octets-code).  One lemma per response builder, bottom
; up, says the codes of its replies are among a set -- stated as
; member-equal hypotheses so that a caller whose set is a ground list
; discharges them by evaluation, and parametric where the builder's code is
; (fn-proto-retrieval-code KIND for ARTICLE/HEAD/BODY/STAT, fn-proto-hdr-code
; LEGACYP for HDR/XHDR).  One lemma per ROW, generated from the table by
; `fn-proto-row-events' (books/protocol-codes-rows.lisp), opens the
; dispatcher under that row's keyword; the keystone is their case split,
; also generated.  A per-row theorem is smaller
; than one theorem by induction over the row list: each row's proof opens the
; dispatcher once under one keyword, where the other arms fall away by
; fn-proto-keywordp-exclusive, and the case split over the rows is then
; propositional; an induction over the rows would have to carry the whole
; dispatcher through its step.

(in-package "ACL2")
; The definitions, the helper lemmas and one theorem per row.
(include-book "protocol-codes-rows")

(local (in-theory (enable fn-nntp-syntax-vocabulary)))

; -----------------------------------------------------------------------------
; KEYSTONE.  Every reply code of the reader dispatcher is in the table's row
; for the command's first token.

(defun fn-proto-row-cases (alist term)
  (declare (xargs :guard t))
  (if (consp alist)
      (cons `(fn-nntp-keywordp ,term ,(and (consp (car alist)) (car (car alist))))
            (fn-proto-row-cases (cdr alist) term))
    nil))

; The case split, generated from the table (local: the ledger reads the
; keystone below, which a make-event would hide from its non-evaluating reader).
(make-event
 `(local (defthm fn-proto-command-pinned-replies-are-in-the-row-by-rows
    (fn-proto-within
     (fn-nntp-result-effects
      (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena))
     (fn-proto-reader-codes (car tokens)))
    :hints (("Goal"
             :cases ((not (fn-nntp-keyword-tokenp (car tokens)))
                     ,@(fn-proto-row-cases *fn-proto-reader-alist* '(car tokens)))
             :in-theory (disable fn-nntp-command-pinned fn-proto-reader-codes
                                 ,@*fn-proto-token-theory*))))))

(defthm fn-proto-command-pinned-replies-are-in-the-row
  (fn-proto-within
   (fn-nntp-result-effects
    (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena))
   (fn-proto-reader-codes (car tokens)))
  :hints (("Goal" :by fn-proto-command-pinned-replies-are-in-the-row-by-rows)))
