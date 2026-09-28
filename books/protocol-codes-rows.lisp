; The per-row theorems of the protocol table's reader codes (lane
; defprotocol; split from books/protocol-codes.lisp by lane defprotocol-2,
; which was 18.6 s at 3 jobs with them).  One generated theorem per reader
; row: fn-proto-row-NAME-codes (every reply code fn-nntp-command-pinned emits
; for a first token matching NAME is in the row's :reader codes) and
; fn-proto-row-NAME-lookup (fn-proto-reader-codes of such a token IS those
; codes), plus the unrecognized and syntax pseudo-rows.  The keystone, their
; case split, is books/protocol-codes.lisp; read its header for the subject
; and the shape of the proof.

(in-package "ACL2")
(include-book "protocol-builders")
(include-book "protocol-table")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-nntp-message-id-tokenp))))

(local (in-theory (enable fn-nntp-syntax-vocabulary)))

; -----------------------------------------------------------------------------
; The table's reader codes for a first token

(defun fn-proto-reader-codes-in (keyword alist)
  (declare (xargs :guard t))
  (if (consp alist)
      (if (and (consp (car alist)) (stringp (car (car alist)))
               (fn-nntp-keywordp keyword (car (car alist))))
          (cdr (car alist))
        (fn-proto-reader-codes-in keyword (cdr alist)))
    *fn-proto-unrecognized-codes*))

; The codes the table allows the reader dispatcher for a command line whose
; first token is KEYWORD: the syntax pseudo-row's for a token that is not a
; keyword (RFC 3977 section 9.8), the matching row's, or the unrecognized
; pseudo-row's.
(defun fn-proto-reader-codes (keyword)
  (declare (xargs :guard t))
  (if (fn-nntp-keyword-tokenp keyword)
      (fn-proto-reader-codes-in keyword *fn-proto-reader-alist*)
    *fn-proto-syntax-codes*))

; Two command names with different octets never match one token.
(defthm fn-proto-keywordp-exclusive
  (implies (and (fn-nntp-keywordp keyword a)
                (syntaxp (quotep b))
                (not (equal (fn-nntp-string-octets a) (fn-nntp-string-octets b))))
           (not (fn-nntp-keywordp keyword b)))
  :hints (("Goal" :in-theory (enable fn-nntp-keywordp))))

; A token that matches a command name that is a keyword is a keyword: the
; upcase map sends only a-z to A-Z, so it preserves RFC 3977 section 9.8's
; keyword shape in both directions.
(local
 (defthm fn-proto-first-byte-of-upcase
   (implies (fn-nntp-keyword-first-bytep (fn-nntp-upcase-byte b))
            (fn-nntp-keyword-first-bytep b))
   :hints (("Goal" :in-theory (enable fn-nntp-keyword-first-bytep
                                      fn-nntp-upcase-byte)))))

(local
 (defthm fn-proto-rest-byte-of-upcase
   (implies (fn-nntp-keyword-rest-bytep (fn-nntp-upcase-byte b))
            (fn-nntp-keyword-rest-bytep b))
   :hints (("Goal" :in-theory (enable fn-nntp-keyword-rest-bytep
                                      fn-nntp-keyword-first-bytep
                                      fn-nntp-upcase-byte)))))

(local
 (defthm fn-proto-tail-of-upcase
   (implies (fn-nntp-keyword-tailp (fn-nntp-upcase-keyword x))
            (fn-nntp-keyword-tailp x))
   :hints (("Goal" :in-theory (enable fn-nntp-keyword-tailp
                                      fn-nntp-upcase-keyword)))))

(local
 (defthm fn-proto-token-of-upcase
   (implies (fn-nntp-keyword-tokenp (fn-nntp-upcase-keyword x))
            (fn-nntp-keyword-tokenp x))
   :hints (("Goal" :in-theory (e/d (fn-nntp-keyword-tokenp fn-nntp-upcase-keyword)
                                   (fn-nntp-keyword-tailp))))))

(defthm fn-proto-keywordp-implies-keyword-token
  (implies (and (fn-nntp-keywordp keyword name)
                (syntaxp (quotep name))
                (fn-nntp-keyword-tokenp (fn-nntp-string-octets name)))
           (fn-nntp-keyword-tokenp keyword))
  :hints (("Goal" :in-theory (e/d (fn-nntp-keywordp)
                                  (fn-nntp-keyword-tokenp fn-nntp-upcase-keyword
                                   fn-nntp-string-octets))
           :use ((:instance fn-proto-token-of-upcase (x keyword))))))

; -----------------------------------------------------------------------------
; One theorem per row, generated from the table

(defconst *fn-proto-dispatch-theory*
  '(fn-nntp-command-pinned fn-nntp-archive-command-pinned
    fn-nntp-archive-command fn-nntp-session-command fn-nntp-archive-keywordp
    fn-nntp-xref-reply fn-rcompat-reply fn-rcompat-newgroups
    fn-rcompat-active-times fn-rcompat-retrieval-kind))

; The token recognizers stay closed in the row proofs: an arm for another
; command falls away by fn-proto-keywordp-exclusive, not by computing.
(defconst *fn-proto-token-theory*
  '(fn-nntp-keywordp fn-nntp-keyword-tokenp fn-nntp-upcase-keyword))

; Definitions no row's code depends on, which the HDR row otherwise opens
; while it simplifies the :fn-verified arm's lines (the verdict renderer and
; the decimal field): the builder lemmas already bound their codes.  Closed,
; the HDR row costs 134,580 prover steps instead of 2,238,607.
(defconst *fn-proto-closed-theory*
  '(fn-nntp-verdict-hdr-lines fn-stx-reader-item explode-nonnegative-integer))

(defun fn-proto-row-thm-name (name suffix)
  (declare (xargs :guard (and (stringp name) (stringp suffix))))
  (intern-in-package-of-symbol
   (concatenate 'string "FN-PROTO-ROW-" (string-upcase name) suffix)
   'fn-proto-within))

(defun fn-proto-row-events (alist)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp alist)
      (let ((name (car (car alist))) (codes (cdr (car alist))))
        (list*
         `(defthm ,(fn-proto-row-thm-name name "-CODES")
            (implies (fn-nntp-keywordp (car tokens) ,name)
                     (fn-proto-within
                      (fn-nntp-result-effects
                       (fn-nntp-command-pinned session archive index verdicts
                                               env tokens fn-arena))
                      ',codes))
            :hints (("Goal" :in-theory (e/d ,*fn-proto-dispatch-theory*
                                            ,(append *fn-proto-token-theory*
                                                     *fn-proto-closed-theory*)))))
         `(defthm ,(fn-proto-row-thm-name name "-LOOKUP")
            (implies (fn-nntp-keywordp keyword ,name)
                     (equal (fn-proto-reader-codes keyword) ',codes))
            :hints (("Goal" :in-theory (e/d (fn-proto-reader-codes-in)
                                            ,*fn-proto-token-theory*))))
         (fn-proto-row-events (cdr alist))))
    nil))

(defun fn-proto-not-any-row (alist term)
  (declare (xargs :guard t))
  (if (consp alist)
      (cons `(not (fn-nntp-keywordp ,term ,(and (consp (car alist)) (car (car alist)))))
            (fn-proto-not-any-row (cdr alist) term))
    nil))

(make-event (cons 'progn (fn-proto-row-events *fn-proto-reader-alist*)))

(make-event
 `(defthm fn-proto-row-unrecognized-codes
    (implies (and (fn-nntp-keyword-tokenp (car tokens))
                  ,@(fn-proto-not-any-row *fn-proto-reader-alist* '(car tokens)))
             (fn-proto-within
              (fn-nntp-result-effects
               (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena))
              ',*fn-proto-unrecognized-codes*))
    :hints (("Goal" :in-theory (e/d ,*fn-proto-dispatch-theory*
                                    ,*fn-proto-token-theory*)))))

(make-event
 `(defthm fn-proto-row-unrecognized-lookup
    (implies (and (fn-nntp-keyword-tokenp keyword)
                  ,@(fn-proto-not-any-row *fn-proto-reader-alist* 'keyword))
             (equal (fn-proto-reader-codes keyword) ',*fn-proto-unrecognized-codes*))
    :hints (("Goal" :in-theory (e/d (fn-proto-reader-codes-in) ,*fn-proto-token-theory*)))))

(defthm fn-proto-row-syntax-codes
  (implies (not (fn-nntp-keyword-tokenp (car tokens)))
           (fn-proto-within
            (fn-nntp-result-effects
             (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena))
            (fn-proto-reader-codes (car tokens))))
  :hints (("Goal" :in-theory (enable fn-nntp-command-pinned))))

