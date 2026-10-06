; fn: the tariff of a reply that is a few built lines (lane tariff4,
; 2026-10-04; planning/design/tariff-2026-10-04.md Q3).
;
; GROUP, NEXT and LAST answer one line built from the catalog's carried
; summary or the held metadata of a neighbour, never from payload octets
; (books/served-available-commands.lisp fn-av-nntp-group-result-cat,
; fn-av-nntp-next-or-last-cat: "STAT needs no payload pread").  The tariff
; is the cells that line conses: a measured per-octet cell count over the
; reply's octets, a fixed part for the session update and the result, and
; *fn-tariff-cons-octets* octets a cell (books/output-tariff-article.lisp).
;
;   fn-tariff-line-octets N = 16 * (10 * N + 32)
;
; The 10 is a stated representation constant, the figure's analogue of the
; ARTICLE tariff's 2 spines: building a reply of N octets from strings
; converts each string to octets (coerce + loop + reverse: at most 3 cells an
; octet), renders each number (explode + convert: at most 3), joins the
; pieces (reverse each onto an accumulator, then once more: 2), ends the
; line (append: 2) and, for a block, stuffs each line (3) and appends it
; (1); no octet takes all of these, so 10 bounds its cells.  It is NOT yet a derived bound: def-cost's :conses dimension cannot
; cost `coerce' or `explode-nonnegative-integer' (they are not in
; *fn-cost-cons-contracts*), so the derived twin of each factory leaves them
; unaccounted; PGO-TARIFF-LINE-REPLY-CONSES owes the theorem.  What IS
; proved here is the other half: the reply's octets, over the factory that
; runs, are within the bound the tariff multiplies.
(in-package "ACL2")
(include-book "output-tariff-article")
(include-book "served-available-commands")

(defconst *fn-tariff-line-spines* 10)
(defconst *fn-tariff-line-fixed-cells* 32)

(defun fn-tariff-line-octets (reply-octets)
  (declare (xargs :guard (natp reply-octets)))
  (* *fn-tariff-cons-octets*
     (+ (* *fn-tariff-line-spines* reply-octets) *fn-tariff-line-fixed-cells*)))

(defthm fn-tariff-line-octets-natp
  (implies (natp n) (natp (fn-tariff-line-octets n)))
  :rule-classes :type-prescription)

; The octets of the replies in a result's effects (a close carries none).
(defun fn-tariff-effects-octets (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (+ (if (and (consp (car effects)) (eq (car (car effects)) :reply)
                  (consp (cdr (car effects))) (true-listp (cadr (car effects))))
             (len (cadr (car effects)))
           0)
         (fn-tariff-effects-octets (cdr effects)))
    0))

(local
 (defthm fn-tariff-len-decimal-field
   (<= (len (fn-nntp-decimal-field n)) 10)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-nntp-decimal-field)))))

(local
 (defthm fn-tariff-len-string-octets-aux
   (equal (len (fn-nntp-string-octets-aux chars)) (len chars))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-tariff-len-string-octets
   (equal (len (fn-nntp-string-octets text))
          (if (stringp text) (length text) 0))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets)))))

(local
 (defthm fn-tariff-len-append-pieces
   (equal (len (fn-nntp-append-pieces pieces))
          (if (consp pieces)
              (+ (len (car pieces)) (len (fn-nntp-append-pieces (cdr pieces))))
            0))
   :hints (("Goal" :in-theory (enable fn-nntp-append-pieces)))))

(local
 (defthm fn-tariff-len-crlf
   (equal (len (fn-nntp-crlf line)) (+ 2 (len line)))
   :hints (("Goal" :in-theory (enable fn-nntp-crlf)))))

; GROUP: "211 count low high name" and CRLF: the four literal and
; separator octets, three fields of at most ten digits, the name; every
; other reply of the row (no such group, syntax) is shorter than the
; literal part.
(defun fn-tariff-group-reply-octets (namelen)
  (declare (xargs :guard (natp namelen)))
  (+ 39 namelen))

(defthm fn-tariff-group-reply-within-line
  (implies (stringp group)
           (<= (fn-tariff-effects-octets
                (fn-nntp-result-effects
                 (fn-av-nntp-group-result-cat session archive group v fn-cat)))
               (fn-tariff-group-reply-octets (length group))))
  :hints (("Goal" :in-theory (e/d (fn-av-nntp-group-result-cat fn-av-scat-group-initial
                                   fn-nntp-make-result fn-nntp-result-effects
                                   fn-nntp-reply-effect fn-nntp-single
                                   fn-tariff-group-reply-octets fn-tariff-effects-octets)
                                  (fn-scat-available-summary fn-scat-available-low
                                   fn-nntp-set-cursor)))))

; The name the row's argument names, in octets: the argument token's length
; bounds the string it denotes.
(defun fn-tariff-group-name-octets (args)
  (declare (xargs :guard t))
  (if (consp args) (len (car args)) 0))

(defthm fn-tariff-group-token-string-within-token
  (<= (length (fn-nntp-token-string token)) (len token))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-nntp-token-string fn-nntp-octets-chars))))

; NEXT and LAST: "223 n <msgid> retrieved" and CRLF, within the initial line
; of the retrieval family (books/output-tariff-article.lisp), the message-id
; bounded by the kept-row test the factory makes.  A session that selects a
; group with a current article that is no natural (none the reader machine
; builds) falls to the raw model, outside this bound.
(defthm fn-tariff-neighbour-reply-within-line
  (implies (fn-nntp-sessionp session)
           (<= (fn-tariff-effects-octets
                (fn-nntp-result-effects
                 (fn-av-nntp-next-or-last-cat session archive direction v fn-arena fn-cat)))
               *fn-tariff-article-initial-octets*))
  :hints (("Goal" :in-theory (e/d (fn-av-nntp-next-or-last-cat fn-nntp-make-result
                                   fn-nntp-result-effects fn-nntp-reply-effect fn-nntp-single
                                   fn-tariff-effects-octets fn-nntp-retrieval-initial
                                   fn-scv-keptp fn-av-held-article fn-scat-msgid-idp
                                   fn-make-article fn-article-msgid fn-nntp-next-or-last
                                   fn-nntp-sessionp)
                                  (fn-scat-available-next-number
                                   fn-scat-available-previous-number fn-nntp-set-cursor)))))

; The session-level commands (books/nntp.lisp fn-nntp-session-command, the
; arm the served step refines): DATE, MODE and QUIT answer one literal or
; fixed-width line, HELP one fixed block.  64 octets holds every reply of
; those three (the longest literal is "503 clock reading outside the
; representable range"); HELP's block is 248 octets whatever the session.
(defconst *fn-tariff-session-line-octets* 64)
(defconst *fn-tariff-help-reply-octets* 248)

(local
 (defthm fn-tariff-len-pad2
   (equal (len (fn-nntp-pad2 n)) 2)
   :hints (("Goal" :in-theory (enable fn-nntp-pad2)))))

(local
 (defthm fn-tariff-len-pad4
   (equal (len (fn-nntp-pad4 n)) 4)
   :hints (("Goal" :in-theory (enable fn-nntp-pad4)))))

(defthm fn-tariff-date-reply-within-line
  (implies (fn-nntp-keywordp keyword "DATE")
           (<= (fn-tariff-effects-octets
                (fn-nntp-result-effects (fn-nntp-session-command session env keyword args)))
               *fn-tariff-session-line-octets*))
  :hints (("Goal" :in-theory (e/d (fn-nntp-session-command fn-nntp-date-response
                                   fn-nntp-date-octets fn-nntp-make-result
                                   fn-nntp-result-effects fn-nntp-reply-effect
                                   fn-nntp-single fn-tariff-effects-octets)
                                  (fn-nntp-pad4 fn-nntp-pad2)))))

(defthm fn-tariff-mode-reply-within-line
  (implies (fn-nntp-keywordp keyword "MODE")
           (<= (fn-tariff-effects-octets
                (fn-nntp-result-effects (fn-nntp-session-command session env keyword args)))
               *fn-tariff-session-line-octets*))
  :hints (("Goal" :in-theory (enable fn-nntp-session-command fn-nntp-mode-response
                                     fn-nntp-make-result fn-nntp-result-effects
                                     fn-nntp-reply-effect fn-nntp-single
                                     fn-tariff-effects-octets fn-nntp-close-effect))))

(defthm fn-tariff-quit-reply-within-line
  (implies (fn-nntp-keywordp keyword "QUIT")
           (<= (fn-tariff-effects-octets
                (fn-nntp-result-effects (fn-nntp-session-command session env keyword args)))
               *fn-tariff-session-line-octets*))
  :hints (("Goal" :in-theory (enable fn-nntp-session-command fn-nntp-make-result
                                     fn-nntp-result-effects fn-nntp-reply-effect
                                     fn-nntp-single fn-tariff-effects-octets
                                     fn-nntp-close-effect))))

(defthm fn-tariff-help-reply-within-block
  (implies (fn-nntp-keywordp keyword "HELP")
           (<= (fn-tariff-effects-octets
                (fn-nntp-result-effects (fn-nntp-session-command session env keyword args)))
               *fn-tariff-help-reply-octets*))
  :hints (("Goal" :in-theory (enable fn-nntp-session-command fn-nntp-help fn-nntp-multi
                                     fn-nntp-make-result fn-nntp-result-effects
                                     fn-nntp-reply-effect fn-nntp-single
                                     fn-tariff-effects-octets))))
