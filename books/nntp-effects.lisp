; Effect typing for the experimental fn NNTP reader.
;
; An effect is not merely a two-element list with octets in it.  A reply is
; re-parsed here as a protocol response: a three-digit status indicator
; followed by SP or by CRLF (RFC 3977 section 3.2), an initial line of at most
; 512 octets including its CRLF (section 3.1), and, when the response is
; multi-line, a dot-stuffed block terminated by the five octets CRLF "." CRLF
; that carries none of NUL, bare LF, or bare CR (section 3.1.1).  The scanner
; below is independent of the response constructors: it reads the emitted
; octets back.
(in-package "ACL2")
(include-book "nntp-invariants")
(include-book "nntp-overview")

; The five books of the nntp cluster withdraw their definitions at their
; export events (2026-09-19 split of books/nntp.lisp); this book reasons
; about the transitions, so it re-enables exactly them, locally.
(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary
                          fn-nntp-vocabulary)))
(local (in-theory (enable fn-statep fn-articlep fn-pendingp)))

; The consp- and true-listp-backchaining rules books/article.lisp and
; books/wildmat.lisp export enabled fan every (consp X) and (true-listp X)
; out through their recursive recognizers (nntp-invariants, same list, with
; the accumulated-persistence figures); the -is-response-text theorems here
; ran past 40M prover steps under them on 2026-09-20.  Withdrawn by name; the
; owning books should withdraw them at their exports (docs/proof-style.md
; section 8).
(local (in-theory (disable fn-article-nonempty-true-list-is-consp
                           fn-article-field-list-true-listp
                           fn-article-header-bytes-true-listp
                           fn-article-octet-list-true-listp
                           fn-wildmat-guard-items-p-true-listp
                           fn-wildmat-guard-octet-listp-true-listp)))

; -----------------------------------------------------------------------------
; The response grammar

(defun fn-nntp-response-octetp (byte)
  ; RFC 3977 section 3.1.1: a block carries no NUL, LF, or CR apart from the
  ; line endings themselves.  The same restriction keeps an initial line from
  ; splitting into two responses.
  (and (integerp byte) (<= 1 byte) (<= byte 255)
       (not (equal byte 13)) (not (equal byte 10))))

(defun fn-nntp-response-textp (bytes)
  (if (consp bytes)
      (and (fn-nntp-response-octetp (car bytes))
           (fn-nntp-response-textp (cdr bytes)))
    (null bytes)))

(defun fn-nntp-block-textp (lines)
  (if (consp lines)
      (and (fn-nntp-response-textp (car lines))
           (fn-nntp-block-textp (cdr lines)))
    (null lines)))

; Three decimal digits, then SP or the terminating CRLF.
(defun fn-nntp-status-prefixp (bytes)
  (and (consp bytes) (consp (cdr bytes)) (consp (cdr (cdr bytes)))
       (fn-nntp-decimal-digitp (car bytes))
       (fn-nntp-decimal-digitp (car (cdr bytes)))
       (fn-nntp-decimal-digitp (car (cdr (cdr bytes))))
       (let ((rest (cdr (cdr (cdr bytes)))))
         (and (consp rest)
              (or (equal (car rest) 32)
                  (and (equal (car rest) 13)
                       (consp (cdr rest))
                       (equal (car (cdr rest)) 10)))))))

; The same shape, stated about an initial line that does not yet carry CRLF.
(defun fn-nntp-initial-status-linep (line)
  (and (consp line) (consp (cdr line)) (consp (cdr (cdr line)))
       (fn-nntp-decimal-digitp (car line))
       (fn-nntp-decimal-digitp (car (cdr line)))
       (fn-nntp-decimal-digitp (car (cdr (cdr line))))
       (or (null (cdr (cdr (cdr line))))
           (equal (car (cdr (cdr (cdr line)))) 32))))

; `seen` counts the octets already accepted on the initial line.  The CRLF pair
; is charged to the 512-octet limit, as RFC 3977 section 3.1 requires.
(defun fn-nntp-initial-line-tail (bytes seen)
  (if (consp bytes)
      (if (equal (car bytes) 13)
          (if (and (consp (cdr bytes))
                   (equal (car (cdr bytes)) 10)
                   (<= (+ seen 2) *fn-nntp-max-response-octets*))
              (list :ok (cdr (cdr bytes)))
            (list :error))
        (if (fn-nntp-response-octetp (car bytes))
            (fn-nntp-initial-line-tail (cdr bytes) (+ 1 seen))
          (list :error)))
    (list :error)))

; `startp` is true at the start of a block line.  A line whose first octet is
; the termination octet is either the terminating line, which must end the
; reply, or a dot-stuffed content line.
(defun fn-nntp-block-scan (bytes startp)
  (declare (xargs :measure (+ (* 2 (acl2-count bytes)) (if startp 1 0))))
  (if (not (consp bytes))
      nil
    (if startp
        (if (equal (car bytes) 46)
            (if (and (consp (cdr bytes)) (equal (car (cdr bytes)) 13))
                (and (consp (cdr (cdr bytes)))
                     (equal (car (cdr (cdr bytes))) 10)
                     (null (cdr (cdr (cdr bytes)))))
              (and (consp (cdr bytes))
                   (equal (car (cdr bytes)) 46)
                   (fn-nntp-block-scan (cdr (cdr bytes)) nil)))
          (fn-nntp-block-scan bytes nil))
      (if (equal (car bytes) 13)
          (and (consp (cdr bytes))
               (equal (car (cdr bytes)) 10)
               (fn-nntp-block-scan (cdr (cdr bytes)) t))
        (and (fn-nntp-response-octetp (car bytes))
             (fn-nntp-block-scan (cdr bytes) nil))))))

(defun fn-nntp-replyp (octets)
  (and (fn-nntp-status-prefixp octets)
       (let ((tail (fn-nntp-initial-line-tail octets 0)))
         (and (equal (car tail) :ok)
              (let ((rest (car (cdr tail))))
                (if (null rest) t (fn-nntp-block-scan rest t)))))))

; A reply is a well-formed protocol response carried as octets; close has no
; payload.  This is the concrete effect vocabulary emitted by books/nntp.lisp.
(defun fn-nntp-effectp (effect)
  (or (and (true-listp effect)
           (equal (len effect) 2)
           (equal (car effect) :reply)
           (fn-octet-listp (car (cdr effect)))
           (fn-nntp-replyp (car (cdr effect))))
      (equal effect (fn-nntp-close-effect))
      ; POST (RFC 3977 section 6.3.1) changes the framing mode rather than
      ; emitting octets: the host applies this one by calling
      ; fn-wire-begin-article.  It carries no payload, so nothing about it can
      ; be malformed; books/nntp-post.lisp is what reads it.
      (equal effect (fn-nntp-begin-article-effect))))

(defun fn-nntp-effectsp (effects)
  (if (consp effects)
      (and (fn-nntp-effectp (car effects))
           (fn-nntp-effectsp (cdr effects)))
    (null effects)))

; -----------------------------------------------------------------------------
; Octet-shape facts, kept below the response constructors

(local (defthm fn-nntp-len-of-append-lemma
         (equal (len (append x y)) (+ (len x) (len y)))))

(local (defthm fn-nntp-append-associates-lemma
         (equal (append (append x y) z) (append x (append y z)))))

(defthm fn-nntp-effects-octet-listp-append
  (implies (and (fn-octet-listp x)
                (fn-octet-listp y))
           (fn-octet-listp (append x y))))

(defthm fn-nntp-effects-octet-listp-revappend
  (implies (and (fn-octet-listp x)
                (fn-octet-listp accumulator))
           (fn-octet-listp (revappend x accumulator))))

(defthm fn-nntp-effects-octet-listp-reverse
  (implies (fn-octet-listp x)
           (fn-octet-listp (reverse x)))
  :hints (("Goal" :in-theory (enable reverse))))

; std/lists/rev (books/article.lisp:13) rewrites the (revappend x nil) that
; reverse opens to into (rev x), so every reverse inside an opened
; fn-nntp-crlf-lines-aux reaches a proof as rev and the lemma above cannot
; match it (certify-20260920T010731Z-93121).  The same lemma in that normal
; form, from the one above.
(defthm fn-nntp-effects-octet-listp-rev
  (implies (fn-octet-listp x)
           (fn-octet-listp (rev x)))
  :hints (("Goal" :use fn-nntp-effects-octet-listp-reverse :in-theory (e/d (reverse) (fn-nntp-effects-octet-listp-reverse)))))

(defthm fn-nntp-effects-string-octets-aux
  (implies (character-listp chars)
           (fn-octet-listp (fn-nntp-string-octets-aux chars))))

(defthm fn-nntp-effects-string-octets
  (fn-octet-listp (fn-nntp-string-octets text))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets))))

(defthm fn-nntp-effects-string-octets-true-listp
  (true-listp (fn-nntp-string-octets text))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets))))

(defthm fn-nntp-effects-decimal-characters-aux
  (implies (and (natp number)
                (character-listp accumulator))
           (character-listp
            (explode-nonnegative-integer number 10 accumulator))))

(defthm fn-nntp-effects-decimal-characters
  (implies (natp number)
           (character-listp (explode-nonnegative-integer number 10 nil))))

(defthm fn-nntp-effects-decimal-rev-octets
  (implies (natp number)
           (fn-octet-listp (fn-nntp-decimal-rev number)))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-rev)
                   :use ((:instance fn-nntp-effects-string-octets-aux
                                    (chars (explode-nonnegative-integer
                                            number 10 nil)))))))

(defthm fn-nntp-effects-decimal-octets
  (fn-octet-listp (fn-nntp-decimal number))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal))))

; -----------------------------------------------------------------------------
; Decimal fields are bounded digit runs by construction

(defthm fn-nntp-decimal-field-is-a-digit-run
  (fn-nntp-decimal-tokenp (fn-nntp-decimal-field number))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-field))))

(defthm fn-nntp-decimal-field-is-nonempty
  (consp (fn-nntp-decimal-field number))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-field))))

(defthm fn-nntp-decimal-field-is-bounded
  (<= (len (fn-nntp-decimal-field number)) *fn-nntp-max-decimal-octets*)
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-field))))

(defthm fn-nntp-decimal-field-is-octets
  (fn-octet-listp (fn-nntp-decimal-field number))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-field))))

(defthm fn-nntp-decimal-field-is-true-listp
  (true-listp (fn-nntp-decimal-field number))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-field))))

(defthm fn-nntp-decimal-token-is-response-text
  (implies (and (fn-nntp-decimal-tokenp octets) (true-listp octets))
           (fn-nntp-response-textp octets)))

(defthm fn-nntp-decimal-field-is-response-text
  (fn-nntp-response-textp (fn-nntp-decimal-field number))
  :hints (("Goal" :use ((:instance fn-nntp-decimal-token-is-response-text
                         (octets (fn-nntp-decimal-field number)))))))

(defthm fn-nntp-decimal-field-first-is-digit
  (fn-nntp-decimal-digitp (car (fn-nntp-decimal-field number)))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-field))))

; -----------------------------------------------------------------------------
; Printable projected data is response text

(defthm fn-nntp-printable-token-is-response-text
  (implies (and (fn-nntp-printable-tokenp octets) (true-listp octets))
           (fn-nntp-response-textp octets)))

(defthm fn-nntp-response-text-of-append
  (implies (and (fn-nntp-response-textp x) (fn-nntp-response-textp y))
           (fn-nntp-response-textp (append x y))))

(defthm fn-nntp-response-text-true-listp
  (implies (fn-nntp-response-textp x) (true-listp x)))

(defthm fn-nntp-safe-group-name-is-response-text
  (implies (fn-nntp-safe-group-namep group)
           (fn-nntp-response-textp (fn-nntp-string-octets group)))
  :hints (("Goal" :in-theory (enable fn-nntp-safe-group-namep))))

(defthm fn-nntp-safe-group-name-is-bounded
  (implies (fn-nntp-safe-group-namep group)
           (<= (len (fn-nntp-string-octets group)) *fn-nntp-max-group-octets*))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-nntp-safe-group-namep))))

(defthm fn-nntp-safe-group-list-member
  (implies (and (fn-nntp-safe-group-listp groups)
                (member-equal group groups))
           (fn-nntp-safe-group-namep group))
  :hints (("Goal" :induct (fn-nntp-safe-group-listp groups))))

(defthm fn-nntp-projection-groups-are-safe
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-safe-group-listp (fn-state-groups archive)))
  :hints (("Goal" :in-theory (enable fn-nntp-projectionp))))

(defthm fn-nntp-projected-group-is-safe
  (implies (and (fn-nntp-projectionp archive)
                (member-equal group (fn-state-groups archive)))
           (fn-nntp-safe-group-namep group))
  :hints (("Goal" :in-theory (enable fn-nntp-projectionp))))

(defthm fn-nntp-filter-groups-keeps-safe-list
  (implies (fn-nntp-safe-group-listp groups)
           (fn-nntp-safe-group-listp
            (fn-nntp-filter-groups-by-wildmat patterns groups)))
  :hints (("Goal" :induct (fn-nntp-filter-groups-by-wildmat patterns groups)
           :in-theory (e/d (fn-nntp-filter-groups-by-wildmat)
                           (fn-nntp-group-matches-parsed-wildmatp)))))

(defthm fn-nntp-message-id-tail-is-true-listp
  (implies (fn-nntp-message-id-tailp tail) (true-listp tail))
  :hints (("Goal" :induct (fn-nntp-message-id-tailp tail))))

(defthm fn-nntp-message-id-token-is-response-text
  (implies (fn-nntp-message-id-tokenp octets)
           (fn-nntp-response-textp octets))
  :hints (("Goal" :in-theory (enable fn-nntp-message-id-tokenp)
           :use ((:instance fn-nntp-printable-token-is-response-text)))))

(defthm fn-nntp-article-id-is-response-text
  (implies (fn-nntp-article-idp article)
           (fn-nntp-response-textp
            (fn-nntp-string-octets (fn-article-msgid article))))
  :hints (("Goal" :in-theory (enable fn-nntp-article-idp))))

(defthm fn-nntp-article-id-is-bounded
  (implies (fn-nntp-article-idp article)
           (<= (len (fn-nntp-string-octets (fn-article-msgid article)))
               *fn-nntp-max-message-id-octets*))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-nntp-article-idp
                                     fn-nntp-message-id-tokenp))))

; -----------------------------------------------------------------------------
; The block a multi-line response carries

(defthm fn-nntp-block-textp-revappend
  (implies (and (fn-nntp-block-textp x) (fn-nntp-block-textp accumulator))
           (fn-nntp-block-textp (revappend x accumulator))))

(defthm fn-nntp-block-textp-reverse
  (implies (fn-nntp-block-textp x) (fn-nntp-block-textp (reverse x)))
  :hints (("Goal" :in-theory (enable reverse))))

; std/lists/rev (books/article.lisp:13) rewrites the (revappend x nil) that
; reverse opens to into (rev x), so every reverse inside an opened
; fn-nntp-crlf-lines-aux reaches a proof as rev and the lemma above cannot
; match it (certify-20260920T010731Z-93121).  The same lemma in that normal
; form, from the one above.
(defthm fn-nntp-block-textp-rev
  (implies (fn-nntp-block-textp x) (fn-nntp-block-textp (rev x)))
  :hints (("Goal" :use fn-nntp-block-textp-reverse :in-theory (e/d (reverse) (fn-nntp-block-textp-reverse)))))

(defthm fn-nntp-response-textp-revappend
  (implies (and (fn-nntp-response-textp x) (fn-nntp-response-textp accumulator))
           (fn-nntp-response-textp (revappend x accumulator))))

(defthm fn-nntp-response-textp-reverse
  (implies (fn-nntp-response-textp x) (fn-nntp-response-textp (reverse x)))
  :hints (("Goal" :in-theory (enable reverse))))

; std/lists/rev (books/article.lisp:13) rewrites the (revappend x nil) that
; reverse opens to into (rev x), so every reverse inside an opened
; fn-nntp-crlf-lines-aux reaches a proof as rev and the lemma above cannot
; match it (certify-20260920T010731Z-93121).  The same lemma in that normal
; form, from the one above.
(defthm fn-nntp-response-textp-rev
  (implies (fn-nntp-response-textp x) (fn-nntp-response-textp (rev x)))
  :hints (("Goal" :use fn-nntp-response-textp-reverse :in-theory (e/d (reverse) (fn-nntp-response-textp-reverse)))))

(defthm fn-nntp-crlf-lines-aux-is-response-text
  (implies (and (fn-octet-listp bytes)
                (fn-nntp-response-textp line-rev)
                (fn-nntp-block-textp lines-rev)
                (equal (car (fn-nntp-crlf-lines-aux bytes line-rev lines-rev)) :ok))
           (fn-nntp-block-textp
            (car (cdr (fn-nntp-crlf-lines-aux bytes line-rev lines-rev)))))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf-lines-aux
                                     fn-nntp-block-textp
                                     fn-nntp-response-textp))))

(defthm fn-nntp-crlf-lines-is-response-text
  (implies (equal (car (fn-nntp-crlf-lines bytes)) :ok)
           (fn-nntp-block-textp (car (cdr (fn-nntp-crlf-lines bytes)))))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf-lines))))

(defthm fn-nntp-article-section-is-response-text
  (implies (equal (car (fn-nntp-article-section article kind)) :ok)
           (fn-nntp-block-textp
            (car (cdr (fn-nntp-article-section article kind)))))
  :hints (("Goal" :in-theory (enable fn-nntp-article-section))))

(defthm fn-nntp-number-lines-are-response-text
  (fn-nntp-block-textp (fn-nntp-number-lines numbers))
  :hints (("Goal" :in-theory (enable fn-nntp-number-lines
                                     fn-nntp-block-textp))))

(defthm fn-nntp-active-line-is-response-text
  (implies (fn-nntp-safe-group-namep group)
           (fn-nntp-response-textp (fn-nntp-active-line archive group)))
  :hints (("Goal" :in-theory (enable fn-nntp-active-line
                                     fn-nntp-append-pieces))))

(defthm fn-nntp-active-lines-are-response-text
  (implies (fn-nntp-safe-group-listp groups)
           (fn-nntp-block-textp (fn-nntp-active-lines archive groups)))
  :hints (("Goal" :induct (fn-nntp-active-lines archive groups)
           :in-theory (e/d (fn-nntp-active-lines fn-nntp-block-textp
                            fn-nntp-safe-group-listp)
                           (fn-nntp-active-line)))))

(defthm fn-nntp-newsgroup-lines-are-response-text
  (implies (fn-nntp-safe-group-listp groups)
           (fn-nntp-block-textp (fn-nntp-newsgroup-lines groups)))
  :hints (("Goal" :induct (fn-nntp-newsgroup-lines groups)
           :in-theory (enable fn-nntp-newsgroup-lines fn-nntp-block-textp
                              fn-nntp-safe-group-listp
                              fn-nntp-append-pieces))))

; -----------------------------------------------------------------------------
; Reading an emitted response back

(local
 (defun fn-nntp-text-seen-induction (line seen)
   (if (consp line)
       (fn-nntp-text-seen-induction (cdr line) (+ 1 seen))
     (list line seen))))

(defthm fn-nntp-initial-line-tail-of-text
  (implies (and (fn-nntp-response-textp line)
                (natp seen)
                (<= (+ seen (len line) 2) *fn-nntp-max-response-octets*))
           (equal (fn-nntp-initial-line-tail
                   (append line (cons 13 (cons 10 rest))) seen)
                  (list :ok rest)))
  :hints (("Goal" :induct (fn-nntp-text-seen-induction line seen)
           :in-theory (enable fn-nntp-initial-line-tail
                              fn-nntp-response-textp))))

(defthm fn-nntp-status-prefix-of-append
  (implies (fn-nntp-initial-status-linep line)
           (fn-nntp-status-prefixp (append line (cons 13 (cons 10 rest)))))
  :hints (("Goal" :in-theory (enable fn-nntp-status-prefixp
                                     fn-nntp-initial-status-linep))))

(defthm fn-nntp-block-scan-of-text-line
  (implies (fn-nntp-response-textp body)
           (equal (fn-nntp-block-scan (append body (cons 13 (cons 10 rest))) nil)
                  (fn-nntp-block-scan rest t)))
  :hints (("Goal" :induct (fn-nntp-response-textp body)
           :in-theory (enable fn-nntp-response-textp))))

; A block scan that is at the start of a line and does not see a dot there is
; the same scan in mid-line mode.  Stated separately because the start flag is
; what makes `fn-nntp-block-scan' resist the induction suggested by
; `fn-nntp-response-textp': the induction hypothesis arrives in mid-line mode
; and the goal is in start mode.
(defthm fn-nntp-block-scan-start-without-a-dot
  (implies (not (equal (car bytes) 46))
           (equal (fn-nntp-block-scan bytes t)
                  (fn-nntp-block-scan bytes nil)))
  :hints (("Goal" :expand ((fn-nntp-block-scan bytes t)))))

(defthm fn-nntp-block-scan-of-stuffed-line
  (implies (fn-nntp-response-textp line)
           (equal (fn-nntp-block-scan
                   (append (fn-nntp-crlf (fn-wire-stuff-line line)) rest) t)
                  (fn-nntp-block-scan rest t)))
  :hints (("Goal"
           :do-not-induct t
           :cases ((equal (car line) 46) (not (consp line)))
           :in-theory (e/d (fn-nntp-crlf fn-wire-stuff-line)
                           (fn-nntp-response-textp))
           :expand ((:free (x) (fn-nntp-block-scan (cons 46 x) t))
                    (:free (x) (fn-nntp-block-scan (cons 13 x) nil))
                    (fn-nntp-response-textp line)))))

(defthm fn-nntp-block-scan-of-stuff-lines
  (implies (fn-nntp-block-textp lines)
           (fn-nntp-block-scan
            (append (fn-nntp-stuff-lines lines) '(46 13 10)) t))
  :hints (("Goal" :induct (fn-nntp-block-textp lines)
           :in-theory (e/d (fn-nntp-stuff-lines fn-nntp-block-textp)
                           (fn-nntp-crlf fn-wire-stuff-line)))))

(defthm fn-nntp-replyp-of-single-line
  (implies (and (fn-nntp-response-textp line)
                (fn-nntp-initial-status-linep line)
                (<= (+ (len line) 2) *fn-nntp-max-response-octets*))
           (fn-nntp-replyp (fn-nntp-crlf line)))
  ;; The two re-parse rules are stated over `(append line (cons 13 (cons 10
  ;; rest)))'.  Any induction destructures that append and the rules stop
  ;; matching, so the line predicates stay closed and the goal is discharged by
  ;; rewriting alone.
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-nntp-replyp fn-nntp-crlf)
                           (fn-nntp-initial-line-tail
                            fn-nntp-status-prefixp
                            fn-nntp-initial-status-linep
                            fn-nntp-response-textp)))))

(defthm fn-nntp-replyp-of-block
  (implies (and (fn-nntp-response-textp line)
                (fn-nntp-initial-status-linep line)
                (<= (+ (len line) 2) *fn-nntp-max-response-octets*)
                (fn-nntp-block-textp lines))
           (fn-nntp-replyp (append (fn-nntp-crlf line)
                                   (append (fn-nntp-stuff-lines lines)
                                           '(46 13 10)))))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-replyp fn-nntp-crlf)
                           (fn-nntp-initial-line-tail
                            fn-nntp-status-prefixp
                            fn-nntp-initial-status-linep
                            fn-nntp-response-textp
                            fn-nntp-block-textp
                            fn-nntp-block-scan
                            fn-nntp-stuff-lines)))))

; -----------------------------------------------------------------------------
; The response constructors

(defthm fn-nntp-effects-reply-effect
  (implies (and (fn-octet-listp octets) (fn-nntp-replyp octets))
           (fn-nntp-effectp (fn-nntp-reply-effect octets)))
  :hints (("Goal" :in-theory (enable fn-nntp-effectp fn-nntp-reply-effect))))

(defthm fn-nntp-effects-of-make-result
  (equal (fn-nntp-result-effects (fn-nntp-make-result session effects))
         effects))

(defthm fn-nntp-effects-crlf-octets
  (implies (fn-octet-listp line)
           (fn-octet-listp (fn-nntp-crlf line)))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf))))

(defthm fn-nntp-effects-wire-stuff-line-octets
  (implies (fn-octet-listp line)
           (fn-octet-listp (fn-wire-stuff-line line)))
  :hints (("Goal" :in-theory (enable fn-wire-stuff-line))))

(defun fn-nntp-octet-linesp (lines)
  (if (consp lines)
      (and (fn-octet-listp (car lines))
           (fn-nntp-octet-linesp (cdr lines)))
    (null lines)))

(defthm fn-nntp-block-text-is-octet-lines
  (implies (fn-nntp-block-textp lines)
           (fn-nntp-octet-linesp lines))
  :hints (("Goal" :induct (fn-nntp-block-textp lines)
           :in-theory (enable fn-nntp-block-textp fn-nntp-octet-linesp))))

(defthm fn-nntp-effects-stuff-lines-octets
  (implies (fn-nntp-octet-linesp lines)
           (fn-octet-listp (fn-nntp-stuff-lines lines)))
  :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines
                                     fn-nntp-octet-linesp))))

(defthm fn-nntp-effects-append-pieces-octets
  (implies (fn-nntp-octet-linesp pieces)
           (fn-octet-listp (fn-nntp-append-pieces pieces)))
  :hints (("Goal" :in-theory (enable fn-nntp-append-pieces
                                     fn-nntp-octet-linesp))))

(defthm fn-nntp-response-text-is-octets
  (implies (fn-nntp-response-textp bytes) (fn-octet-listp bytes)))

(defthm fn-nntp-effects-single
  (implies (and (fn-nntp-response-textp (fn-nntp-string-octets text))
                (fn-nntp-initial-status-linep (fn-nntp-string-octets text))
                (<= (+ (len (fn-nntp-string-octets text)) 2)
                    *fn-nntp-max-response-octets*))
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-single session text))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-single fn-nntp-effectsp)
                                  (fn-nntp-replyp fn-nntp-crlf
                                   fn-nntp-initial-status-linep
                                   fn-nntp-response-textp)))))

(defthm fn-nntp-effects-multi-octets
  (implies (and (fn-nntp-response-textp initial)
                (fn-nntp-initial-status-linep initial)
                (<= (+ (len initial) 2) *fn-nntp-max-response-octets*)
                (fn-nntp-block-textp lines))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-multi-octets session initial lines))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-multi-octets fn-nntp-effectsp)
                                  (fn-nntp-replyp fn-nntp-crlf
                                   fn-nntp-stuff-lines
                                   fn-nntp-initial-status-linep
                                   fn-nntp-response-textp
                                   fn-nntp-block-textp)))))

(defthm fn-nntp-effects-multi
  (implies (and (fn-nntp-response-textp (fn-nntp-string-octets initial))
                (fn-nntp-initial-status-linep (fn-nntp-string-octets initial))
                (<= (+ (len (fn-nntp-string-octets initial)) 2)
                    *fn-nntp-max-response-octets*)
                (fn-nntp-block-textp lines))
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-multi session initial lines))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-multi fn-nntp-effectsp)
                                  (fn-nntp-replyp fn-nntp-crlf
                                   fn-nntp-stuff-lines
                                   fn-nntp-initial-status-linep
                                   fn-nntp-response-textp
                                   fn-nntp-block-textp)))))

; -----------------------------------------------------------------------------
; Every generated initial line fits inside RFC 3977 section 3.1's 512 octets

(defthm fn-nntp-group-initial-is-response-text
  (implies (fn-nntp-safe-group-namep group)
           (fn-nntp-response-textp (fn-nntp-group-initial archive group)))
  :hints (("Goal" :in-theory (enable fn-nntp-group-initial
                                     fn-nntp-append-pieces))))

(defthm fn-nntp-group-initial-is-a-status-line
  (fn-nntp-initial-status-linep (fn-nntp-group-initial archive group))
  :hints (("Goal" :in-theory (enable fn-nntp-group-initial
                                     fn-nntp-initial-status-linep
                                     fn-nntp-append-pieces))))

; 4 status octets, three decimal fields of at most ten octets, three separating
; spaces, and a group name of at most 460 octets: 497, and 510 once LISTGROUP
; adds " list follows".  Both are inside 512 once CRLF is charged.
(defthm fn-nntp-group-initial-fits
  (implies (fn-nntp-safe-group-namep group)
           (<= (+ (len (fn-nntp-group-initial archive group)) 2)
               *fn-nntp-max-response-octets*))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-nntp-group-initial
                                     fn-nntp-append-pieces))))

(defthm fn-nntp-listgroup-initial-is-response-text
  (implies (fn-nntp-safe-group-namep group)
           (fn-nntp-response-textp (fn-nntp-listgroup-initial archive group)))
  :hints (("Goal" :in-theory (enable fn-nntp-listgroup-initial))))

(defthm fn-nntp-listgroup-initial-is-a-status-line
  (fn-nntp-initial-status-linep (fn-nntp-listgroup-initial archive group))
  :hints (("Goal" :in-theory (e/d (fn-nntp-listgroup-initial
                                   fn-nntp-group-initial
                                   fn-nntp-initial-status-linep
                                   fn-nntp-append-pieces)
                                  ()))))

(defthm fn-nntp-listgroup-initial-fits
  (implies (fn-nntp-safe-group-namep group)
           (<= (+ (len (fn-nntp-listgroup-initial archive group)) 2)
               *fn-nntp-max-response-octets*))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-nntp-listgroup-initial
                                     fn-nntp-group-initial
                                     fn-nntp-append-pieces))))

(defthm fn-nntp-retrieval-initial-is-response-text
  (implies (fn-nntp-article-idp article)
           (fn-nntp-response-textp
            (fn-nntp-retrieval-initial kind number article)))
  :hints (("Goal" :in-theory (enable fn-nntp-retrieval-initial
                                     fn-nntp-append-pieces))))

(defthm fn-nntp-retrieval-initial-is-a-status-line
  (fn-nntp-initial-status-linep (fn-nntp-retrieval-initial kind number article))
  :hints (("Goal" :in-theory (enable fn-nntp-retrieval-initial
                                     fn-nntp-initial-status-linep
                                     fn-nntp-append-pieces))))

(defthm fn-nntp-retrieval-initial-fits
  (implies (fn-nntp-article-idp article)
           (<= (+ (len (fn-nntp-retrieval-initial kind number article)) 2)
               *fn-nntp-max-response-octets*))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-nntp-retrieval-initial
                                     fn-nntp-append-pieces))))

; -----------------------------------------------------------------------------
; Branch by branch

(in-theory (disable fn-nntp-result-effects
                    fn-nntp-make-result fn-nntp-reply-effect
                    fn-nntp-single fn-nntp-multi fn-nntp-multi-octets
                    fn-nntp-group-result fn-nntp-listgroup-result
                    fn-nntp-article-response
                    fn-nntp-group-initial fn-nntp-listgroup-initial
                    fn-nntp-retrieval-initial
                    fn-nntp-list-active fn-nntp-list-newsgroups))

(defthm fn-nntp-effects-group-result
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-group-result session archive group))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-group-result fn-nntp-effectsp)
                                  (fn-nntp-reply-effect fn-nntp-crlf
                                   fn-nntp-set-cursor
                                   fn-nntp-make-result)))))

(defthm fn-nntp-effects-listgroup-result
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-listgroup-result session archive group range))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-listgroup-result)
                                  (fn-nntp-set-cursor
                                   fn-nntp-group-range-numbers)))))

(defthm fn-nntp-effects-listgroup-command
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-listgroup-command session archive args))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-listgroup-command)
                (fn-nntp-listgroup-result fn-nntp-single
                 fn-nntp-parse-range fn-nntp-token-string
                 fn-nntp-result-effects)))))

(defthm fn-nntp-effects-article-response
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-article-response session article number kind updatep group)))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-article-response fn-nntp-effectsp)
                (fn-nntp-article-section
                 fn-nntp-stuff-lines
                 fn-nntp-crlf
                 fn-nntp-set-cursor
                 fn-nntp-decimal-field
                 fn-nntp-string-octets)))))

(defthm fn-nntp-effects-current-retrieval
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-current-retrieval session archive kind)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-current-retrieval)
                                  (fn-nntp-article-response
                                   fn-nntp-available-article)))))

(defthm fn-nntp-effects-number-retrieval
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-number-retrieval session archive kind token)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-number-retrieval)
                                  (fn-nntp-article-response
                                   fn-nntp-find-group-number)))))

(defthm fn-nntp-effects-msgid-retrieval
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-msgid-retrieval session archive kind token)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-msgid-retrieval)
                                  (fn-nntp-article-response
                                   fn-find-article)))))

(defthm fn-nntp-effects-retrieval
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-retrieval session archive kind args)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-retrieval)
                                  (fn-nntp-current-retrieval
                                   fn-nntp-number-retrieval
                                   fn-nntp-msgid-retrieval)))))

(defthm fn-nntp-effects-next-or-last
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-next-or-last session archive direction)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-next-or-last)
                                  (fn-nntp-article-response
                                   fn-nntp-available-article
                                   fn-nntp-group-next-number
                                   fn-nntp-group-last-number)))))

(defthm fn-nntp-effects-list-active
  (implies (fn-nntp-safe-group-listp groups)
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-list-active session archive groups))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-list-active)
                                  (fn-nntp-active-lines)))))

(defthm fn-nntp-effects-list-newsgroups
  (implies (fn-nntp-safe-group-listp groups)
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-list-newsgroups session groups))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-list-newsgroups)
                                  (fn-nntp-newsgroup-lines)))))

(defthm fn-nntp-effects-list-filtered-response
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-list-filtered-response session archive kind wildmat))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-list-filtered-response)
                                  (fn-nntp-projectionp
                            fn-statep fn-state-groups
                            fn-state-articles fn-state-nexts
                                   fn-nntp-list-active fn-nntp-list-newsgroups
                                   fn-nntp-filter-groups-by-wildmat
                                   fn-wildmat-parse)))))

(defthm fn-nntp-effects-list-active-or-newsgroups
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-list-active-or-newsgroups session archive kind args))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-list-active-or-newsgroups)
                                  (fn-nntp-projectionp
                            fn-statep fn-state-groups
                            fn-state-articles fn-state-nexts
                                   fn-nntp-list-active fn-nntp-list-newsgroups
                                   fn-nntp-list-filtered-response)))))

; LIST OVERVIEW.FMT (RFC 3977 section 8.4) is answered from the unmaintained
; LIST dispatcher below, which keeps fn-nntp-list-overview-fmt closed, so its
; effects lemma has to exist first: it was stated 300 lines further down and
; the dispatcher theorem failed on exactly this statement (ld replay,
; 2026-09-20).  A ground fact: the seven lines are a constant.
(defthm fn-nntp-effects-list-overview-fmt
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-list-overview-fmt session)))
  :hints (("Goal" :in-theory (enable fn-nntp-list-overview-fmt
                                     fn-nov-fmt-octet-lines
                                     fn-nntp-block-textp))))

(defthm fn-nntp-effects-list-unmaintained-response
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-list-unmaintained-response session keyword args)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-list-unmaintained-response)
                                  (fn-nntp-list-overview-fmt)))))

(defthm fn-nntp-effects-list-response
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-list-response session archive args))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-list-response)
                                  (fn-nntp-projectionp
                            fn-statep fn-state-groups
                            fn-state-articles fn-state-nexts
                                   fn-nntp-list-active
                                   fn-nntp-list-active-or-newsgroups
                                   fn-nntp-list-unmaintained-response)))))

(defthm fn-nntp-effects-capabilities
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-capabilities session)))
  :hints (("Goal" :in-theory (enable fn-nntp-capabilities
                                     fn-nntp-capability-lines
                                     fn-nntp-unadvertised-capability-lines
                                     fn-nntp-block-textp))))

(defthm fn-nntp-effects-help
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-help session)))
  :hints (("Goal" :in-theory (enable fn-nntp-help
                                     fn-nntp-block-textp))))

; -----------------------------------------------------------------------------
; The reader profile's new branches (RFC 3977 sections 5.3, 7.1, 7.3, 8.3, 8.4)
;
; books/nntp-overview.lisp proves that every overview field and every overview
; line is clean, with no hypothesis about the stored article.  These two
; bridges carry that into this book's response grammar, so an overview line can
; neither split a response nor invent a field boundary.

(defthm fn-nntp-clean-line-is-response-text
  (implies (fn-nov-clean-linep bytes) (fn-nntp-response-textp bytes))
  :hints (("Goal" :induct (fn-nov-clean-linep bytes)
           :in-theory (enable fn-nov-clean-linep fn-nntp-response-textp))))

(defthm fn-nntp-clean-lines-are-block-text
  (implies (fn-nov-clean-line-listp lines) (fn-nntp-block-textp lines))
  :hints (("Goal" :induct (fn-nov-clean-line-listp lines)
           :in-theory (enable fn-nov-clean-line-listp fn-nntp-block-textp))))

(defthm fn-nntp-over-block-is-block-text
  (fn-nntp-block-textp (fn-nov-lines-for-numbers group numbers articles))
  :hints (("Goal" :use fn-nov-lines-for-numbers-are-clean
           :in-theory (disable fn-nov-lines-for-numbers-are-clean
                               fn-nov-lines-for-numbers))))

(defthm fn-nntp-over-one-line-is-block-text
  (implies (fn-nov-okp (fn-nov-overview article))
           (fn-nntp-block-textp (list (fn-nov-line number (fn-nov-overview article)))))
  :hints (("Goal" :use ((:instance fn-nov-line-is-a-clean-line
                         (over (fn-nov-overview article)))
                        (:instance fn-nov-overview-is-an-overview))
           :in-theory (e/d (fn-nntp-block-textp)
                           (fn-nov-line-is-a-clean-line
                            fn-nov-overview-is-an-overview
                            fn-nov-line fn-nov-overview fn-nov-overviewp)))))

(defthm fn-nntp-effects-over-current
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-over-current session archive)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-current)
                                  (fn-nov-overview fn-nov-line
                                   fn-nntp-available-article fn-nntp-single)))))

(defthm fn-nntp-effects-over-range
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-over-range session archive token)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range)
                                  (fn-nov-lines-for-numbers
                                   fn-nntp-group-range-numbers
                                   fn-nntp-parse-range fn-nntp-single)))))

(defthm fn-nntp-effects-over-msgid
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-over-msgid session archive token)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-msgid)
                                  (fn-nov-overview fn-nov-line
                                   fn-find-article fn-nntp-single
                                   fn-nntp-token-string)))))

(defthm fn-nntp-effects-over-response
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-over-response session archive args)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-response)
                                  (fn-nntp-over-current fn-nntp-over-range
                                   fn-nntp-over-msgid fn-nntp-single
                                   fn-nntp-parse-range
                                   fn-nntp-message-id-tokenp)))))

; DATE renders only fixed octets and table-looked-up digits, so its line is a
; status line of exactly eighteen octets whatever the clock reads.
(defthm fn-nntp-pad2-is-response-text
  (fn-nntp-response-textp (fn-nntp-pad2 n)))

(defthm fn-nntp-pad4-is-response-text
  (fn-nntp-response-textp (fn-nntp-pad4 n))
  :hints (("Goal" :in-theory (enable fn-nntp-pad4 fn-nntp-pad2))))

(defthm fn-nntp-date-octets-is-response-text
  (fn-nntp-response-textp (fn-nntp-date-octets civil))
  :hints (("Goal" :in-theory (e/d (fn-nntp-date-octets fn-nntp-append-pieces)
                                  (fn-nntp-pad2 fn-nntp-pad4)))))

(defthm fn-nntp-date-octets-is-a-status-line
  (fn-nntp-initial-status-linep (fn-nntp-date-octets civil))
  :hints (("Goal" :in-theory (e/d (fn-nntp-date-octets fn-nntp-append-pieces
                                   fn-nntp-initial-status-linep)
                                  (fn-nntp-pad2 fn-nntp-pad4)))))

(defthm fn-nntp-date-octets-length
  (equal (len (fn-nntp-date-octets civil)) 18)
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-nntp-date-octets fn-nntp-append-pieces
                                     fn-nntp-pad2 fn-nntp-pad4))))

(defthm fn-nntp-effects-date-response
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-date-response session env)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-date-response fn-nntp-effectsp)
                                  (fn-nntp-date-octets fn-nntp-single
                                   fn-nntp-replyp fn-nntp-crlf
                                   fn-nntp-dtn-civil
                                   fn-clock-observationp fn-clock-has-wall)))))

(defthm fn-nntp-effects-mode-response
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-mode-response session args)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-mode-response fn-nntp-effectsp
                                   fn-nntp-effectp fn-nntp-reply-effect
                                   fn-nntp-close-effect)
                                  (fn-nntp-replyp fn-nntp-single
                                   fn-nntp-keywordp)))))

; NEWGROUPS lists group names that came from persisted creation facts, so the
; environment recognizer is what makes every emitted name renderable.
; fn-nntp-facts-since screens every fact it keeps, so the emitted names are
; renderable whatever the host passed: no environment hypothesis is needed, and
; one would have no teeth.
(defthm fn-nntp-facts-since-are-facts
  (fn-nntp-group-fact-listp (fn-nntp-facts-since threshold facts)))

(defthm fn-nntp-fact-names-are-safe
  (implies (fn-nntp-group-fact-listp facts)
           (fn-nntp-safe-group-listp (fn-nntp-fact-names facts))))

(defthm fn-nntp-effects-newgroups-response
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-newgroups-response session archive env args)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-newgroups-response)
                                  (fn-nntp-active-lines fn-nntp-single
                                   fn-nntp-fact-names fn-nntp-facts-since
                                   fn-nntp-newgroups-date-parse
                                   fn-nntp-newgroups-time-parse
                                   fn-nntp-civil-dtn-ms
                                   fn-nntp-observed-year
                                   fn-nntp-keywordp)))))

(in-theory (disable fn-nntp-listgroup-command
                    fn-nntp-current-retrieval
                    fn-nntp-number-retrieval
                    fn-nntp-msgid-retrieval
                    fn-nntp-retrieval fn-nntp-next-or-last
                    fn-nntp-list-filtered-response
                    fn-nntp-list-active-or-newsgroups
                    fn-nntp-list-unmaintained-response
                    fn-nntp-list-response
                    fn-nntp-capabilities fn-nntp-help
                    fn-nntp-date-response fn-nntp-mode-response
                    fn-nntp-newgroups-response fn-nntp-list-overview-fmt
                    fn-nntp-over-current fn-nntp-over-range
                    fn-nntp-over-msgid fn-nntp-over-response))

(defthm fn-nntp-close-effect-is-well-formed
  (fn-nntp-effectp (fn-nntp-close-effect))
  :hints (("Goal" :in-theory (enable fn-nntp-effectp fn-nntp-close-effect))))

(defthm fn-nntp-session-command-effects-well-formed
  (fn-nntp-effectsp
   (fn-nntp-result-effects (fn-nntp-session-command session env keyword args)))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-session-command fn-nntp-effectsp)
                (fn-nntp-capabilities fn-nntp-help fn-nntp-single
                 fn-nntp-date-response fn-nntp-mode-response
                 fn-nntp-keywordp fn-nntp-keyword-tokenp)))))

(defthm fn-nntp-archive-command-effects-well-formed
  (implies (fn-nntp-projectionp archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-archive-command session archive env keyword args))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-archive-command)
                (fn-nntp-projectionp
                            fn-statep fn-state-groups
                            fn-state-articles fn-state-nexts fn-nntp-keywordp
                 fn-nntp-group-result fn-nntp-listgroup-command
                 fn-nntp-list-response fn-nntp-next-or-last
                 fn-nntp-retrieval fn-nntp-single
                 fn-nntp-over-response fn-nntp-newgroups-response
                 fn-nntp-token-string)))))

(defthm fn-nntp-command-effects-well-formed
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-command session archive env tokens))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-command)
                (fn-nntp-session-command fn-nntp-archive-command
                 fn-nntp-archive-keywordp fn-nntp-keyword-tokenp
                 fn-nntp-single fn-nntp-projectionp
                            fn-statep fn-state-groups
                            fn-state-articles fn-state-nexts))
           :expand ((fn-nntp-session-consistentp session archive)))))

(defthm fn-nntp-step-effects-well-formed
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-step session archive env wire-event))))
  :hints (("Goal" :in-theory
           (e/d (fn-nntp-step)
                (fn-nntp-result-effects fn-nntp-make-result
                 fn-nntp-single fn-nntp-command
                 fn-nntp-session-consistentp
                 fn-nntp-sessionp fn-nntp-session-openp
                 fn-nntp-command-inputp fn-nntp-tokenize
                 fn-nntp-command-arguments-at-mostp)))))

(defthm fn-nntp-closed-step-has-no-effects
  (implies (or (not (fn-nntp-sessionp session))
               (not (equal (fn-nntp-session-openp session) t)))
           (equal (fn-nntp-result-effects (fn-nntp-step session archive env wire-event))
                  nil))
  :hints (("Goal" :in-theory (e/d (fn-nntp-step) (fn-nntp-command)))))

(defthm fn-nntp-closed-step-effects-well-formed
  (implies (or (not (fn-nntp-sessionp session))
               (not (equal (fn-nntp-session-openp session) t)))
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-step session archive env wire-event))))
  :hints (("Goal" :use fn-nntp-closed-step-has-no-effects)))

(defthm fn-nntp-quit-step-effects-well-formed
  (implies (and (fn-nntp-sessionp session)
                (equal (fn-nntp-session-openp session) t))
           (fn-nntp-effectsp
            (fn-nntp-result-effects
             (fn-nntp-step session archive env '(:command (81 85 73 84))))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-step
                                   fn-nntp-command
                                   fn-nntp-session-command
                                   fn-nntp-effectsp
                                   fn-nntp-effectp
                                   fn-nntp-reply-effect
                                   fn-nntp-close-effect)
                                  (fn-nntp-replyp fn-nntp-date-response
                                   fn-nntp-mode-response)))))

; -----------------------------------------------------------------------------
; The decimal rendering guard is inactive across RFC 3977 section 6's range

; fn-nntp-decimal-field clamps the rendered width so the 512-octet argument
; above is structural.  This says the clamp never changes a number the profile
; can legitimately render, so no response loses information to it.

; GAP, not a weakening.  The final form of this book used to be an
; `encapsulate' proving `fn-nntp-decimal-field-is-exact-in-range', that the
; ten-octet clamp in `fn-nntp-decimal-field' is inactive for every number a
; projectable archive can render.  Its local `(include-book "arithmetic-5/top"
; :dir :system)' fails to load in this ACL2 (DEFTHEORY
; ARITHMETIC-5-CURRENT-BASE rejects (:TYPE-PRESCRIPTION INCREMENT-TIMER@PAR)),
; so the event is removed rather than left uncertified.  Nothing above depends
; on it: `fn-nntp-decimal-field' bounds the rendered width by construction, so
; `fn-nntp-group-initial-fits', `fn-nntp-listgroup-initial-fits' and
; `fn-nntp-retrieval-initial-fits' are unconditional.  What is lost is the
; statement that the clamp never fires in range; the boundary values 0, 1 and
; 2147483647 are still pinned by `assert-event' in tests/acl2/nntp-tests.lisp.
