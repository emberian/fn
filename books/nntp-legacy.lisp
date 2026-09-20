; The legacy reader commands of RFC 2980 and their RFC 3977 successors:
; XOVER (section 2.8), XHDR (section 2.6) and HDR (RFC 3977 section 8.5),
; LIST ACTIVE.TIMES (section 2.1.3 / RFC 3977 section 7.6.4), LIST NEWSGROUPS
; (section 2.1.6 / RFC 3977 section 7.6.6) and LIST HEADERS (RFC 3977
; section 8.6).
;
; Two things are proved here and nothing else is claimed.  First, that the
; legacy spelling is the modern one: fn-nntp-xover-range and
; fn-nntp-over-range return the same result wherever the two RFCs assign the
; same response, so XOVER is not a second overview implementation that could
; drift from OVER.  Second, that every line these commands render is clean in
; the sense books/nntp-overview.lisp fixed for the overview line -- no NUL,
; CR or LF anywhere, and for the per-article lines no TAB either, since those
; carry no TAB-separated fields.  Cleanliness is what lets
; books/nntp-effects.lisp read a rendered line back as a block line of a
; well-formed response, which is where dot-stuffing and the terminating
; sequence are proved; this book does not restate them.
(in-package "ACL2")
(include-book "nntp-overview")

; The five books of the nntp cluster and books/nntp-overview.lisp withdraw
; their definitions at their export events; this book reasons about the
; renderers themselves, so it re-enables exactly them, locally.  No includer
; inherits them.
(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary
                          fn-nntp-vocabulary
                          fn-nov-vocabulary
                          fn-nov-overviewp)))

; The parser, the article syntax recognizer and the body splitter stay closed
; for the whole book, for the reason books/nntp-overview.lisp records: opened,
; they if-split every goal that mentions an article thousands of ways.
(local (in-theory (disable fn-article-parse fn-article-syntax-p
                           fn-nntp-split-article fn-nov-value-content)))

; -----------------------------------------------------------------------------
; A clean field is closed under append (books/nntp-overview.lisp proves the
; corresponding fact for a clean line).

(local
 (defthm fn-nntp-legacy-clean-field-of-append
   (implies (and (fn-nov-clean-fieldp x) (fn-nov-clean-fieldp y))
            (fn-nov-clean-fieldp (append x y)))))

; A printable command token (RFC 3977 section 9.8: octets 33 to 126) is
; already a clean field: it carries no NUL, TAB, CR or LF.
; :rule-classes nil deliberately.  Left as a rewrite this backchains on
; true-listp under every goal in the book, which is the rule shape
; books/nntp-invariants.lisp measured as the cause of its 1800 s runs (the
; w3/reader-profile NOTE on the board).  The two places that need it cite it.
(defthm fn-nntp-printable-token-is-a-clean-field
  (implies (and (fn-nntp-printable-tokenp token) (true-listp token))
           (fn-nov-clean-fieldp token))
  :rule-classes nil)

(defthm fn-nntp-safe-group-name-renders-a-clean-field
  (implies (fn-nntp-safe-group-namep name)
           (fn-nov-clean-fieldp (fn-nntp-string-octets name)))
  :hints (("Goal" :in-theory (disable fn-nntp-printable-tokenp)
           :use ((:instance fn-nntp-printable-token-is-a-clean-field
                            (token (fn-nntp-string-octets name)))))))


; -----------------------------------------------------------------------------
; XOVER is OVER
;
; RFC 2980 section 2.8.1 and RFC 3977 section 8.3.1 assign the same 224 and
; the same 412; they differ only where the range selects nothing (420 against
; 423).  On every other input the two functions are the same value, so the
; legacy spelling cannot report a different overview from the modern one.

(defthm fn-nntp-xover-agrees-with-over-on-a-nonempty-range
  (implies (consp (fn-nov-lines-for-numbers
                   (fn-nntp-session-group session)
                   (fn-nntp-group-range-numbers
                    (fn-nntp-session-group session)
                    (fn-nntp-range-low (fn-nntp-parse-range token))
                    (fn-nntp-range-high (fn-nntp-parse-range token))
                    (fn-state-articles archive))
                   (fn-state-articles archive)))
           (equal (fn-nntp-xover-range session archive token)
                  (fn-nntp-over-range session archive token)))
  ; Both bodies are the same `let*' but for one octet string, so the proof is
  ; propositional once the four terms inside them stay closed.  Opened, the
  ; range walk and the overview fold appear twice each and the goal passes
  ; 2,000,000 prover steps (ld replay, 2026-09-20).
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-xover-range fn-nntp-over-range)
                           (fn-nov-lines-for-numbers
                            fn-nntp-group-range-numbers fn-nntp-parse-range
                            fn-nntp-session-group fn-state-articles
                            fn-nntp-multi fn-nntp-single)))))

(defthm fn-nntp-xover-with-no-argument-is-over-with-no-argument
  (equal (fn-nntp-xover-response session archive nil)
         (fn-nntp-over-response session archive nil))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-xover-response fn-nntp-over-response)
                           (fn-nntp-over-current fn-nntp-xover-range
                            fn-nntp-over-range fn-nntp-single)))))

; -----------------------------------------------------------------------------
; HDR and XHDR render clean lines
;
; RFC 3977 section 8.5.2 applies the section 8.3.2 transformation to a header
; content, which is fn-nov-scrub, and a metadata item is a decimal count.  So
; the value half of an HDR line is clean with no hypothesis at all, and the
; whole line -- number, space, value -- carries no TAB either.

(defthm fn-nntp-hdr-content-is-clean
  (fn-nov-clean-fieldp (fn-nntp-hdr-octets (fn-nntp-hdr-content field article))))

(defthm fn-nntp-hdr-line-is-a-clean-field
  (implies (and (fn-nov-clean-fieldp label) (fn-nov-clean-fieldp content))
           (fn-nov-clean-fieldp (fn-nntp-hdr-line label content))))

(defun fn-nntp-hdr-clean-field-listp (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (and (fn-nov-clean-fieldp (car lines))
           (fn-nntp-hdr-clean-field-listp (cdr lines)))
    (null lines)))

(defthm fn-nntp-hdr-clean-fields-are-clean-lines
  (implies (fn-nntp-hdr-clean-field-listp lines)
           (fn-nov-clean-line-listp lines)))

(defthm fn-nntp-hdr-lines-for-numbers-are-clean
  (fn-nntp-hdr-clean-field-listp
   (fn-nntp-hdr-lines-for-numbers field group numbers articles))
  :hints (("Goal" :in-theory (disable fn-nntp-hdr-content fn-nntp-hdr-line
                                      fn-nntp-hdr-octets))))

; RFC 3977 section 8.5.2: if the requested header is not present in the
; article, a line for that article is still included and the content portion
; is empty.  This is that, of the function the dispatcher calls into.
(defthm fn-nntp-hdr-of-a-missing-field-is-empty
  (implies (and (not (fn-nntp-hdr-metadata-tokenp field))
                (not (consp (fn-article-get-headers
                             (fn-article-result-article
                              (fn-article-parse (fn-article-payload article)))
                             field))))
           (equal (fn-nntp-hdr-octets (fn-nntp-hdr-content field article))
                  nil)))

; The two line shapes the three HDR responses render, each with no hypothesis
; at all: books/nntp-effects.lisp reads these back as block lines.
(defthm fn-nntp-hdr-numbered-line-is-clean
  (fn-nov-clean-fieldp
   (fn-nntp-hdr-line (fn-nntp-decimal-field number)
                     (fn-nntp-hdr-octets (fn-nntp-hdr-content field article))))
  :hints (("Goal" :in-theory (disable fn-nntp-hdr-line fn-nntp-hdr-content
                                      fn-nntp-hdr-octets))))

(defthm fn-nntp-hdr-labelled-line-is-clean
  (fn-nov-clean-fieldp
   (fn-nntp-hdr-line (fn-nov-scrub token)
                     (fn-nntp-hdr-octets (fn-nntp-hdr-content field article))))
  :hints (("Goal" :in-theory (disable fn-nntp-hdr-line fn-nntp-hdr-content
                                      fn-nntp-hdr-octets fn-nov-scrub))))

; -----------------------------------------------------------------------------
; XPAT selects from XHDR's lines (RFC 2980 section 2.9)
;
; The parity claim, and the reason XPAT is not a second header projection:
; every line XPAT emits for a field, a group and a list of numbers is a line
; fn-nntp-hdr-lines-for-numbers emits for the same three.  The wildmat only
; decides which of those lines survive.  A client therefore cannot see a
; header through XPAT that XHDR renders differently, whatever the pattern.

; The filter's "selects everything" condition, as a recognizer over the same
; recursion, so the agreement theorem below has a hypothesis that can be
; discharged by evaluation on a concrete transcript rather than by a claim
; about the matcher.
(defun fn-nntp-xpat-selects-everythingp (field patterns group numbers articles)
  (declare (xargs :guard t))
  (if (consp numbers)
      (let* ((article (fn-nntp-available-article group (car numbers) articles))
             (content (if (consp article)
                          (fn-nntp-hdr-content field article)
                        (list :error))))
        (and (or (not (fn-nntp-hdr-okp content))
                 (fn-nntp-xpat-matchesp patterns (fn-nntp-hdr-octets content)))
             (fn-nntp-xpat-selects-everythingp field patterns group
                                               (cdr numbers) articles)))
    t))

(defthm fn-nntp-xpat-lines-are-hdr-lines
  (subsetp-equal
   (fn-nntp-xpat-lines-for-numbers field patterns group numbers articles)
   (fn-nntp-hdr-lines-for-numbers field group numbers articles))
  :hints (("Goal" :induct (fn-nntp-xpat-lines-for-numbers field patterns group
                                                          numbers articles)
           :in-theory (disable fn-nntp-hdr-content fn-nntp-hdr-line
                               fn-nntp-hdr-octets fn-nntp-xpat-matchesp
                               fn-nntp-available-article))))

; A pattern that selects every article gives exactly XHDR's block: the two
; renderers agree where the filter is the identity.  Stated of the lines, so
; the only difference left between XPAT and XHDR is the section 2.9.1 initial
; line, which is XHDR's own (fn-nntp-hdr-initial with legacyp T).
(defthm fn-nntp-xpat-with-a-total-filter-is-the-hdr-block
  (implies (fn-nntp-xpat-selects-everythingp field patterns group numbers
                                             articles)
           (equal (fn-nntp-xpat-lines-for-numbers field patterns group numbers
                                                  articles)
                  (fn-nntp-hdr-lines-for-numbers field group numbers articles)))
  :hints (("Goal" :induct (fn-nntp-xpat-lines-for-numbers field patterns group
                                                          numbers articles)
           :in-theory (disable fn-nntp-hdr-content fn-nntp-hdr-line
                               fn-nntp-hdr-octets fn-nntp-xpat-matchesp
                               fn-nntp-available-article))))

(defthm fn-nntp-xpat-lines-are-clean
  (fn-nntp-hdr-clean-field-listp
   (fn-nntp-xpat-lines-for-numbers field patterns group numbers articles))
  :hints (("Goal" :induct (fn-nntp-xpat-lines-for-numbers field patterns group
                                                          numbers articles)
           :in-theory (e/d (fn-nntp-hdr-clean-field-listp)
                           (fn-nntp-hdr-content fn-nntp-hdr-line
                            fn-nntp-hdr-octets fn-nntp-xpat-matchesp
                            fn-nntp-available-article)))))

; -----------------------------------------------------------------------------
; The LIST variants

(local
 (defthm fn-nntp-legacy-creator-text-is-clean
   (fn-nov-clean-fieldp
    (fn-nntp-string-octets *fn-nntp-active-times-creator*))))

(local
 (defthm fn-nntp-legacy-no-description-text-is-clean
   (fn-nov-clean-fieldp (fn-nntp-string-octets "(no description)"))))

; The one fact about a creation fact the line renderer needs.  Stated so that
; fn-nntp-group-factp can stay closed in the theorem below: opened, it drags
; fn-clock-observationp into every subgoal.
(local
 (defthm fn-nntp-legacy-fact-name-is-safe
   (implies (fn-nntp-group-factp fact)
            (fn-nntp-safe-group-namep (fn-nntp-fact-name fact)))))

; The line is four pieces: the group name (clean because a creation fact
; carries a safe group name), a space, a decimal count and the fixed creator
; text.  Every one of the four stays closed, so the induction is over the
; fact list alone; opened, the seconds conversion drags `floor' into the goal
; and it passes 2,000,000 prover steps (ld replay, 2026-09-20).
(defthm fn-nntp-active-times-lines-are-clean
  (fn-nov-clean-line-listp (fn-nntp-active-times-lines facts))
  :hints (("Goal" :induct (fn-nntp-active-times-lines facts)
           :in-theory (disable fn-nntp-safe-group-namep fn-nntp-string-octets
                               fn-nntp-decimal-field fn-nntp-dtn-unix-seconds
                               fn-nntp-div fn-nntp-fact-created
                               fn-nntp-fact-name fn-nntp-group-factp))))

(defthm fn-nntp-newsgroup-lines-are-clean
  (implies (fn-nntp-safe-group-listp groups)
           (fn-nov-clean-line-listp (fn-nntp-newsgroup-lines groups)))
  :hints (("Goal" :induct (fn-nntp-newsgroup-lines groups)
           :in-theory (disable fn-nntp-safe-group-namep
                               fn-nntp-string-octets))))

; RFC 3977 section 8.6: the three entries LIST HEADERS renders are clean.
; A ground fact, established by evaluation.
(defthm fn-nntp-hdr-field-lines-are-clean
  (fn-nov-clean-line-listp
   (fn-nov-fmt-octet-lines *fn-nntp-hdr-field-lines*)))

; The XHDR message-id form renders the message-id where HDR renders a zero
; (RFC 2980 section 2.6 against RFC 3977 section 8.5.2).  It passes the token
; through fn-nov-scrub, which is total; on the printable token the caller has
; already recognized, scrub is the identity, so the rendered label is the
; client's own message-id octet for octet.
(defthm fn-nov-scrub-is-the-identity-on-a-printable-token
  (implies (and (fn-nntp-printable-tokenp token) (true-listp token))
           (equal (fn-nov-scrub token) token)))

(verify-guards fn-nntp-hdr-clean-field-listp)

; -----------------------------------------------------------------------------
; Export.  The keystones stay enabled.  The two bridges are proof vocabulary:
; fn-nntp-printable-token-is-a-clean-field is :rule-classes nil at its
; statement, and fn-nntp-safe-group-name-renders-a-clean-field is withdrawn
; here, because both backchain on true-listp or on a group recognizer, which
; is the rule shape books/nntp-invariants.lisp measured as the cause of its
; 1800 s runs.  fn-nntp-hdr-clean-fields-are-clean-lines stays enabled:
; books/nntp-effects.lisp cites it to read an HDR block back as block text.
(verify-guards fn-nntp-xpat-selects-everythingp)

(in-theory (disable fn-nntp-hdr-clean-field-listp
                    fn-nntp-safe-group-name-renders-a-clean-field))
