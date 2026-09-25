; fn: XPAT on the served reader step (RFC 2980 section 2.9), and its label.
;
; Subject.  The served reader reaches fn-nntp-step-pinned (books/nntp.lisp)
; for every reader command: host/native/owner.lisp calls fn-owner-chunk
; (host/owner-host.lisp), which runs fn-served-step (books/served.lisp) over
; the connection; fn-served-dispatch calls fn-auth-step-pinned
; (books/nntp-auth.lisp), whose delegate reaches fn-nntp-post-step-pinned and
; from there fn-nntp-step-pinned (books/nntp-post.lisp) for every command
; that is not POST.  `fn-nntp-step-pinned-xpat-is-the-xpat-response' is the
; XPAT arm of that step: the pinned dispatcher adds no XPAT arm of its own,
; so the reply is fn-nntp-xpat-response's.
;
; The pattern rule, and which RFC it is.  XPAT is RFC 2980 section 2.9, not
; RFC 3977.  Section 2.9: "If there are additional arguments the are joined
; together separated by a single space to form one complete pattern."  fn
; implements that rule (fn-nntp-xpat-join, books/nntp-responses.lisp), as
; INN's nnrpd does (planning/evidence/inn-xpat-2026-09-20.md).  A second
; argument is therefore NOT a second alternative: `XPAT Subject 1-9 *a* *b*'
; asks for subjects matching the one pattern "*a* *b*".  The alternative is
; the wildmat's comma (RFC 3977 section 4.2): `XPAT Subject 1-9 *a*,*b*'.
; `fn-nntp-xpat-alternation-is-or' states that comma alternatives OR at
; the matcher the XPAT arm calls, whenever the alternatives on the right
; are not negated.  Case: RFC 3977 section 4.2, "A <wildmat-exact> matches
; the same character"; fn-wildmat-item-character-matchp compares code
; points, so matching is case-sensitive (the teeth book shows a subject
; that one case matches and the other does not).
;
; The label.  RFC 3977 section 3.3.3 lets a private extension appear in the
; capability list only under a label beginning with "X".  XPAT is such an
; extension (RFC 2980 predates capability labels), and the served capability
; block now lists it: `fn-auth-capability-lines-advertise-xpat', over the
; renderer fn-auth-command's CAPABILITIES arm calls.
(in-package "ACL2")
(include-book "nntp")
(include-book "nntp-auth")

; -----------------------------------------------------------------------------
; The subject: the XPAT arm of the served reader step.

(defthm fn-nntp-step-pinned-xpat-is-the-xpat-response
  (implies (and (fn-nntp-sessionp session)
                (equal (fn-nntp-session-openp session) t)
                (fn-nntp-session-projected session)
                (fn-nntp-command-inputp line)
                (consp (fn-nntp-tokenize line))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "XPAT"))
           (equal (fn-nntp-step-pinned session archive index verdicts env
                                       (list :command line))
                  (fn-nntp-xpat-response session archive
                                         (cdr (fn-nntp-tokenize line)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-step-pinned fn-nntp-command-pinned
                            fn-nntp-archive-command-pinned
                            fn-nntp-archive-command fn-nntp-archive-keywordp
                            fn-nntp-keywordp)
                           (fn-nntp-upcase-keyword fn-nntp-keyword-tokenp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp
                            fn-nntp-sessionp fn-nntp-xpat-response
                            fn-gidx-list-counts-command
                            fn-nntp-msgid-retrieval-indexed
                            fn-gidx-listgroup-command
                            fn-nntp-over-range-indexed
                            fn-nntp-verdict-hdr-response)))))

; -----------------------------------------------------------------------------
; Comma alternation is OR (RFC 3977 section 4.2), at the matcher XPAT calls.

(defun fn-nxp-all-positivep (patterns)
  (declare (xargs :guard t))
  (if (consp patterns)
      (and (consp (car patterns))
           (equal (car (car patterns)) :positive)
           (fn-nxp-all-positivep (cdr patterns)))
    t))

(local
 (defthm fn-nxp-rightmost-match-of-append
   (equal (fn-wildmat-rightmost-match (append p q) target)
          (or (fn-wildmat-rightmost-match q target)
              (fn-wildmat-rightmost-match p target)))
   :hints (("Goal" :in-theory (disable fn-wildmat-pattern-matchp)))))

(local
 (defthm fn-nxp-rightmost-match-of-positive-is-positive
   (implies (and (fn-nxp-all-positivep q)
                 (fn-wildmat-rightmost-match q target))
            (fn-wildmat-pattern-positivep
             (fn-wildmat-rightmost-match q target)))
   :hints (("Goal" :in-theory (e/d (fn-wildmat-pattern-positivep
                                    fn-wildmat-pattern-sign)
                                   (fn-wildmat-pattern-matchp))))))

(defthm fn-wildmat-match-codepoints-of-append
  (implies (fn-nxp-all-positivep q)
           (iff (fn-wildmat-match-codepoints (append p q) target)
                (or (fn-wildmat-match-codepoints p target)
                    (fn-wildmat-match-codepoints q target))))
  :hints (("Goal" :in-theory (disable fn-wildmat-pattern-matchp
                                      fn-wildmat-rightmost-match
                                      fn-wildmat-pattern-positivep))))

; Keystone: appending non-negated alternatives to a pattern list ORs them
; into the match of the XPAT arm's filter, over every header content.
(defthm fn-nntp-xpat-alternation-is-or
  (implies (fn-nxp-all-positivep q)
           (iff (fn-nntp-xpat-matchesp (append p q) content)
                (or (fn-nntp-xpat-matchesp p content)
                    (fn-nntp-xpat-matchesp q content))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-xpat-matchesp)
                                  (fn-wildmat-match-codepoints
                                   fn-wildmat-decode)))))

; -----------------------------------------------------------------------------
; The label, over the block the served CAPABILITIES arm renders.

(defthm fn-auth-capability-lines-advertise-xpat
  (member-equal (fn-nntp-string-octets "XPAT")
                (fn-auth-capability-lines-for-peer acfg subject tlsp postingp
                                                   record))
  :hints (("Goal" :in-theory (e/d (fn-auth-capability-lines-for-peer
                                   fn-peer-capability-lines
                                   fn-nntp-capability-lines)
                                  (fn-auth-access-capability-lines)))))
