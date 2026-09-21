; Teeth for the wildmat matcher keystones.
;
; The 2026-09-18 review §5: "the matcher is proved equal to an independent
; backtracking reference; rightmost-wins is proved against a left-to-right
; last-match reference, which is RFC 3977 section 4.2."  The first of those is
; unconditional, so it has no hypothesis to remove; what it needs instead is a
; witness that exhibits both poles, because an equality between two functions
; that are both constantly NIL is also unconditional.  The second has one
; hypothesis, and it has teeth.

(in-package "ACL2")
(include-book "../../books/wildmat-matcher-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness: RFC 3977 section 4.2's own example,
; `a*,!*b,*c*', parsed by the production parser rather than written out as a
; pattern record by hand.

(defconst *wm-teeth-octets* '(97 42 44 33 42 98 44 42 99 42))
(defconst *wm-teeth-parsed* (fn-wildmat-parse *wm-teeth-octets*))
(assert-event (fn-wildmat-result-okp *wm-teeth-parsed*))

(defconst *wm-teeth-patterns* (fn-wildmat-result-value *wm-teeth-parsed*))
(assert-event (fn-wildmat-pattern-listp *wm-teeth-patterns*))
(assert-event (equal (len *wm-teeth-patterns*) 3))

; Both poles, so neither side of the equality is constant: `aaa' is included by
; the leftmost constituent, and `abb' is excluded by the negated one.  A
; separating witness has to separate the predicates by more than their weakest
; clause, and a single accepting target would not.
(assert-event
 (fn-wildmat-pattern-positivep
  (fn-wildmat-rightmost-match *wm-teeth-patterns* '(97 97 97))))
(assert-event
 (not (fn-wildmat-pattern-positivep
       (fn-wildmat-rightmost-match *wm-teeth-patterns* '(97 98 98)))))
(assert-event
 (fn-wildmat-pattern-positivep
  (fn-wildmat-rightmost-match *wm-teeth-patterns* '(99 99 98))))
(assert-event (null (fn-wildmat-rightmost-match *wm-teeth-patterns* '(120 120 120))))

; The keystone equalities hold at the witness, in both directions of the
; rightmost rule and for a target that no constituent matches.
(assert-event
 (equal (fn-wildmat-rightmost-match *wm-teeth-patterns* '(99 99 98))
        (fn-wm-select-reference *wm-teeth-patterns* '(99 99 98) nil)))
(assert-event
 (equal (fn-wildmat-rightmost-match *wm-teeth-patterns* '(97 98 98))
        (fn-wm-select-reference *wm-teeth-patterns* '(97 98 98) nil)))

; And the dynamic-programming matcher agrees with the backtracking reference on
; a pattern with two stars, where a naive left-to-right greedy matcher would
; not.  `*c*' matches `ccb'; `a*' does not.
(defconst *wm-teeth-star-items*
  (fn-wildmat-pattern-items (car (last *wm-teeth-patterns*))))
(assert-event
 (equal (fn-wildmat-pattern-matchp *wm-teeth-star-items* '(99 99 98))
        (fn-wm-anchored-matchp *wm-teeth-star-items* '(99 99 98))))
(assert-event (fn-wildmat-pattern-matchp *wm-teeth-star-items* '(99 99 98)))
(assert-event (not (fn-wildmat-pattern-matchp *wm-teeth-star-items* '(120 120 120))))

; -----------------------------------------------------------------------------
; Teeth for `fn-wildmat-rightmost-match-is-last-reference-match'
;   (implies (fn-wildmat-pattern-listp patterns)
;            (equal (fn-wildmat-rightmost-match patterns target)
;                   (fn-wm-select-reference patterns target nil)))

; The sole hypothesis dropped.  `fn-wildmat-rightmost-match' uses the pattern
; record it returns as its own "found" flag (books/wildmat.lisp:397-405): a
; NIL right-hand result means "keep looking left".  A well-formed pattern
; record is never NIL, so under the hypothesis that is sound.  Drop it and a
; list whose rightmost matching element IS NIL makes the two disagree: the
; production matcher keeps looking and reports the left constituent, while the
; left-to-right reference correctly reports the rightmost one.
(defconst *wm-teeth-malformed*
  (list (fn-wildmat-make-pattern t nil) nil))
(assert-event (not (fn-wildmat-pattern-listp *wm-teeth-malformed*)))

(local
 (must-fail
  (defthm wm-teeth-rightmost-without-pattern-listp
    (equal (fn-wildmat-rightmost-match *wm-teeth-malformed* nil)
           (fn-wm-select-reference *wm-teeth-malformed* nil nil)))))

; -----------------------------------------------------------------------------
; `fn-wildmat-pattern-matchp-is-anchored-reference' has no hypothesis, so it
; has no must-fail sibling; the witness above is its whole teeth requirement.
; What would make it vacuous is both sides being constant, and the assertions
; above exhibit a target each side accepts and a target each side rejects.

; -----------------------------------------------------------------------------
; Teeth for the header-value profile keystones (decision D19)

(include-book "../../books/wildmat-parser-invariants")

; -----------------------------------------------------------------------------
; `fn-wildmat-exactp-implies-text-exactp' and its two siblings
;   (implies (fn-wildmat-exactp c) (fn-wildmat-text-exactp c))
;
; A containment whose two sides were the same set would also be provable, so
; the witness has to exhibit the gap AND the floor.  %x20 SP is in the wider
; set and not in RFC 3977 §4.1's; `!' is in neither, which is what makes the
; hypothesis do work rather than hold everywhere.

(assert-event (and (fn-wildmat-text-exactp 32) (not (fn-wildmat-exactp 32))))
(assert-event (and (fn-wildmat-text-exactp 91) (not (fn-wildmat-exactp 91))))
(assert-event (and (fn-wildmat-text-exactp 92) (not (fn-wildmat-exactp 92))))
(assert-event (and (fn-wildmat-text-exactp 93) (not (fn-wildmat-exactp 93))))
(assert-event (and (fn-wildmat-exactp 97) (fn-wildmat-text-exactp 97)))

; The hypothesis dropped: `!' satisfies neither side, so the implication is
; not vacuously true of every code point.
(local
 (must-fail
  (defthm wm-teeth-text-exactp-without-exactp
    (fn-wildmat-text-exactp 33)
    :rule-classes nil)))

; `fn-wildmat-items-p-implies-text-items-p', hypothesis dropped.
(assert-event (and (not (fn-wildmat-items-p '(33)))
                   (not (fn-wildmat-text-items-p '(33)))))
(assert-event (and (not (fn-wildmat-items-p '(32)))
                   (fn-wildmat-text-items-p '(32))))

; -----------------------------------------------------------------------------
; `fn-wildmat-item-character-matchp-is-rfc3977-on-rfc3977-items'
;   (implies (fn-wildmat-itemp item)
;            (equal (fn-wildmat-item-character-matchp item codepoint)
;                   <the body this function had before D19>))
;
; This is the conservation keystone: it is what says no newsgroup-name match
; moved.  Its hypothesis has teeth at exactly the four code points D19 added.
; At item = 32 the two sides disagree -- the widened matcher matches an SP
; against an SP, and the pre-D19 body matched it against nothing -- so the
; equality is false without `fn-wildmat-itemp'.

(assert-event (fn-wildmat-item-character-matchp 32 32))
(assert-event (not (fn-wildmat-itemp 32)))
(assert-event
 (not (equal (fn-wildmat-item-character-matchp 32 32)
             (if (equal 32 63)
                 t
               (if (fn-wildmat-exactp 32) (if (equal 32 32) t nil) nil)))))

(local
 (must-fail
  (defthm wm-teeth-matchp-conservation-without-itemp
    (equal (fn-wildmat-item-character-matchp 32 32)
           (if (equal 32 63)
               t
             (if (fn-wildmat-exactp 32) (if (equal 32 32) t nil) nil)))
    :rule-classes nil)))

; And under the hypothesis it holds at both poles: an exact item that matches,
; an exact item that does not, and `?' which matches anything.
(assert-event (fn-wildmat-item-character-matchp 97 97))
(assert-event (not (fn-wildmat-item-character-matchp 97 98)))
(assert-event (fn-wildmat-item-character-matchp 63 97))

; -----------------------------------------------------------------------------
; `fn-wildmat-parse-yields-rfc3977-patterns'
;   (implies (fn-wildmat-result-okp (fn-wildmat-parse octets))
;            (and (consp ...) (fn-wildmat-rfc3977-pattern-listp ...)))
;
; The reachable non-degenerate witness is RFC 3977 §4.2's own example, parsed
; by the production entry point: three constituents, one of them negated.

(assert-event (fn-wildmat-rfc3977-pattern-listp *wm-teeth-patterns*))
(assert-event (equal (len *wm-teeth-patterns*) 3))

; The hypothesis dropped.  On octets the newsgroup-name entry refuses, the
; conclusion is false: the result value is the reason keyword, not a list.
(defconst *wm-teeth-spaced* '(42 84 32 42 116 42))
(assert-event (equal (fn-wildmat-parse *wm-teeth-spaced*) '(:error :syntax)))
(assert-event
 (not (consp (fn-wildmat-result-value
              (fn-wildmat-parse *wm-teeth-spaced*)))))

(local
 (must-fail
  (defthm wm-teeth-rfc3977-patterns-without-a-successful-parse
    (consp (fn-wildmat-result-value (fn-wildmat-parse *wm-teeth-spaced*)))
    :rule-classes nil)))

; ... and the SECOND hypothesis of the lemma behind it,
; `fn-wm-parse-one-rfc3977-pattern-listp', is the §4.1 restriction on the code
; points.  The same octets parse through the HEADER entry and the result is
; NOT §4.1-shaped, which is the whole point of the profile.
(assert-event (fn-wildmat-result-okp (fn-wildmat-parse-text *wm-teeth-spaced*)))
(assert-event
 (fn-wildmat-pattern-listp
  (fn-wildmat-result-value (fn-wildmat-parse-text *wm-teeth-spaced*))))
(assert-event
 (not (fn-wildmat-rfc3977-pattern-listp
       (fn-wildmat-result-value (fn-wildmat-parse-text *wm-teeth-spaced*)))))
(assert-event
 (not (fn-wildmat-rfc3977-codepointsp *wm-teeth-spaced*)))

(local
 (must-fail
  (defthm wm-teeth-parse-one-rfc3977-without-the-restriction
    (fn-wildmat-rfc3977-pattern-listp
     (fn-wildmat-result-value (fn-wildmat-parse-text *wm-teeth-spaced*)))
    :rule-classes nil)))

; -----------------------------------------------------------------------------
; `fn-wildmat-rfc3977-pattern-listp-implies-pattern-listp', hypothesis dropped:
; the widened shape admits a pattern the §4.1 shape refuses, and neither admits
; a malformed record.
(assert-event (not (fn-wildmat-rfc3977-pattern-listp *wm-teeth-malformed*)))
(assert-event (not (fn-wildmat-pattern-listp *wm-teeth-malformed*)))

; -----------------------------------------------------------------------------
; Positive anchors for the three recognisers the teeth above only ever assert
; FALSE (tools/teeth_check.py --report, `recogniser-never-true'): a definition
; that is constantly false would satisfy a refusal witness, so each one is
; also exhibited accepting.
(assert-event (and (fn-wildmat-itemp 97) (fn-wildmat-itemp 42)
                   (fn-wildmat-itemp 63)))
(assert-event (fn-wildmat-items-p '(97 42 63)))
(assert-event (fn-wildmat-rfc3977-codepointsp '(97 42 44 33 98)))
(assert-event (fn-wildmat-text-items-p '(97 32 42)))
