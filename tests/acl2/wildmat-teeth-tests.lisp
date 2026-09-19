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
