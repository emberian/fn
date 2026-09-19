; Teeth for the article source-preservation keystone.
;
; The 2026-09-18 review §5: "Article source preservation is a genuine induction
; with the sole premise 'parse succeeded', for all inputs."  Sole premise is
; the point, so there is exactly one case to make, and the witness is what
; carries the weight: a source that a parser could plausibly normalise and
; must not.

(in-package "ACL2")
(include-book "../../books/article-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness.
;
; Folded continuation, a repeated unknown field, a NUL and a 255 octet in the
; body, an open parenthesis and a quoted string that a Lisp reader would find
; interesting, and a multi-octet UTF-8 sequence.  Preservation of a source
; with none of these would separate the parser from a normalising one by
; nothing.

(defconst *art-teeth-source*
  '(88 45 84 97 103 58 32 111 110 101 13 10
    83 117 98 106 101 99 116 58 32 97 108 112 104 97 13 10
    9 98 101 116 97 13 10
    88 45 84 97 103 58 32 116 119 111 13 10
    13 10
    0 255 40 114 101 97 100 32 34 110 111 116 32 76 105 115 112 34 41
    227 129 147 13 10))

(defconst *art-teeth-result* (fn-article-parse *art-teeth-source*))
(assert-event (fn-article-result-okp *art-teeth-result*))

(defconst *art-teeth-article* (fn-article-result-article *art-teeth-result*))
(assert-event (fn-article-syntax-p *art-teeth-article*))

; The keystone holds at the witness, octet for octet.
(assert-event (equal (fn-article-source *art-teeth-article*) *art-teeth-source*))

; Non-degenerate: the parsed view is not the source, so preservation is a real
; claim about two different objects rather than an identity on one.
(assert-event
 (not (equal (fn-article-header *art-teeth-article*) *art-teeth-source*)))
(assert-event (consp (fn-article-body *art-teeth-article*)))
(assert-event
 (equal (len (fn-article-get-headers *art-teeth-article* '(120 45 116 97 103))) 2))

; -----------------------------------------------------------------------------
; Teeth for `fn-article-successful-parse-preserves-source'
;   (implies (fn-article-result-okp (fn-article-parse octets))
;            (equal (fn-article-source
;                    (fn-article-result-article (fn-article-parse octets)))
;                   octets))

; The sole hypothesis dropped.  A header with no body separator is refused;
; the source of the article a refused parse did not produce is not the input.
(defconst *art-teeth-unterminated* '(83 117 98 106 101 99 116 58 32 120 13 10))
(assert-event (equal (fn-article-parse *art-teeth-unterminated*)
                     '(:error :missing-separator)))
(assert-event (not (fn-article-result-okp (fn-article-parse *art-teeth-unterminated*))))

(local
 (must-fail
  (defthm art-teeth-preserves-source-without-successful-parse
    (equal (fn-article-source
            (fn-article-result-article (fn-article-parse *art-teeth-unterminated*)))
           *art-teeth-unterminated*))))

; A second refused input, this one refused for field syntax rather than
; framing, so the case does not rest on one error path.
(defconst *art-teeth-bare-lf* '(83 117 98 106 101 99 116 58 32 120 10 10))
(assert-event (equal (fn-article-parse *art-teeth-bare-lf*)
                     '(:error :invalid-header)))

(local
 (must-fail
  (defthm art-teeth-preserves-source-without-crlf-framing
    (equal (fn-article-source
            (fn-article-result-article (fn-article-parse *art-teeth-bare-lf*)))
           *art-teeth-bare-lf*))))
