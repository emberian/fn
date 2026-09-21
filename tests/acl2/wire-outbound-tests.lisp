; Teeth for the universal outbound scanner and renderer evidence.  These use
; the actual ACL2 functions the feed host calls; no host-language formatter is
; involved.
(in-package "ACL2")
(include-book "../../books/wire-outbound-invariants")
(include-book "std/testing/must-fail" :dir :system)

; A reachable non-degenerate article: it has an empty header/body separator,
; a literal dot-leading line, a dot-only line, and two preserved final empty
; lines.  It separates byte-preserving CRLF framing from a generic text
; splitter or a newline-trimming renderer.
(defconst *fn-wire-outbound-proof-witness*
  '(83 117 98 106 101 99 116 58 32 116 13 10 13 10
    46 108 105 116 101 114 97 108 13 10 46 13 10
    98 111 100 121 13 10 13 10 13 10))

(defconst *fn-wire-outbound-proof-parsed*
  (fn-wire-outbound-lines *fn-wire-outbound-proof-witness* 64))
(assert-event (fn-wire-outbound-okp *fn-wire-outbound-proof-parsed*))
(assert-event
 (equal (fn-wire-source-lines
         (fn-wire-outbound-octets *fn-wire-outbound-proof-parsed*))
        *fn-wire-outbound-proof-witness*))

(defconst *fn-wire-outbound-proof-rendered*
  (fn-wire-render-block *fn-wire-outbound-proof-witness* 64))
(assert-event (fn-wire-outbound-okp *fn-wire-outbound-proof-rendered*))
(assert-event
 (equal (fn-wire-outbound-octets *fn-wire-outbound-proof-rendered*)
        '(83 117 98 106 101 99 116 58 32 116 13 10 13 10
          46 46 108 105 116 101 114 97 108 13 10 46 46 13 10
          98 111 100 121 13 10 13 10 13 10 46 13 10)))
(assert-event
 (<= (len (fn-wire-outbound-octets *fn-wire-outbound-proof-rendered*))
     (+ 3 (* 2 (len *fn-wire-outbound-proof-witness*)))))

; Empty is an accepted article, not a refusal sentinel, and has only the
; physical dot terminator.  It exercises the zero-line side of both proofs.
(assert-event
 (equal (fn-wire-outbound-octets (fn-wire-render-block nil 1)) '(46 13 10)))
(assert-event
 (equal (fn-wire-source-lines
         (fn-wire-outbound-octets (fn-wire-outbound-lines nil 1))) nil))

; Teeth for the sole premise of reconstruction: a bare LF cannot be treated
; as an accepted line spelling, so its empty result does not reconstruct the
; source.  The bound tooth separately shows that an otherwise valid source is
; refused when its total byte budget is removed.
(defconst *fn-wire-outbound-proof-bare-lf* '(120 10))
(assert-event
 (equal (fn-wire-outbound-reason
         (fn-wire-outbound-lines *fn-wire-outbound-proof-bare-lf* 8))
        :bare-lf))
(must-fail
 (assert-event
  (equal (fn-wire-source-lines
          (fn-wire-outbound-octets
           (fn-wire-outbound-lines *fn-wire-outbound-proof-bare-lf* 8)))
         *fn-wire-outbound-proof-bare-lf*)))
(assert-event
 (equal (fn-wire-outbound-reason
         (fn-wire-render-block '(120 13 10) 2))
        :overlimit))
(must-fail
 (assert-event (fn-wire-outbound-okp (fn-wire-render-block '(120 13 10) 2))))
