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

; Exact conclusion of the universal block-renderer / fn-wire-drive theorem.
(defmacro fn-wire-block-render-roundtripp
  (article article-limit body-limit)
  `(let ((lines (fn-wire-outbound-octets
                 (fn-wire-outbound-lines ,article ,article-limit))))
     (and
      (equal
       (fn-wire-drive
        (fn-wire-outbound-receiver-start ,body-limit)
        (fn-wire-outbound-octets
         (fn-wire-render-block ,article ,article-limit)))
       (fn-wire-make-result
        (fn-wire-make-state :command nil 0 nil nil 0
                            (+ 1 (nfix ,body-limit))
                            (nfix ,body-limit))
        (list (fn-wire-article-event lines))))
      (equal (fn-wire-source-lines lines) ,article))))

; Non-degenerate witness and one counterexample per premise of
; fn-wire-drive-of-successful-render-block-preserves-source.
(assert-event
 (fn-wire-block-render-roundtripp
  *fn-wire-outbound-proof-witness* 64 64))
(must-fail
 (assert-event (fn-wire-block-render-roundtripp nil 0 0)))
(must-fail
 (assert-event (fn-wire-block-render-roundtripp '(120 10) 8 64)))
(must-fail
 (assert-event (fn-wire-block-render-roundtripp '(120 13 10) 3 2)))

; Exact conclusion of the host-renderer / served-profile composition theorem.
; This macro only keeps the ground witness and hypothesis teeth readable.
(defmacro fn-wire-host-render-roundtripp
  (article command-limit article-limit body-limit)
  `(let ((lines (fn-wire-outbound-octets
                 (fn-wire-outbound-lines ,article ,article-limit))))
     (and
      (equal
       (fn-wire-drive
        (fn-wire-result-state
         (fn-wire-begin-article-with-line-limit
          (fn-wire-initial-state ,command-limit ,body-limit)
          (fn-wire-article-line-limit
           (fn-wire-initial-state ,command-limit ,body-limit))))
        (fn-wire-outbound-octets
         (fn-wire-render-feed-command
          ,article ,command-limit ,article-limit)))
       (fn-wire-make-result
        (fn-wire-make-state :command nil 0 nil nil 0
                            (+ 1 (nfix ,body-limit))
                            (nfix ,body-limit))
        (list (fn-wire-article-event lines))))
      (equal (fn-wire-source-lines lines) ,article))))

; Reachable, non-degenerate witness for the host-called renderer theorem.  It
; exercises ordinary, empty, dot-leading, dot-only and trailing-empty source
; lines through fn-wire-render-feed-command and the actual fn-wire-drive loop.
(assert-event
 (fn-wire-host-render-roundtripp
  *fn-wire-outbound-proof-witness* 32 64 64))

; Every premise of fn-wire-drive-of-host-rendered-article-preserves-source has
; a ground counterexample.  In each case all other premises hold.

; Without a positive command limit, the served initial state is inadmissible.
(must-fail
 (assert-event
  (fn-wire-host-render-roundtripp
   *fn-wire-outbound-proof-witness* 0 64 64)))

; Without nonempty article input, the host's NIL no-command arm emits no block.
(must-fail
 (assert-event (fn-wire-host-render-roundtripp nil 32 0 64)))

; Without exclusion of CHECK, the host emits an offer line without a block
; terminator, so an article-mode receiver cannot produce the claimed event.
(must-fail
 (assert-event
  (fn-wire-host-render-roundtripp
   '(67 72 69 67 75 32 60 105 64 110 62 13 10) 32 64 64)))

; IHAVE has the same command-only framing, independently exercising its branch
; exclusion while CHECK and TAKETHIS remain excluded.
(must-fail
 (assert-event
  (fn-wire-host-render-roundtripp
   '(73 72 65 86 69 32 60 105 64 110 62 13 10) 32 64 64)))

; A TAKETHIS command can succeed with an empty body under ARTICLE-LIMIT zero;
; starting its command line in article mode exceeds the independent body cap.
(must-fail
 (assert-event
  (fn-wire-host-render-roundtripp
   '(84 65 75 69 84 72 73 83 32 60 105 64 110 62 13 10) 32 0 1)))

; Without renderer success, a bare LF is refused and cannot reconstruct the
; claimed source or produce its article event.
(must-fail
 (assert-event (fn-wire-host-render-roundtripp '(120 10) 32 8 64)))

; Without ARTICLE-LIMIT <= BODY-LIMIT, rendering succeeds but the receiver
; closes on its cumulative decoded-body bound before producing an article.
(must-fail
 (assert-event (fn-wire-host-render-roundtripp '(120 13 10) 32 3 2)))
