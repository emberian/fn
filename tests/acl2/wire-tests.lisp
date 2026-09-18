; Executable boundary traces for the bounded NNTP wire framing model.
(in-package "ACL2")
(include-book "../../books/wire")

(defconst *fn-wire-empty* (fn-wire-initial-state 32 64))
(assert-event (fn-wire-statep *fn-wire-empty*))

; A command CRLF may be split at every byte boundary.
(defconst *fn-wire-command-split-a*
  (fn-wire-feed *fn-wire-empty* '(72 69 76 80 13)))
(assert-event (equal (fn-wire-result-events *fn-wire-command-split-a*) nil))
(defconst *fn-wire-command-split-b*
  (fn-wire-feed (fn-wire-result-state *fn-wire-command-split-a*) '(10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-command-split-b*)
        '((:command (72 69 76 80)))))

; A dot-stuffed line is data and a terminator split across chunks ends one body.
(defconst *fn-wire-article-start* (fn-wire-begin-article *fn-wire-empty*))
(defconst *fn-wire-article-part-a*
  (fn-wire-feed *fn-wire-article-start* '(46 46 102 105 114 115 116 13 10 46 13)))
(assert-event (equal (fn-wire-result-events *fn-wire-article-part-a*) nil))
(defconst *fn-wire-article-part-b*
  (fn-wire-feed (fn-wire-result-state *fn-wire-article-part-a*) '(10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-article-part-b*)
        '((:article ((46 102 105 114 115 116))))))

; The empty article is distinct from malformed input and completes on dot CRLF.
(defconst *fn-wire-empty-article*
  (fn-wire-feed *fn-wire-article-start* '(46 13 10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-empty-article*) '((:article nil))))

; A line over limit closes the connection.  Its apparent CRLF and a command
; after it are discarded, so rejected article tails never become commands.
(defconst *fn-wire-tiny-article*
  (fn-wire-begin-article (fn-wire-initial-state 3 64)))
(defconst *fn-wire-overlong*
  (fn-wire-feed *fn-wire-tiny-article*
                '(97 98 99 100 13 10 72 69 76 80 13 10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-overlong*) '((:reject :line-overlimit))))
(assert-event
 (equal (fn-wire-state-mode (fn-wire-result-state *fn-wire-overlong*)) :closed))
(assert-event
 (equal (fn-wire-result-events
         (fn-wire-feed (fn-wire-result-state *fn-wire-overlong*) '(81 13 10)))
        nil))

; Bare LF and CR followed by a non-LF are malformed and close rather than
; resynchronizing to a body or command boundary.
(defconst *fn-wire-bare-lf* (fn-wire-feed *fn-wire-empty* '(72 10 73 13 10)))
(assert-event (equal (fn-wire-result-events *fn-wire-bare-lf*) '((:reject :malformed))))
(defconst *fn-wire-bad-cr* (fn-wire-feed *fn-wire-empty* '(72 13 73 13 10)))
(assert-event (equal (fn-wire-result-events *fn-wire-bad-cr*) '((:reject :malformed))))

; Total retained body bytes are bounded, after dot unstuffing and with CRLF
; accounted for.  The second line is rejected before it becomes an article.
(defconst *fn-wire-small-body*
  (fn-wire-begin-article (fn-wire-initial-state 16 3)))
(defconst *fn-wire-body-overlimit*
  (fn-wire-feed *fn-wire-small-body* '(97 98 13 10 46 13 10)))
(assert-event
 (equal (fn-wire-result-events *fn-wire-body-overlimit*) '((:reject :body-overlimit))))

; The executable partition law is exercised with an article split inside its
; CRLF and a separately chunked continuation.
(defconst *fn-wire-partition-whole*
  (fn-wire-feed *fn-wire-article-start* '(120 13 10 46 13 10)))
(defconst *fn-wire-partition-split*
  (fn-wire-continue
   (fn-wire-feed *fn-wire-article-start* '(120 13))
   '(10 46 13 10)))
(assert-event (equal *fn-wire-partition-whole* *fn-wire-partition-split*))
