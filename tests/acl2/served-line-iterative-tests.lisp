; Teeth for the served path's constant-stack line folds (lane
; served-line-iterative, 2026-09-26): fn-nntp-stuff-lines (books/nntp-session,
; the multi-line block of every ARTICLE, HEAD, BODY, OVER and HDR reply) and
; fn-post-body-octets (books/nntp-post, the POST's article reassembled from
; the wire's lines).  Both keystones have no hypotheses, so each gets a
; reachable non-degenerate witness, a served-size witness through the
; compiled executable (the size that exhausted the owner's 64 MiB control
; stack before this lane), and labelled MUTATION witnesses: plausible loops
; that are not the definition, each refuted on a concrete input (the
; must-fail is that ground instance, so its failure is a counterexample and
; not a failed proof search).
(in-package "ACL2")
(include-book "../../books/nntp-post")
(include-book "std/testing/must-fail" :dir :system)

; The host runs the loop: both subjects are guard-verified, so the host's
; call (fn-owner-chunk-span -> ... -> fn-nntp-article-response and
; fn-nntp-post-step) executes the :exec body.
(assert-event
 (and (eq (symbol-class 'fn-nntp-stuff-lines (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-post-body-octets (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-nntp-stuff-lines-iter (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-post-body-octets-iter (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; fn-nntp-stuff-lines-iter-is-stuff-lines

; Reachable witness: a dot-led line (stuffed), an empty line, a lone dot (the
; terminator's shape, stuffed so it is not one), and an ordinary line.
(defconst *sli-t-lines* '((46 97) () (46) (104 105)))
(defconst *sli-t-block* '(46 46 97 13 10  13 10  46 46 13 10  104 105 13 10))
(assert-event (equal (fn-nntp-stuff-lines-iter *sli-t-lines*) *sli-t-block*))
(assert-event (equal (fn-nntp-stuff-lines *sli-t-lines*) *sli-t-block*))

; Composed: the ARTICLE reply for a stored article is the initial line, the
; stuffed block and the terminator, and it answers 220.
(defconst *sli-t-payload*
  '(83 58 32 120 13 10  13 10  46 13 10  46 46 121 13 10))   ; "S: x", "", ".", "..y"
(defconst *sli-t-article*
  (fn-make-article "<sli@example.invalid>" *sli-t-payload* '("fn.test") nil t nil))
(defconst *sli-t-section* (fn-nntp-article-section *sli-t-article* :body))
(assert-event (equal *sli-t-section* '(:ok ((46) (46 46 121)))))
(assert-event (equal (fn-nntp-stuff-lines (cadr *sli-t-section*))
                     '(46 46 13 10  46 46 46 121 13 10)))
(defconst *sli-t-reply*
  (fn-nntp-article-response (fn-nntp-make-session t "fn.test" nil t)
                            *sli-t-article* 1 :body t "fn.test"))
(assert-event
 (equal (fn-nntp-result-effects *sli-t-reply*)
        (list (fn-nntp-reply-effect
               (append (fn-nntp-string-octets "222 1 <sli@example.invalid> body follows")
                       '(13 10  46 46 13 10  46 46 46 121 13 10  46 13 10))))))

; Served size: 2,100,000 lines, past the two million that exhausted the
; owner's 64 MiB control stack with the per-line recursion; every other line
; dot-led.  The executable returns, and its length is the specification's:
; 2,100,000 x 2 CRLF octets + 2,100,000 line octets + 1,050,000 stuffed dots.
(defun sli-t-alternating (n acc)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      acc
    (sli-t-alternating (1- n) (cons (if (evenp n) '(46) '(120)) acc))))

(assert-event
 (equal (len (fn-nntp-stuff-lines (sli-t-alternating 2100000 nil)))
        (+ (* 2 2100000) 2100000 1050000)))

; MUTATION (labelled): a loop that lays each line on in order instead of in
; reverse, then turns the block round, reverses every line's octets.
(defun sli-t-mut-stuff-onto (lines acc)
  (declare (xargs :guard t))
  (if (consp lines)
      (sli-t-mut-stuff-onto (cdr lines)
                            (cons 10 (cons 13 (fn-ag-append (fn-wire-stuff-line (car lines))
                                                            acc))))
    acc))
(assert-event
 (not (equal (fn-ag-rev-onto (sli-t-mut-stuff-onto *sli-t-lines* nil) nil)
             (fn-nntp-stuff-lines *sli-t-lines*))))
(must-fail
 (defthm sli-t-mut-stuff-is-stuff-lines
   (equal (fn-ag-rev-onto (sli-t-mut-stuff-onto *sli-t-lines* nil) nil)
          (fn-nntp-stuff-lines *sli-t-lines*))))

; MUTATION (labelled): the loop without the stuffing; on a line with no
; leading dot it agrees, so the witness is the dot-led line.
(defun sli-t-mut-unstuffed-onto (lines acc)
  (declare (xargs :guard t))
  (if (consp lines)
      (sli-t-mut-unstuffed-onto (cdr lines)
                                (cons 10 (cons 13 (fn-ag-rev-onto (car lines) acc))))
    acc))
(assert-event
 (equal (fn-ag-rev-onto (sli-t-mut-unstuffed-onto '((104 105)) nil) nil)
        (fn-nntp-stuff-lines '((104 105)))))
(assert-event
 (not (equal (fn-ag-rev-onto (sli-t-mut-unstuffed-onto *sli-t-lines* nil) nil)
             (fn-nntp-stuff-lines *sli-t-lines*))))
(must-fail
 (defthm sli-t-mut-unstuffed-is-stuff-lines
   (equal (fn-ag-rev-onto (sli-t-mut-unstuffed-onto *sli-t-lines* nil) nil)
          (fn-nntp-stuff-lines *sli-t-lines*))))

; -----------------------------------------------------------------------------
; fn-post-body-octets-iter-is-body-octets

; Reachable witness: the POST tests' article (header lines, the empty
; separator, a body line), reassembled with CRLF after every line.
(defconst *sli-t-post-lines*
  (list '(70 58 32 97) '(83 58 32 98) '() '(46 104 105)))
(defconst *sli-t-post-octets*
  '(70 58 32 97 13 10  83 58 32 98 13 10  13 10  46 104 105 13 10))
(assert-event (equal (fn-post-body-octets-iter *sli-t-post-lines*) *sli-t-post-octets*))
(assert-event (equal (fn-post-body-octets *sli-t-post-lines*) *sli-t-post-octets*))

; Served size, both shapes the profile admits: 2,100,000 lines, and one line
; of 20,000,000 octets (the article line limit is the article bound plus one,
; books/wire.lisp fn-wire-article-line-limit, so one line may be the whole
; article; the recursion it replaced took a frame per octet of it).
(assert-event
 (equal (len (fn-post-body-octets (sli-t-alternating 2100000 nil)))
        (* 3 2100000)))
(assert-event
 (equal (len (fn-post-body-octets (list (make-list 20000000 :initial-element 120))))
        20000002))

; MUTATION (labelled): CRLF between lines instead of after each; the last
; line then lacks its CRLF and the injection would see a truncated article.
(defun sli-t-mut-join-onto (lines acc)
  (declare (xargs :guard t))
  (if (consp lines)
      (sli-t-mut-join-onto (cdr lines)
                           (let ((acc (fn-ag-rev-onto (car lines) acc)))
                             (if (consp (cdr lines)) (cons 10 (cons 13 acc)) acc)))
    acc))
(assert-event
 (not (equal (fn-ag-rev-onto (sli-t-mut-join-onto *sli-t-post-lines* nil) nil)
             (fn-post-body-octets *sli-t-post-lines*))))
(must-fail
 (defthm sli-t-mut-join-is-body-octets
   (equal (fn-ag-rev-onto (sli-t-mut-join-onto *sli-t-post-lines* nil) nil)
          (fn-post-body-octets *sli-t-post-lines*))))
