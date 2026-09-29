; Universal outbound NNTP block evidence.  This book starts at the actual
; renderer scanner, not a Python spelling of it, and keeps the source-tail
; invariant separate from the receiver composition below.
(in-package "ACL2")
(include-book "wire-invariants")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-wire-octet-listp)
                          (:rewrite fn-wire-octet-listp-cdr))))

; Reattach source CRLF delimiters to forward-order source lines.  The second
; form takes a tail and consumes a reverse-order accumulator; its continuation
; shape is what the scanner's ordinary octet branch preserves by definition.
(defun fn-wire-source-lines (lines)
  (declare (xargs :guard t :measure (acl2-count lines)))
  (if (consp lines)
      (fn-wire-append (car lines)
                      (fn-wire-append '(13 10)
                                      (fn-wire-source-lines (cdr lines))))
    nil))

(defun fn-wire-source-lines-rev (lines-rev tail)
  (declare (xargs :guard t :measure (acl2-count lines-rev)))
  (if (consp lines-rev)
      (fn-wire-source-lines-rev
       (cdr lines-rev)
       (fn-wire-append (car lines-rev)
                       (fn-wire-append '(13 10) tail)))
    tail))

; This generalized accumulator identity is the reverse bridge needed at an
; accepted CRLF.  Its induction follows the actual reverse helper and leaves
; the arbitrary tail untouched, avoiding a singleton-specialization rewrite.
(defthm fn-wire-reverse-octets-aux-onto-tail
  (equal (fn-wire-append
          (fn-wire-reverse-octets-aux octets accumulator) tail)
         (revappend octets (fn-wire-append accumulator tail)))
  :hints (("Goal"
           :induct (fn-wire-reverse-octets-aux octets accumulator)
           :in-theory (enable fn-wire-reverse-octets-aux
                              fn-wire-append revappend))))

(defthm fn-wire-reverse-octets-onto-tail
  (equal (fn-wire-append (fn-wire-reverse-octets octets) tail)
         (revappend octets tail))
  :hints (("Goal"
           :use ((:instance fn-wire-reverse-octets-aux-onto-tail
                            (accumulator nil)))
           :in-theory (enable fn-wire-reverse-octets))))

; Reversing the completed-line stack and rendering its source spelling is the
; same as threading the source tail through that stack.  This is a parser
; reconstruction fact, not a condition assumed by the eventual round trip.
(defthm fn-wire-source-lines-of-reverse-lines-aux
  (equal (fn-wire-source-lines
          (fn-wire-reverse-lines-aux lines accumulator))
         (fn-wire-source-lines-rev lines
                                   (fn-wire-source-lines accumulator)))
  :hints (("Goal"
           :induct (fn-wire-reverse-lines-aux lines accumulator)
           :in-theory (enable fn-wire-reverse-lines-aux
                              fn-wire-source-lines
                              fn-wire-source-lines-rev))))

(defthm fn-wire-source-lines-of-reverse-lines
  (equal (fn-wire-source-lines (fn-wire-reverse-lines lines))
         (fn-wire-source-lines-rev lines nil))
  :hints (("Goal"
           :use ((:instance fn-wire-source-lines-of-reverse-lines-aux
                            (accumulator nil)))
           :in-theory (enable fn-wire-reverse-lines
                              fn-wire-source-lines))))

; Successful scanner output reconstructs the source represented by its
; current line and its unread suffix.  At the public entry point both
; accumulators are nil, yielding exact input-byte reconstruction.
(defthm fn-wire-outbound-lines-aux-success-reconstructs-source
  (implies (fn-wire-outbound-okp
            (fn-wire-outbound-lines-aux octets fuel line-rev lines-rev))
           (equal
            (fn-wire-source-lines
             (fn-wire-outbound-octets
              (fn-wire-outbound-lines-aux octets fuel line-rev lines-rev)))
            (fn-wire-source-lines-rev lines-rev
                                      (revappend line-rev octets))))
  :hints (("Goal"
           :induct (fn-wire-outbound-lines-aux octets fuel line-rev lines-rev)
           :do-not '(generalize fertilize)
           :in-theory (e/d (fn-wire-outbound-lines-aux
                             fn-wire-outbound-okp
                             fn-wire-outbound-octets
                             fn-wire-outbound-ok
                             fn-wire-outbound-refused
                             fn-wire-source-lines
                             fn-wire-source-lines-rev
                             revappend)
                            (fn-wire-reverse-octets-is-revappend
                             fn-wire-reverse-octets-aux-is-revappend)))))

(defthm fn-wire-outbound-lines-success-reconstructs-source
  (implies (fn-wire-outbound-okp (fn-wire-outbound-lines octets limit))
           (equal (fn-wire-source-lines
                   (fn-wire-outbound-octets
                    (fn-wire-outbound-lines octets limit)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-wire-outbound-lines-aux-success-reconstructs-source
                            (fuel (nfix limit)) (line-rev nil) (lines-rev nil)))
           :in-theory (enable fn-wire-outbound-lines))))

; Rendering grows a source line by at most its one possible leading-dot
; escape.  The following size facts deliberately cover the actual renderer
; (`fn-wire-render-lines' and `fn-wire-render-block'), rather than a shadow
; list printer in the host.
(defthm fn-wire-append-length
  (equal (len (fn-wire-append left right))
         (+ (len left) (len right)))
  :hints (("Goal"
           :induct (fn-wire-append left right)
           :in-theory (enable fn-wire-append))))

(defthm fn-wire-stuff-line-length-at-most-one-more
  (<= (len (fn-wire-stuff-line line))
      (+ 1 (len line)))
  :hints (("Goal" :in-theory (enable fn-wire-stuff-line))))

(defthm fn-wire-source-lines-length-is-lines-size
  (equal (len (fn-wire-source-lines lines))
         (fn-wire-lines-size lines))
  :hints (("Goal"
           :induct (fn-wire-source-lines lines)
           :in-theory (enable fn-wire-source-lines
                              fn-wire-lines-size
                              fn-wire-line-cost))))

(defthm fn-wire-lines-size-natp
  (natp (fn-wire-lines-size lines))
  :hints (("Goal"
           :induct (fn-wire-lines-size lines)
           :in-theory (enable fn-wire-lines-size fn-wire-line-cost))))

(defthm fn-wire-render-lines-length-at-most-double-source
  (<= (len (fn-wire-render-lines lines))
      (* 2 (fn-wire-lines-size lines)))
  :hints (("Goal"
           :induct (fn-wire-render-lines lines)
           :in-theory (enable fn-wire-render-lines
                              fn-wire-lines-size
                              fn-wire-line-cost
                              fn-wire-lines-size-natp
                              fn-wire-stuff-line))))

(defthm fn-wire-plus-three-preserves-<=
  (implies (<= left right)
           (<= (+ 3 left) (+ 3 right))))

(defthm fn-wire-render-lines-terminator-length-from-lines-size
  (<= (len (fn-wire-append (fn-wire-render-lines lines) '(46 13 10)))
      (+ 3 (* 2 (fn-wire-lines-size lines))))
  :hints (("Goal"
           :use ((:instance fn-wire-render-lines-length-at-most-double-source)
                 (:instance fn-wire-plus-three-preserves-<=
                            (left (len (fn-wire-render-lines lines)))
                            (right (* 2 (fn-wire-lines-size lines)))))
           :in-theory (enable fn-wire-append))))

(defthm fn-wire-source-lines-equal-implies-lines-size
  (implies (equal (fn-wire-source-lines lines) article)
           (equal (fn-wire-lines-size lines) (len article)))
  :hints (("Goal"
           :use ((:instance fn-wire-source-lines-length-is-lines-size)))))

(defthm fn-wire-render-lines-terminator-length-from-source
  (implies (equal (fn-wire-source-lines lines) article)
           (<= (len (fn-wire-append (fn-wire-render-lines lines) '(46 13 10)))
               (+ 3 (* 2 (len article)))))
  :hints (("Goal"
           :use ((:instance fn-wire-render-lines-terminator-length-from-lines-size)
                 (:instance fn-wire-source-lines-equal-implies-lines-size))
           :in-theory (disable fn-wire-append-length))))

; A successful block adds at most one dot per source line, then exactly the
; three-octet terminator.  Its source is bounded by the same total byte count
; accepted by `fn-wire-outbound-lines', so this conservative physical bound is
; valid for all accepted source spellings, including empty and trailing-empty
; articles.
(defthm fn-wire-render-block-output-length-at-most-double-source-plus-terminator
  (implies (fn-wire-outbound-okp (fn-wire-render-block article limit))
           (<= (len (fn-wire-outbound-octets
                     (fn-wire-render-block article limit)))
               (+ 3 (* 2 (len article)))))
  :hints (("Goal"
           :in-theory (e/d (fn-wire-render-block
                             fn-wire-outbound-okp
                             fn-wire-outbound-octets
                             fn-wire-outbound-ok)
                            (fn-wire-append fn-wire-render-lines
                             fn-wire-append-length))
           :use ((:instance fn-wire-render-lines-terminator-length-from-source
                            (lines (fn-wire-outbound-octets
                                    (fn-wire-outbound-lines article limit))))
                 (:instance fn-wire-outbound-lines-success-reconstructs-source
                            (octets article))))))

; ---------------------------------------------------------------------------
; Receiver-side admission facts extracted from the same outbound scanner.
; They justify the article profile without constraining accepted source lines
; to the command limit: an accepted source consumes at most its *total* bound,
; while one leading dot can add one physical octet on the wire.

(defun fn-wire-clean-linesp (lines)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count lines)))
  (if (consp lines)
      (and (fn-wire-line-contentp (car lines))
           (fn-wire-clean-linesp (cdr lines)))
    (null lines)))

(defthm fn-wire-line-contentp-reverse-octets-aux
  (implies (and (fn-wire-line-contentp line)
                (fn-wire-line-contentp accumulator))
           (fn-wire-line-contentp
            (fn-wire-reverse-octets-aux line accumulator)))
  :hints (("Goal"
           :induct (fn-wire-reverse-octets-aux line accumulator)
           :in-theory (enable fn-wire-line-contentp
                              fn-wire-reverse-octets-aux))))

(defthm fn-wire-line-contentp-reverse-octets
  (implies (fn-wire-line-contentp line)
           (fn-wire-line-contentp (fn-wire-reverse-octets line)))
  :hints (("Goal"
           :use ((:instance fn-wire-line-contentp-reverse-octets-aux
                            (accumulator nil)))
           :in-theory (enable fn-wire-reverse-octets fn-wire-line-contentp))))

(defthm fn-wire-clean-linesp-reverse-lines-aux
  (implies (and (fn-wire-clean-linesp lines)
                (fn-wire-clean-linesp accumulator))
           (fn-wire-clean-linesp
            (fn-wire-reverse-lines-aux lines accumulator)))
  :hints (("Goal"
           :induct (fn-wire-reverse-lines-aux lines accumulator)
           :in-theory (enable fn-wire-clean-linesp
                              fn-wire-reverse-lines-aux))))

(defthm fn-wire-clean-linesp-reverse-lines
  (implies (fn-wire-clean-linesp lines)
           (fn-wire-clean-linesp (fn-wire-reverse-lines lines)))
  :hints (("Goal"
           :use ((:instance fn-wire-clean-linesp-reverse-lines-aux
                            (accumulator nil)))
           :in-theory (enable fn-wire-reverse-lines fn-wire-clean-linesp))))

(defthm fn-wire-outbound-lines-aux-success-is-clean
  (implies (and (fn-wire-outbound-okp
                 (fn-wire-outbound-lines-aux octets fuel line-rev lines-rev))
                (fn-wire-line-contentp line-rev)
                (fn-wire-clean-linesp lines-rev))
           (fn-wire-clean-linesp
            (fn-wire-outbound-octets
             (fn-wire-outbound-lines-aux octets fuel line-rev lines-rev))))
  :hints (("Goal"
           :induct (fn-wire-outbound-lines-aux octets fuel line-rev lines-rev)
           :in-theory (e/d (fn-wire-outbound-lines-aux
                             fn-wire-outbound-okp
                             fn-wire-outbound-octets
                             fn-wire-outbound-ok
                             fn-wire-outbound-refused
                             fn-wire-line-contentp
                             fn-wire-clean-linesp)
                            (fn-wire-reverse-octets-is-revappend
                             fn-wire-reverse-octets-aux-is-revappend)))))

(defthm fn-wire-outbound-lines-success-is-clean
  (implies (fn-wire-outbound-okp (fn-wire-outbound-lines octets limit))
           (fn-wire-clean-linesp
            (fn-wire-outbound-octets (fn-wire-outbound-lines octets limit))))
  :hints (("Goal"
           :use ((:instance fn-wire-outbound-lines-aux-success-is-clean
                            (fuel (nfix limit)) (line-rev nil) (lines-rev nil)))
           :in-theory (enable fn-wire-outbound-lines
                              fn-wire-line-contentp fn-wire-clean-linesp))))

(defthm fn-wire-outbound-lines-aux-success-respects-fuel
  (implies (fn-wire-outbound-okp
            (fn-wire-outbound-lines-aux octets fuel line-rev lines-rev))
           (<= (len octets) (nfix fuel)))
  :hints (("Goal"
           :induct (fn-wire-outbound-lines-aux octets fuel line-rev lines-rev)
           :in-theory (enable fn-wire-outbound-lines-aux
                              fn-wire-outbound-okp
                              fn-wire-outbound-ok
                              fn-wire-outbound-refused))))

(defthm fn-wire-outbound-lines-success-respects-limit
  (implies (fn-wire-outbound-okp (fn-wire-outbound-lines octets limit))
           (<= (len octets) (nfix limit)))
  :hints (("Goal"
           :use ((:instance fn-wire-outbound-lines-aux-success-respects-fuel
                            (fuel (nfix limit)) (line-rev nil) (lines-rev nil)))
           :in-theory (enable fn-wire-outbound-lines))))

(defthm fn-wire-line-contentp-implies-octet-listp
  (implies (fn-wire-line-contentp line)
           (fn-wire-octet-listp line))
  :hints (("Goal"
           :induct (fn-wire-line-contentp line)
           :in-theory (enable fn-wire-line-contentp))))

(defthm fn-wire-line-contentp-implies-true-listp
  (implies (fn-wire-line-contentp line)
           (true-listp line))
  :hints (("Goal"
           :use ((:instance fn-wire-line-contentp-implies-octet-listp)
                 (:instance fn-wire-octet-list-is-true-list
                            (octets line)))
           :in-theory (disable fn-wire-line-contentp-implies-octet-listp
                               fn-wire-octet-list-is-true-list))))

(defthm fn-wire-line-contentp-of-stuff-line
  (implies (fn-wire-line-contentp line)
           (fn-wire-line-contentp (fn-wire-stuff-line line)))
  :hints (("Goal" :in-theory (enable fn-wire-stuff-line
                                      fn-wire-line-contentp))))

(defthm fn-wire-lines-size-of-append
  (equal (fn-wire-lines-size (append left right))
         (+ (fn-wire-lines-size left)
            (fn-wire-lines-size right)))
  :hints (("Goal"
           :induct (append left right)
           :in-theory (enable fn-wire-lines-size))))

(defthm fn-wire-lines-size-of-cdr-is-at-most-lines-size
  (<= (fn-wire-lines-size (cdr lines))
      (fn-wire-lines-size lines))
  :hints (("Goal" :in-theory (enable fn-wire-lines-size
                                      fn-wire-line-cost))))

(defthm fn-wire-first-line-fits-total-body-bound
  (implies (and (consp lines)
                (<= (+ body-size (fn-wire-lines-size lines)) body-limit))
           (<= (+ body-size (fn-wire-line-cost (car lines))) body-limit))
  :hints (("Goal" :in-theory (enable fn-wire-lines-size
                                      fn-wire-line-cost))))

(defthm fn-wire-rest-lines-fit-after-first
  (implies (and (consp lines)
                (<= (+ body-size (fn-wire-lines-size lines)) body-limit))
           (<= (+ body-size
                  (fn-wire-line-cost (car lines))
                  (fn-wire-lines-size (cdr lines)))
               body-limit))
  :hints (("Goal" :in-theory (enable fn-wire-lines-size))))

; `fn-wire-list-length' counts conses and stops at a non-cons, which is what
; `len' does on every object; books/wire keeps its own recursion so the line
; cost function does not depend on the arithmetic vocabulary.  The stuffing
; bound above is stated in `len' and `fn-wire-line-cost' is stated in
; `fn-wire-list-length', so the cumulative bound below cannot see that its two
; halves measure the same list without this bridge.  Local: the equality is
; proof vocabulary here, not a fact this book exports.
(local (defthm fn-wire-list-length-is-len
         (equal (fn-wire-list-length xs) (len xs))
         :hints (("Goal" :in-theory (enable fn-wire-list-length)))))

(defthm fn-wire-stuffed-first-line-length-at-most-lines-size
  (implies (consp lines)
           (<= (len (fn-wire-stuff-line (car lines)))
               (fn-wire-lines-size lines)))
  :hints (("Goal"
           :use ((:instance fn-wire-stuff-line-length-at-most-one-more
                            (line (car lines)))
                 (:instance fn-wire-lines-size-natp
                            (lines (cdr lines))))
           :in-theory (e/d (fn-wire-lines-size fn-wire-line-cost)
                           (fn-wire-stuff-line-length-at-most-one-more
                            fn-wire-lines-size-natp))
           :do-not-induct t)))

(defthm fn-wire-stuffed-line-fits-article-profile
  (implies (and (consp lines)
                (natp body-size)
                (natp body-limit)
                (natp line-limit)
                (<= (+ body-size (fn-wire-lines-size lines)) body-limit)
                (<= (+ 1 body-limit) line-limit))
           (<= (len (fn-wire-stuff-line (car lines))) line-limit))
  :hints (("Goal"
           :use ((:instance fn-wire-stuffed-first-line-length-at-most-lines-size))
           :in-theory (disable fn-wire-stuff-line
                               fn-wire-lines-size
                               fn-wire-stuffed-first-line-length-at-most-lines-size)
           :do-not-induct t)))

(defthm fn-wire-append-when-true-listp
  (implies (true-listp left)
           (equal (fn-wire-append left right)
                  (append left right)))
  :hints (("Goal"
           :induct (fn-wire-append left right)
           :in-theory (enable fn-wire-append))))

(defthm fn-wire-octet-listp-of-total-append
  (implies (and (fn-wire-octet-listp left)
                (fn-wire-octet-listp right))
           (fn-wire-octet-listp (fn-wire-append left right)))
  :hints (("Goal"
           :induct (fn-wire-append left right)
           :in-theory (enable fn-wire-append))))

(defthm fn-wire-rendered-line-prefix-is-append
  (implies (true-listp source)
           (equal
            (fn-wire-append (fn-wire-stuff-line source)
                            (fn-wire-append '(13 10) tail))
            (append (append (fn-wire-stuff-line source) '(13 10)) tail)))
  :hints (("Goal"
           :in-theory (enable fn-wire-append fn-wire-stuff-line))))

(defthm fn-wire-rendered-block-cons-decomposition
  (implies
   (true-listp source)
   (equal
    (fn-wire-append
     (fn-wire-append (fn-wire-stuff-line source)
                     (list* 13 10 rendered-rest))
     '(46 13 10))
    (append
     (append (fn-wire-stuff-line source) '(13 10))
     (fn-wire-append rendered-rest '(46 13 10)))))
  :hints (("Goal"
           :in-theory (enable fn-wire-append fn-wire-stuff-line))))

(defthm fn-wire-append-associative
  (equal (fn-wire-append (fn-wire-append first second) third)
         (fn-wire-append first (fn-wire-append second third)))
  :hints (("Goal"
           :induct (fn-wire-append first second)
           :in-theory (enable fn-wire-append))))

(defthm fn-wire-octet-linesp-is-true-list
  (implies (fn-wire-octet-linesp lines)
           (true-listp lines))
  :hints (("Goal" :induct (fn-wire-octet-linesp lines))))

(defthm fn-wire-statep-has-positive-line-limit
  (implies (fn-wire-statep wire-state)
           (posp (fn-wire-state-line-limit wire-state)))
  :hints (("Goal" :in-theory (enable fn-wire-statep))))

; -----------------------------------------------------------------------------
; The receiver (lane chunked-body, B6).  In article mode the wire holds the
; body in a store (books/body-chunks.lisp); a rendered source line received
; from a line start appends the source octets and CR LF to it, whatever the
; stuffing did to the physical line.

(local (defthm fn-wire-reverse-lines-aux-is-rev-onto
         (equal (fn-wire-reverse-lines-aux lines acc)
                (fn-ag-rev-onto lines acc))
         :hints (("Goal" :in-theory (enable fn-wire-reverse-lines-aux)))))

(local (defthm fn-wire-list-length-is-len-2
         (equal (fn-wire-list-length xs) (len xs))
         :hints (("Goal" :in-theory (enable fn-wire-list-length)))))

(defthm fn-wire-stuff-line-of-atom
  (implies (not (consp source))
           (equal (fn-wire-stuff-line source) source))
  :hints (("Goal" :in-theory (enable fn-wire-stuff-line))))

(defthm fn-wire-line-contentp-of-stuff-line-2
  (implies (fn-wire-line-contentp source)
           (fn-wire-line-contentp (fn-wire-stuff-line source)))
  :hints (("Goal" :in-theory (enable fn-wire-stuff-line))))

(local (defthm fn-wire-append-assoc-list
         (equal (append (append a b) c) (append a (append b c)))))

(local (defthm fn-wire-len-of-consp-positive
         (implies (consp x) (< 0 (len x)))
         :rule-classes :linear))

(defthm fn-wire-feed-proper-of-article-crlf-then
  (equal (fn-wire-feed-proper
          (fn-wire-make-state :article nil l body nil body-size line-limit body-limit)
          (list* 13 10 tail))
         (let ((r (fn-wire-after-line
                   (fn-wire-make-state :article nil l body nil body-size line-limit body-limit)
                   nil)))
           (fn-wire-make-result
            (fn-wire-result-state (fn-wire-feed-proper (fn-wire-result-state r) tail))
            (append (fn-wire-result-events r)
                    (fn-wire-result-events (fn-wire-feed-proper (fn-wire-result-state r) tail))))))
  :hints (("Goal" :use ((:instance fn-wire-feed-proper-append
                                   (wire-state (fn-wire-make-state :article nil l body nil body-size
                                                                   line-limit body-limit))
                                   (left '(13 10)) (right tail)))
                  :in-theory (disable fn-wire-feed-proper-append fn-wire-feed-proper
                                      fn-wire-after-line))))

(local
 (defthm fn-wire-stuff-line-len-at-most-one-more
   (<= (len (fn-wire-stuff-line s)) (+ 1 (len s)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-wire-stuff-line)))))

(defthm fn-wire-feed-proper-of-rendered-source-line
  (implies
   (and (fn-bch-wfp body)
        (equal (fn-bch-length body) body-size)
        (fn-wire-line-contentp source)
        (<= (len (fn-wire-stuff-line source)) line-limit)
        (natp line-limit) (natp body-limit)
        (<= (+ body-size (fn-wire-line-cost source)) body-limit))
   (equal
    (fn-wire-feed-proper
     (fn-wire-make-state :article nil 0 body nil body-size line-limit body-limit)
     (append (append (fn-wire-stuff-line source) '(13 10)) tail))
    (fn-wire-feed-proper
     (fn-wire-make-state :article nil 0
                         (fn-bch-push-list body (append source '(13 10)))
                         nil
                         (+ body-size (fn-wire-line-cost source))
                         line-limit body-limit)
     tail)))
  :hints (("Goal"
           :in-theory (e/d (fn-wire-line-cost
                            fn-wire-result-state fn-wire-result-events fn-wire-make-result)
                           (fn-wire-feed-proper
                            fn-wire-after-line fn-wire-stuff-line
                            fn-wire-line-contentp))
           :cases ((consp source))
           :do-not-induct t)))

(defthm fn-wire-feed-proper-of-article-terminator
  (implies (and (posp line-limit)
                (natp body-size) (natp body-limit) (<= body-size body-limit)
                (equal (fn-bch-partial-len body body-size) 0))
           (equal
            (fn-wire-feed-proper
             (fn-wire-make-state :article nil 0 body nil body-size line-limit body-limit)
             '(46 13 10))
            (fn-wire-make-result
             (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)
             (list (fn-wire-article-event
                    (fn-ag-rev-onto (fn-bch-lines-rev body) nil))))))
  :hints (("Goal"
           :use ((:instance fn-wire-feed-proper-append
                            (wire-state (fn-wire-make-state :article nil 0 body nil body-size
                                                            line-limit body-limit))
                            (left '(46)) (right '(13 10)))
                 (:instance fn-wire-feed-proper-of-article-line-content
                            (xs '(46)) (l 0))
                 (:instance fn-wire-feed-proper-of-article-crlf (l 1)))
           :in-theory (e/d (fn-wire-result-state fn-wire-result-events fn-wire-make-result
                            fn-wire-reverse-lines)
                           (fn-wire-feed-proper fn-wire-feed-proper-append
                            fn-wire-feed-proper-of-article-line-content
                            fn-wire-feed-proper-of-article-crlf))
           :do-not-induct t)))

; A line start's store holds exactly the completed lines.
(defthm fn-wire-line-start-body-facts
  (implies (fn-bch-body-okp body body-size 0)
           (and (fn-bch-wfp body)
                (equal (fn-bch-length body) body-size)
                (equal (fn-bch-partial-len body body-size) 0)
                (equal (fn-bch-held-partial body body-size) nil)))
  :hints (("Goal" :use ((:instance fn-bch-body-okp-facts (b body) (n body-size) (l 0))
                        (:instance fn-bch-partial-len-plus (b body) (n body-size))))))

; The store after a received source line, from a line start.
(defthm fn-wire-received-line-body
  (implies (and (fn-bch-body-okp body body-size 0)
                (fn-wire-line-contentp source))
           (let ((body2 (fn-bch-push-list body (append source '(13 10))))
                 (size2 (+ body-size (fn-wire-line-cost source))))
             (and (fn-bch-body-okp body2 size2 0)
                  (equal (fn-bch-held-lines body2 size2)
                         (append (fn-bch-held-lines body body-size) (list source))))))
  :hints (("Goal"
           :use ((:instance fn-bch-body-okp-whole-line (b body) (n body-size) (xs source)))
           :in-theory (e/d (fn-wire-line-cost)
                           (fn-bch-body-okp-whole-line fn-wire-line-contentp))
           :do-not-induct t)))

; Follow the receiver state that the first rendered line establishes, so the
; induction hypothesis speaks about the actual cumulative counters and body.
(local
 (defun fn-wire-render-lines-induction (body body-size lines)
   (declare (xargs :guard t :verify-guards nil
                   :measure (acl2-count lines)))
   (if (consp lines)
       (fn-wire-render-lines-induction
        (fn-bch-push-list body (append (car lines) '(13 10)))
        (+ body-size (fn-wire-line-cost (car lines)))
        (cdr lines))
     (list body body-size))))

; Cumulative induction lemma: every clean source line and final dot terminator are
; delivered through the real byte feeder, in order, under the same cumulative
; body counter and physical-line ceiling the served path carries.  The result
; is one article event: the lines the store held and the exact source lines.
(defthm fn-wire-feed-proper-of-rendered-block-lines
  (implies
   (and (fn-bch-body-okp body body-size 0)
        (fn-wire-clean-linesp lines)
        (<= (+ body-size (fn-wire-lines-size lines)) body-limit)
        (<= (+ 1 body-limit) line-limit)
        (natp body-limit)
        (natp line-limit))
   (equal
    (fn-wire-feed-proper
     (fn-wire-make-state :article nil 0 body nil body-size line-limit body-limit)
     (fn-wire-append (fn-wire-render-lines lines) '(46 13 10)))
    (fn-wire-make-result
     (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)
     (list
      (fn-wire-article-event
       (append (fn-bch-held-lines body body-size) lines))))))
  :hints (("Goal"
           :induct (fn-wire-render-lines-induction body body-size lines)
           :in-theory (e/d (fn-wire-render-lines
                             fn-wire-clean-linesp)
                            (fn-wire-feed-proper
                             fn-wire-make-result
                             fn-wire-make-state
                             fn-wire-feed-proper-append
                             fn-wire-append-associative
                             fn-wire-append-when-true-listp
                             fn-wire-rendered-line-prefix-is-append
                             fn-bch-push-list)))
          ("Subgoal *1/2"
           :use ((:instance fn-wire-line-start-body-facts)
                 (:instance fn-wire-feed-proper-of-article-terminator (line-limit line-limit))
                 (:instance fn-bch-body-okp-terminator-lines (b body) (n body-size) (l 0))))
          ("Subgoal *1/1"
           :use ((:instance fn-wire-line-start-body-facts)
                 (:instance fn-wire-received-line-body (source (car lines)))
                 (:instance fn-wire-feed-proper-of-rendered-source-line
                            (source (car lines))
                            (tail (fn-wire-append (fn-wire-render-lines (cdr lines)) '(46 13 10))))
                 (:instance fn-wire-stuffed-line-fits-article-profile)
                 (:instance fn-wire-first-line-fits-total-body-bound)
                 (:instance fn-wire-rest-lines-fit-after-first)
                 (:instance fn-wire-rendered-block-cons-decomposition
                            (source (car lines))
                            (rendered-rest (fn-wire-render-lines (cdr lines))))))))

(defthm fn-wire-clean-linesp-implies-octet-linesp
  (implies (fn-wire-clean-linesp lines)
           (fn-wire-octet-linesp lines))
  :hints (("Goal"
           :induct (fn-wire-clean-linesp lines)
           :in-theory (enable fn-wire-clean-linesp))))

(defthm fn-wire-clean-linesp-implies-true-listp
  (implies (fn-wire-clean-linesp lines)
           (true-listp lines))
  :hints (("Goal"
           :use ((:instance fn-wire-clean-linesp-implies-octet-linesp)
                 (:instance fn-wire-octet-linesp-is-true-list))
           :in-theory (disable fn-wire-clean-linesp-implies-octet-linesp
                               fn-wire-octet-linesp-is-true-list))))

(defthm fn-wire-render-lines-is-an-octet-list
  (implies (fn-wire-clean-linesp lines)
           (fn-wire-octet-listp (fn-wire-render-lines lines)))
  :hints (("Goal"
           :induct (fn-wire-render-lines lines)
           :in-theory (enable fn-wire-render-lines
                              fn-wire-clean-linesp
                              fn-wire-append))))

(defthm fn-wire-successful-render-block-octets
  (implies
   (fn-wire-outbound-okp (fn-wire-render-block article limit))
   (equal
    (fn-wire-outbound-octets (fn-wire-render-block article limit))
    (fn-wire-append
     (fn-wire-render-lines
      (fn-wire-outbound-octets (fn-wire-outbound-lines article limit)))
     '(46 13 10))))
  :hints (("Goal"
           :in-theory (enable fn-wire-render-block
                              fn-wire-outbound-okp
                              fn-wire-outbound-ok
                              fn-wire-outbound-octets))))

(defthm fn-wire-successful-render-block-is-an-octet-list
  (implies (fn-wire-outbound-okp (fn-wire-render-block article limit))
           (fn-wire-octet-listp
            (fn-wire-outbound-octets
             (fn-wire-render-block article limit))))
  :hints (("Goal"
           :use ((:instance fn-wire-outbound-lines-success-is-clean
                            (octets article))
                 (:instance fn-wire-render-lines-is-an-octet-list
                            (lines (fn-wire-outbound-octets
                                    (fn-wire-outbound-lines article limit))))
                 (:instance fn-wire-octet-listp-of-total-append
                            (left (fn-wire-render-lines
                                   (fn-wire-outbound-octets
                                    (fn-wire-outbound-lines article limit))))
                            (right '(46 13 10))))
           :in-theory (e/d (fn-wire-render-block
                             fn-wire-outbound-okp
                             fn-wire-outbound-octets
                             fn-wire-outbound-ok
                             fn-wire-append)
                            (fn-wire-outbound-lines-success-is-clean
                             fn-wire-render-lines-is-an-octet-list
                             fn-wire-octet-listp-of-total-append)))))

(defun fn-wire-outbound-receiver-start (body-limit)
  (declare (xargs :guard t))
  (fn-wire-make-state :article nil 0 (fn-bch-empty) nil 0
                      (+ 1 (nfix body-limit))
                      (nfix body-limit)))

(defthm fn-wire-outbound-receiver-start-is-statep
  (implies (posp body-limit)
           (fn-wire-statep
            (fn-wire-outbound-receiver-start body-limit)))
  :hints (("Goal"
           :in-theory (enable fn-wire-outbound-receiver-start
                              fn-wire-statep))))

; This is the exact article profile selected by fn-served-dispatch before it
; consumes the first article byte.  The host path calls fn-served-step, whose
; dispatch uses this begin transition; the helper above only names its result.
(defthm fn-wire-served-article-profile-is-outbound-receiver-start
  (implies (and (posp command-limit) (posp body-limit))
           (equal
            (fn-wire-result-state
             (fn-wire-begin-article-with-line-limit
              (fn-wire-initial-state command-limit body-limit)
              (fn-wire-article-line-limit
               (fn-wire-initial-state command-limit body-limit))))
            (fn-wire-outbound-receiver-start body-limit)))
  :hints (("Goal"
           :in-theory (enable fn-wire-initial-state
                              fn-wire-article-line-limit
                              fn-wire-begin-article-with-line-limit
                              fn-wire-begin-article-admissiblep
                              fn-wire-outbound-receiver-start
                              fn-wire-statep
                              fn-wire-state-shapep
                              fn-wire-result-state
                              fn-wire-make-result))))

(defthm fn-wire-successful-render-block-lines-fit-body-limit
  (implies
   (and (fn-wire-outbound-okp (fn-wire-render-block article limit))
        (<= (nfix limit) (nfix body-limit)))
   (<= (fn-wire-lines-size
        (fn-wire-outbound-octets
         (fn-wire-outbound-lines article limit)))
       (nfix body-limit)))
  :hints (("Goal"
           :use ((:instance fn-wire-outbound-lines-success-reconstructs-source
                            (octets article))
                 (:instance fn-wire-source-lines-equal-implies-lines-size
                            (lines (fn-wire-outbound-octets
                                    (fn-wire-outbound-lines article limit))))
                 (:instance fn-wire-outbound-lines-success-respects-limit
                            (octets article)))
           :in-theory (e/d (fn-wire-render-block)
                           (fn-wire-outbound-lines-success-reconstructs-source
                            fn-wire-source-lines-equal-implies-lines-size
                            fn-wire-outbound-lines-success-respects-limit)))))

; The universal renderer/receiver composition.  The subject on the left is
; fn-wire-drive, the adapter-loop semantics, over the octets produced by the
; real outbound renderer.  Success, the configured source/body relation and a
; positive body profile are exactly what prevent malformed input, line close
; and cumulative body close.  The sole event contains every parsed source line
; in order, including empty and trailing-empty lines and literal leading dots.
(defthm fn-wire-drive-of-successful-render-block-preserves-source
  (implies
   (and (posp body-limit)
        (fn-wire-outbound-okp (fn-wire-render-block article limit))
        (<= (nfix limit) (nfix body-limit)))
   (let ((lines (fn-wire-outbound-octets
                 (fn-wire-outbound-lines article limit))))
     (and
      (equal
       (fn-wire-drive
        (fn-wire-outbound-receiver-start body-limit)
        (fn-wire-outbound-octets
         (fn-wire-render-block article limit)))
       (fn-wire-make-result
        (fn-wire-make-state :command nil 0 nil nil 0
                            (+ 1 (nfix body-limit))
                            (nfix body-limit))
        (list (fn-wire-article-event lines))))
      (equal (fn-wire-source-lines lines) article))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-wire-feed-proper-of-rendered-block-lines
                            (body (fn-bch-empty)) (body-size 0)
                            (line-limit (+ 1 (nfix body-limit)))
                            (body-limit (nfix body-limit))
                            (lines (fn-wire-outbound-octets
                                    (fn-wire-outbound-lines article limit))))
                 (:instance fn-wire-drive-is-feed-proper
                            (wire-state
                             (fn-wire-outbound-receiver-start body-limit))
                            (octets
                             (fn-wire-outbound-octets
                              (fn-wire-render-block article limit))))
                 (:instance fn-wire-outbound-lines-success-reconstructs-source
                            (octets article))
                 (:instance fn-wire-outbound-lines-success-is-clean
                            (octets article))
                 (:instance fn-wire-successful-render-block-lines-fit-body-limit)
                 (:instance fn-wire-successful-render-block-is-an-octet-list)
                 (:instance fn-wire-successful-render-block-octets)
                 (:instance fn-wire-outbound-receiver-start-is-statep)
                 (:instance fn-wire-clean-linesp-implies-true-listp
                            (lines (fn-wire-outbound-octets
                                    (fn-wire-outbound-lines article limit))))
                 (:instance fn-bch-body-okp-of-empty))
           :in-theory
           (e/d (fn-wire-render-block
                  fn-wire-outbound-receiver-start)
                (fn-wire-drive
                 fn-wire-feed-proper
                 fn-wire-statep
                 fn-wire-render-lines
                 fn-wire-feed-proper-of-rendered-block-lines
                 fn-wire-drive-is-feed-proper
                 fn-wire-outbound-lines-success-reconstructs-source
                 fn-wire-outbound-lines-success-is-clean
                 fn-wire-successful-render-block-lines-fit-body-limit
                 fn-wire-successful-render-block-is-an-octet-list
                 fn-wire-successful-render-block-octets
                 fn-wire-outbound-receiver-start-is-statep
                 fn-wire-clean-linesp-implies-true-listp))
           :do-not '(generalize fertilize))))

; By-definition bridge for the article arm of the exact renderer called at
; host/owner-host.lisp:483.  Empty input is the host's no-command sentinel;
; CHECK, IHAVE and TAKETHIS select the other protocol arms.
(defthm fn-wire-render-feed-command-article-arm-unfolds
  (implies
   (and (consp article)
        (not (fn-wire-prefixp *fn-wire-check-prefix* article))
        (not (fn-wire-prefixp *fn-wire-ihave-prefix* article))
        (not (fn-wire-prefixp *fn-wire-takethis-prefix* article)))
   (equal (fn-wire-render-feed-command article command-limit article-limit)
          (fn-wire-render-block article article-limit)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable fn-wire-render-feed-command))))

; A nonempty source accepted within the receiver's cumulative ceiling forces
; that ceiling to be positive.  This discharges the profile premise below
; instead of exposing a redundant hypothesis on the host-level theorem.
(defthm fn-wire-render-block-success-implies-lines-success
  (implies
   (fn-wire-outbound-okp (fn-wire-render-block article article-limit))
   (fn-wire-outbound-okp (fn-wire-outbound-lines article article-limit)))
  :hints (("Goal"
           :in-theory (enable fn-wire-render-block
                              fn-wire-outbound-okp))))

(defthm fn-wire-consp-has-positive-len
  (implies (consp value)
           (< 0 (len value)))
  :hints (("Goal" :expand ((len value)))))

(defthm fn-wire-nonempty-successful-render-block-needs-positive-body-limit
  (implies
   (and (consp article)
        (fn-wire-outbound-okp (fn-wire-render-block article article-limit))
        (<= (nfix article-limit) (nfix body-limit)))
   (posp body-limit))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  fn-wire-successful-render-block-lines-fit-body-limit
                  (limit article-limit))
                 (:instance
                  fn-wire-outbound-lines-success-reconstructs-source
                  (octets article) (limit article-limit))
                 (:instance
                  fn-wire-render-block-success-implies-lines-success)
                 (:instance fn-wire-consp-has-positive-len
                            (value article))
                 (:instance fn-wire-source-lines-equal-implies-lines-size
                            (lines (fn-wire-outbound-octets
                                    (fn-wire-outbound-lines
                                     article article-limit)))))
           :in-theory
           (e/d (len)
                (fn-wire-successful-render-block-lines-fit-body-limit
                 fn-wire-outbound-lines-success-reconstructs-source
                 fn-wire-render-block-success-implies-lines-success
                 fn-wire-consp-has-positive-len
                 fn-wire-source-lines-equal-implies-lines-size)))))

; Host-called renderer / served receiver composition.  These are exactly the
; conditions selecting fn-wire-render-feed-command's article arm.  The host
; calls that function at host/owner-host.lisp:483.  COMMAND-LIMIT initializes
; the served connection, while BODY-LIMIT+1 is the physical-line ceiling
; selected by fn-served-dispatch and BODY-LIMIT is the cumulative decoded-body
; ceiling.  ARTICLE-LIMIT may be tighter, but may not exceed BODY-LIMIT.
(defthm fn-wire-drive-of-host-rendered-article-preserves-source
  (implies
   (and (posp command-limit)
        (consp article)
        (not (fn-wire-prefixp *fn-wire-check-prefix* article))
        (not (fn-wire-prefixp *fn-wire-ihave-prefix* article))
        (not (fn-wire-prefixp *fn-wire-takethis-prefix* article))
        (fn-wire-outbound-okp
         (fn-wire-render-feed-command article command-limit article-limit))
        (<= (nfix article-limit) (nfix body-limit)))
   (let ((lines (fn-wire-outbound-octets
                 (fn-wire-outbound-lines article article-limit))))
     (and
      (equal
       (fn-wire-drive
        (fn-wire-result-state
         (fn-wire-begin-article-with-line-limit
          (fn-wire-initial-state command-limit body-limit)
          (fn-wire-article-line-limit
           (fn-wire-initial-state command-limit body-limit))))
        (fn-wire-outbound-octets
         (fn-wire-render-feed-command
          article command-limit article-limit)))
       (fn-wire-make-result
        (fn-wire-make-state :command nil 0 nil nil 0
                            (+ 1 (nfix body-limit))
                            (nfix body-limit))
        (list (fn-wire-article-event lines))))
      (equal (fn-wire-source-lines lines) article))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  fn-wire-drive-of-successful-render-block-preserves-source
                  (limit article-limit))
                 (:instance
                  fn-wire-served-article-profile-is-outbound-receiver-start)
                 (:instance
                  fn-wire-render-feed-command-article-arm-unfolds)
                 (:instance
                  fn-wire-nonempty-successful-render-block-needs-positive-body-limit))
           ; The three prefix tests are carried to the arm lemma's instance
           ; unchanged; opened against the constant prefixes they split
           ; the goal 105 ways per test and cost 43 s.
           :in-theory
           (disable fn-wire-served-article-profile-is-outbound-receiver-start
                    fn-wire-prefixp)
           :do-not '(generalize fertilize))))
