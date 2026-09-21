; Universal outbound NNTP block evidence.  This book starts at the actual
; renderer scanner, not a Python spelling of it, and keeps the source-tail
; invariant separate from the receiver composition below.
(in-package "ACL2")
(include-book "wire-invariants")

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
