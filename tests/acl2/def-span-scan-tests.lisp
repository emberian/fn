; Fixture instances of books/def-span-scan.lisp, one per shape and variant,
; each a scan the wire layer uses: find a given octet, count lines, match a
; command verb ignoring case, compare two spans, copy a span out and within,
; dot-stuff a reply body, and frame a command line.
(in-package "ACL2")
(include-book "../../books/def-span-scan")
(local (include-book "arithmetic/top" :dir :system))

; :find --- the first octet equal to B.
(def-span-scan fn-dss-fx-find-byte (b)
  :shape :find
  :body (eql o b)
  :cost-max 1
  :guard (fn-cbor-octetp b))

; :fold --- the number of LF octets, saturating below 2^59.
(def-span-scan fn-dss-fx-count-lf ()
  :shape :fold
  :acc-type (unsigned-byte 59)
  :body (if (and (eql o 10) (< acc (- (expt 2 59) 1))) (+ 1 acc) acc)
  :cost-max 1)

; :equal :constant --- the span is the verb ARTICLE in any case.
(def-span-scan fn-dss-fx-verb-article ()
  :shape :equal
  :against :constant
  :constant (65 82 84 73 67 76 69)
  :norm (if (and (integerp o) (<= 97 o) (<= o 122)) (- o 32) o)
  :cost-max 1)

; :equal :span --- two spans of equal length are the same octets.
(def-span-scan fn-dss-fx-same-octets ()
  :shape :equal
  :against :span)

; :copy --- a span appended onto a distinct output instance.
(def-span-scan fn-dss-fx-copy-out ()
  :shape :copy)

; :copy :within --- a span appended onto its own instance.
(def-span-scan fn-dss-fx-copy-within ()
  :shape :copy
  :within t)

; :stream --- dot-stuffing.  S is 0 at the start of a line, 1 within one.  A
; line that opens with "." is sent with ".." (RFC 3977 3.1.1); FINAL closes the
; block: CRLF if the body did not end at a line start, then ".\r\n".
(defun fn-dss-fx-dot-step (s o)
  (declare (xargs :guard (and (unsigned-byte-p 1 s) (fn-cbor-octetp o))))
  (let ((s2 (if (eql o 10) 0 1)))
    (if (and (eql s 0) (eql o 46))
        (mv s2 2 (+ 46 (* 256 46)) 0)
      (mv s2 1 o 0))))

(defun fn-dss-fx-dot-final (s)
  (declare (xargs :guard (unsigned-byte-p 1 s)))
  (if (eql s 0)
      (mv 3 (+ 46 (* 256 13) (* 65536 10)))
    (mv 5 (+ 13 (* 256 10) (* 65536 46) (* 16777216 13) (* 4294967296 10)))))

(def-span-scan fn-dss-fx-dot-stuff ()
  :shape :stream
  :state-type (unsigned-byte 1)
  :step (fn-dss-fx-dot-step s o)
  :final (fn-dss-fx-dot-final s)
  :emit-max 2
  :final-max 5
  :cost-max 1
  :final-cost-max 1)

; :stream --- command-line framing into a workspace of at most LIMIT octets.
; S is 2N + CR: N octets emitted, CR set when a CR is held back.  LF yields
; the line (a held CR is the terminator's and is dropped); a held CR followed
; by anything else is emitted; a line that would pass LIMIT is refused.
(defun fn-dss-fx-line-step (limit s o)
  (declare (xargs :guard (and (unsigned-byte-p 59 limit) (unsigned-byte-p 59 s)
                              (fn-cbor-octetp o))))
  (let* ((s (nfix s))
         (n (floor s 2))
         (cr (mod s 2)))
    (cond ((eql o 10) (mv 0 0 0 1))
          ((or (>= (+ n cr 1) (nfix limit)) (>= s (expt 2 57))) (mv s 0 0 2))
          ((eql o 13) (if (eql cr 1)
                          (mv (+ 1 (* 2 (+ n 1))) 1 13 0)
                        (mv (+ 1 (* 2 n)) 0 0 0)))
          (t (if (eql cr 1)
                 (mv (* 2 (+ n 2)) 2 (+ 13 (* 256 o)) 0)
               (mv (* 2 (+ n 1)) 1 o 0))))))

(def-span-scan fn-dss-fx-command-line (limit)
  :shape :stream
  :state-type (unsigned-byte 59)
  :step (fn-dss-fx-line-step limit s o)
  :final (mv 0 0)
  :emit-max 2
  :final-max 0
  :cost-max 1
  :guard (unsigned-byte-p 59 limit))

; :stream --- a length-prefixed field: two octets of big-endian length, then
; that many octets, no output.  S packs PHASE (2 bits: 0/3 expecting the high
; length octet, 1 the low one, 2 inside the field, 3 field complete), REM (16
; bits, octets still to come) and LEN (16 bits, the field's length).  The step
; yields at the field's last octet (or at the low length octet of an empty
; field); the host then has the field as the span [I' - LEN, I') of the input,
; LEN = (fn-dss-fx-field-len S'), by arithmetic: no octet of it is copied.
(defun fn-dss-fx-field-len (s)
  (declare (xargs :guard (natp s)))
  (logand (ash (nfix s) -18) 65535))

(defun fn-dss-fx-field-step (s o)
  (declare (xargs :guard (and (unsigned-byte-p 34 s) (fn-cbor-octetp o))))
  (let* ((s (nfix s))
         (o (logand (ifix o) 255))
         (phase (logand s 3))
         (rem (logand (ash s -2) 65535))
         (len (fn-dss-fx-field-len s)))
    (cond ((or (eql phase 0) (eql phase 3))
           (mv (+ 1 (* 262144 (* 256 o))) 0 0 0))
          ((eql phase 1)
           (let ((n (logand (+ len o) 65535)))
             (if (eql n 0)
                 (mv 3 0 0 1)
               (mv (+ 2 (* 4 n) (* 262144 n)) 0 0 0))))
          (t
           (let ((r (if (< 0 rem) (- rem 1) 0)))
             (if (eql r 0)
                 (mv (+ 3 (* 262144 len)) 0 0 1)
               (mv (+ 2 (* 4 r) (* 262144 len)) 0 0 0)))))))

(def-span-scan fn-dss-fx-field ()
  :shape :stream
  :state-type (unsigned-byte 34)
  :step (fn-dss-fx-field-step s o)
  :final (mv 0 0)
  :emit-max 0
  :final-max 0
  :cost-max 1)
