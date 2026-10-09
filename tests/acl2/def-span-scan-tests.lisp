; Fixture instances of books/def-span-scan.lisp, one per shape and variant,
; each a scan the wire layer uses: find a given octet, count lines, match a
; command verb ignoring case, compare two spans, copy a span out and within,
; dot-stuff a reply body, and frame a command line.
(in-package "ACL2")
(include-book "../../books/def-span-scan")
(local (include-book "arithmetic-5/top" :dir :system))

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
(defun-inline fn-dss-fx-dot-step (s o)
  (declare (xargs :guard (and (unsigned-byte-p 1 s) (fn-cbor-octetp o))))
  (let ((s2 (if (eql o 10) 0 1)))
    (if (and (eql s 0) (eql o 46))
        (mv s2 2 (+ 46 (* 256 46)) 0)
      (mv s2 1 o 0))))

(defun-inline fn-dss-fx-dot-final (s)
  (declare (xargs :guard (unsigned-byte-p 1 s)))
  (if (eql s 0)
      (mv 0 3 (+ 46 (* 256 13) (* 65536 10)) 0)
    (mv 0 5 (+ 13 (* 256 10) (* 65536 46) (* 16777216 13) (* 4294967296 10)) 0)))

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
; by anything else is emitted; a line that would pass LIMIT is refused, the
; octet unconsumed.  At the end of input an unterminated line is refused.
(defun-inline fn-dss-fx-line-step (limit s o)
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
  :final (mv s 0 0 (if (eql s 0) 0 2))
  :emit-max 2
  :final-max 0
  :cost-max 1
  :guard (unsigned-byte-p 59 limit))

; :stream --- a length-prefixed field: two octets of big-endian length, then
; that many octets, no output.  S packs PHASE (2 bits: 0/3 expecting the high
; length octet, 1 the low one, 2 inside the field, 3 field complete), REM (16
; bits, octets still to come) and LEN (16 bits, the field's length).  The step
; yields at the field's last octet (or at the low length octet of an empty
; field), LEN = (fn-dss-fx-field-len S').  When the field lies within the
; current input buffer (I' >= LEN) it is the span [I' - LEN, I') of that
; buffer, found by arithmetic, no octet copied.  A field that crosses
; arrivals is not in any one buffer: the host must retain the earlier input
; (or copy the field) itself; the partition theorem says nothing about it.
(defun fn-dss-fx-field-len (s)
  (declare (xargs :guard (natp s)))
  (min (floor (nfix s) 262144) 65535))

; The next state, or a refusal if it would leave the 34-bit state type; no
; state the step itself produces reaches that branch (each packed field stays
; within its bits), so it states the type rather than assuming it.
(defun fn-dss-fx-field-put (s next sig)
  (declare (xargs :guard (and (natp s) (natp next))))
  (if (< (nfix next) 17179869184)
      (mv (nfix next) 0 0 sig)
    (mv (nfix s) 0 0 2)))

(defun-inline fn-dss-fx-field-step (s o)
  (declare (xargs :guard (and (unsigned-byte-p 34 s) (fn-cbor-octetp o))))
  (let* ((s (nfix s))
         (o (mod (nfix o) 256))
         (phase (mod s 4))
         (rem (floor (mod s 262144) 4))
         (len (fn-dss-fx-field-len s)))
    (cond ((or (eql phase 0) (eql phase 3))
           (fn-dss-fx-field-put s (+ 1 (* 262144 (* 256 o))) 0))
          ((eql phase 1)
           (let* ((x (+ len o))
                  (n (if (< x 65536) x (- x 65536))))
             (if (eql n 0)
                 (fn-dss-fx-field-put s 3 1)
               (fn-dss-fx-field-put s (+ 2 (* 4 n) (* 262144 n)) 0))))
          (t
           (let ((r (if (< 0 rem) (- rem 1) 0)))
             (if (eql r 0)
                 (fn-dss-fx-field-put s (+ 3 (* 262144 len)) 1)
               (fn-dss-fx-field-put s (+ 2 (* 4 r) (* 262144 len)) 0)))))))

(defun-inline fn-dss-fx-field-final (s)
  (declare (xargs :guard (unsigned-byte-p 34 s)))
  (let ((phase (mod (nfix s) 4)))
    (mv s 0 0 (if (or (eql phase 1) (eql phase 2)) 2 0))))

(def-span-scan fn-dss-fx-field ()
  :shape :stream
  :state-type (unsigned-byte 34)
  :step (fn-dss-fx-field-step s o)
  :final (fn-dss-fx-field-final s)
  :emit-max 0
  :final-max 0
  :cost-max 1)

; Hygiene (review F3 of 07d0c6686): a context formal named S2, the name a
; generated local once had.  Its drive must keep the caller's S2 on every
; resume: with S2 = 1 every step emits 65.
(def-span-scan fn-dss-fx-context-s2 (s2)
  :shape :stream
  :state-type (unsigned-byte 1)
  :step (mv 0 1 (if (eql s2 1) 65 66) 1)
  :final (mv s 0 0 0)
  :emit-max 1
  :final-max 0
  :cost-max 1)

; -----------------------------------------------------------------------------
; L2.0 (landing 2): the output is extended once and written with `put', and
; every exit of a :stream call truncates to the length written.  Ground
; witnesses that the write-charge bounds are satisfied and attained, and that
; the exits leave the output at the written length, not the zeroed window.

(defun fxw-copy (fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
  (let* ((fn-octets (fn-octets-from-list '(1 2 3 4 5) fn-octets))
         (fn-dss-out (fn-dss-out-from-list '(9) fn-dss-out))
         (ch (fn-dss-fx-copy-out-write-charge 1 4 10 fn-octets fn-dss-out))
         (ch2 (fn-dss-fx-copy-out-write-charge 1 4 3 fn-octets fn-dss-out)))
    (mv-let (sig fn-dss-out) (fn-dss-fx-copy-out 1 4 10 fn-octets fn-dss-out)
      (let ((out (fn-dss-out-list fn-dss-out)))
        (mv-let (sig2 fn-dss-out) (fn-dss-fx-copy-out 1 4 3 fn-octets fn-dss-out)
          (mv (list sig out ch sig2 (fn-dss-out-list fn-dss-out) ch2) fn-octets fn-dss-out))))))

(defun fxw-copy-value ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets)
      (with-local-stobj fn-dss-out
        (mv-let (v fn-octets fn-dss-out) (fxw-copy fn-octets fn-dss-out)
          (mv v fn-octets)))
      v)))

; Extended by 3 and 3 stores: 6 = 2 (END - I), the bound attained; a refused
; copy stores nothing and leaves the output as it was.
(assert-event
 (equal (fxw-copy-value)
        '(:done (9 2 3 4) 6 :refused (9 2 3 4) 0)))

(defun fxw-dot (cap fn-octets fn-dss-out)
  (declare (xargs :stobjs (fn-octets fn-dss-out) :verify-guards nil))
  (let* ((fn-octets (fn-octets-from-list '(46 65 13 10) fn-octets))
         (fn-dss-out (fn-dss-out-clear fn-dss-out))
         (ch (fn-dss-fx-dot-stuff-write-charge 0 0 4 t cap fn-octets fn-dss-out)))
    (mv-let (sig s i fn-dss-out) (fn-dss-fx-dot-stuff 0 0 4 t cap fn-octets fn-dss-out)
      (declare (ignore s))
      (mv (list sig i (fn-dss-out-len fn-dss-out) (fn-dss-out-list fn-dss-out) ch)
          fn-octets fn-dss-out))))

(defun fxw-dot-value (cap)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets)
      (with-local-stobj fn-dss-out
        (mv-let (v fn-octets fn-dss-out) (fxw-dot cap fn-octets fn-dss-out)
          (mv v fn-octets)))
      v)))

; Room for the whole block: 20 cells zeroed, 8 octets written and kept; the
; charge 28 is within the bound 20 + 2 * 4 + 5.
(assert-event
 (equal (fxw-dot-value 20)
        '(:done 4 8 (46 46 65 13 10 46 13 10) 28)))
; Room for the body only: the final needs 5 more, the call answers
; :need-output at the end of the input with the five octets written (6 cells
; zeroed, 5 written: 11).
(assert-event
 (equal (fxw-dot-value 6)
        '(:need-output 4 5 (46 46 65 13 10) 11)))
; Below the floor: nothing is zeroed, written or truncated.
(assert-event
 (equal (fxw-dot-value 3)
        '(:no-room 0 0 nil 0)))
