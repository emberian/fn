; Witnesses and teeth for books/served-reply-buffer.lisp (PRF-192;
; egress-span, PKT-491).
;
; The keystone `fn-served-reply-to-buffer-is-the-reply' has one hypothesis,
; OKP (every reply effect carries an octet list), under which the buffer's
; range [0, len) is the reply.  Here: a reachable non-degenerate witness (a
; reply split over two effects with a non-reply effect between them, over a
; buffer that held a LONGER stale value, so the clear is exercised); the
; must-fail for OKP (a reply effect carrying 300: the range is not the
; reply); a labelled MUTATION witness (appending without the clear leaves
; the stale octets in front); the refusal theorem's witness; and the
; served-size witness, the executable over a 3 MiB reply split as the
; ARTICLE reply is (status line, then the body).
(in-package "ACL2")
(include-book "../../books/served-reply-buffer")
(include-book "std/testing/must-fail" :dir :system)

; Run the host-called subject over a buffer that first holds STALE; answer
; (okp range len).
(defun srbt-run (stale effects)
  (declare (xargs :guard (fn-cbor-octet-listp stale)))
  (with-local-stobj fn-octets
    (mv-let (okp range len fn-octets)
      (let* ((fn-octets (fn-octets-from-list stale fn-octets)))
        (mv-let (okp fn-octets)
          (fn-served-reply-to-buffer effects fn-octets)
          (mv okp
              (fn-oct-slice-list 0 (fn-octets-len fn-octets) fn-octets)
              (fn-octets-len fn-octets)
              fn-octets)))
      (list okp range len))))

; The mutation: the same appends WITHOUT the clear.
(defun srbt-run-no-clear (stale effects)
  (declare (xargs :guard (and (fn-cbor-octet-listp stale)
                              (fn-srb-effects-octetsp effects))))
  (with-local-stobj fn-octets
    (mv-let (range fn-octets)
      (let* ((fn-octets (fn-octets-from-list stale fn-octets))
             (fn-octets (fn-srb-append-effects effects fn-octets)))
        (mv (fn-oct-slice-list 0 (fn-octets-len fn-octets) fn-octets) fn-octets))
      range)))

(defconst *srbt-stale* '(88 88 88 88 88 88 88 88 88 88 88 88))
(defconst *srbt-effects*
  (list (list :reply '(50 50 48 32 49 13 10))      ; "220 1\r\n"
        (list :close)
        (list :reply '(104 105 13 10 46 13 10))))   ; "hi\r\n.\r\n"
(defconst *srbt-reply* (fn-served-reply-octets *srbt-effects*))

; -----------------------------------------------------------------------------
; KEYSTONE fn-served-reply-to-buffer-is-the-reply: reachable witness.
(assert-event (equal (len *srbt-reply*) 14))
(assert-event (fn-srb-effects-octetsp *srbt-effects*))
(assert-event
 (let ((r (srbt-run *srbt-stale* *srbt-effects*)))
   (and (equal (first r) t)
        (equal (third r) (len *srbt-reply*))
        (equal (second r) *srbt-reply*))))

; MUST-FAIL for OKP: a reply effect carrying 300 (not an octet).  OKP is
; nil, the buffer keeps the stale value, and the range is not the reply.
(defconst *srbt-bad* (list (list :reply '(50 50)) (list :reply '(300))))
(assert-event (not (fn-srb-effects-octetsp *srbt-bad*)))
(assert-event (equal (first (srbt-run *srbt-stale* *srbt-bad*)) nil))
(must-fail
 (assert-event (equal (second (srbt-run *srbt-stale* *srbt-bad*))
                      (fn-served-reply-octets *srbt-bad*))))

; fn-served-reply-to-buffer-refusal-keeps-the-buffer: the stale value stays.
(assert-event (equal (second (srbt-run *srbt-stale* *srbt-bad*)) *srbt-stale*))

; MUTATION (labelled): appending without the clear keeps the stale octets.
(must-fail
 (assert-event (equal (srbt-run-no-clear *srbt-stale* *srbt-effects*)
                      *srbt-reply*)))

; -----------------------------------------------------------------------------
; SERVED SIZE: a 3 MiB body behind the status line, the reply the ARTICLE of
; the ledger's row 6 answers; the executable fills the buffer and its whole
; value is the reply.  The buffer is read back with `fn-octets-list' (the
; tail-recursive reader; the range [0, len) is that list by the keystone and
; `fn-oct-list-is-identity'): `fn-oct-slice-list' is a non-tail recursion
; that exhausts the test process's control stack at 3 MiB, and it is only
; this book's reader, never the host's (the host copies the array).
(defun srbt-run-list (stale effects)
  (declare (xargs :guard (fn-cbor-octet-listp stale)))
  (with-local-stobj fn-octets
    (mv-let (okp range len fn-octets)
      (let* ((fn-octets (fn-octets-from-list stale fn-octets)))
        (mv-let (okp fn-octets)
          (fn-served-reply-to-buffer effects fn-octets)
          (mv okp (fn-octets-list fn-octets) (fn-octets-len fn-octets) fn-octets)))
      (list okp range len))))

(defun srbt-body (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))))
  (if (zp n) acc (srbt-body (1- n) (cons (+ 97 (mod n 26)) acc))))

(defconst *srbt-big*
  (list (list :reply '(50 50 48 32 51 13 10))
        (list :reply (srbt-body (* 3 1024 1024) '(13 10 46 13 10)))))
(assert-event
 (let ((r (srbt-run-list *srbt-stale* *srbt-big*)))
   (and (equal (first r) t)
        (equal (third r) (+ 7 (* 3 1024 1024) 5))
        (equal (second r) (fn-served-reply-octets *srbt-big*)))))
