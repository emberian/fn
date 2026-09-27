; fn: the payload arena's EXTENT seal, its logical side (lane
; arena-offheap-2, 2026-09-27; PRF-294; the design is
; planning/evidence/arena-offheap-2026-09-27.md section 3).
;
; Stage 2 of arena-offheap moves payloads off the heap: a handle may denote
; an EXTENT of a durable file (a log segment the host holds open) instead of
; octets the process holds.  The arena's logical value does not change: it
; is the list of sealed payloads, and an extent handle's payload is
; `fn-durable-octets' of its extent (books/assumptions.lisp, A-DURABLE-EXTENT).
;
; This book is the logical side the generic (books/payload-arena.lisp) and
; the extent implementation (books/payload-arena-extent.lisp) share:
;   fn-arn-extentp E              E = (FILE EOFF ELEN POFF PLEN TRAILER), six
;                                 naturals, the payload [POFF, POFF+PLEN)
;                                 inside the entry's protected prefix
;                                 [EOFF, EOFF+ELEN);
;   fn-arena$a-seal-extent ...    (append a (list (fn-durable-octets FILE POFF PLEN))).
; The payload of an extent handle is read through the host's whole-payload
; realizer `fn-durable-realize-octets' (A-DURABLE-EXTENT: it is
; fn-durable-octets of the extent; lane arena-offheap-3).

(in-package "ACL2")
(include-book "payload-arena-bytes")
(include-book "assumptions")

(defun fn-arn-extentp (e)
  (declare (xargs :guard t))
  (and (true-listp e)
       (equal (len e) 6)
       (natp (nth 0 e)) (natp (nth 1 e)) (natp (nth 2 e))
       (natp (nth 3 e)) (natp (nth 4 e)) (natp (nth 5 e))
       (<= (nth 1 e) (nth 3 e))
       (<= (+ (nth 3 e) (nth 4 e)) (+ (nth 1 e) (nth 2 e)))))

(defun fn-arn-extent-guardp (file eoff elen poff plen trailer)
  (declare (xargs :guard t))
  (and (natp file) (natp eoff) (natp elen) (natp poff) (natp plen) (natp trailer)
       (<= eoff poff) (<= (+ poff plen) (+ eoff elen))))

(defthm fn-arn-extentp-of-list
  (equal (fn-arn-extentp (list file eoff elen poff plen trailer))
         (fn-arn-extent-guardp file eoff elen poff plen trailer)))

(defun fn-arena$a-seal-extent (file eoff elen poff plen trailer fn-arena$a)
  (declare (xargs :guard (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (ignore eoff elen trailer))
  (fn-oct-snoc fn-arena$a (fn-durable-octets file poff plen)))
