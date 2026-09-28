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

; The RESEAT (lane arena-offheap-3, PRF-309): handle H is re-pointed at the
; extent the log wrote its payload to, once the log's barrier made it
; durable.  The logical value at H becomes the extent's durable octets; when
; those are the payload H held (the faithful write, which ACL2 checks before
; the owner asks: books/payload-commit-extent.lisp), the arena is unchanged
; (fn-arena-reseat-extent-keeps-a-faithful-arena, books/payload-arena.lisp).
(defun fn-arena$a-reseat-extent (h file eoff elen poff plen trailer fn-arena$a)
  (declare (xargs :guard (and (natp h) (< h (fn-arena$a-count fn-arena$a))
                              (fn-arn-extent-guardp file eoff elen poff plen trailer)))
           (ignore eoff elen trailer))
  (if (and (natp h) (< h (len fn-arena$a)))
      (fn-oct-update h (fn-durable-octets file poff plen) fn-arena$a)
    fn-arena$a))

; The RELEASE: the staged copy of a reseated handle is freed.  Logically
; nothing changes (an extent handle's payload is its extent's).
(defun fn-arena$a-release (h fn-arena$a)
  (declare (xargs :guard (natp h))
           (ignore h))
  fn-arena$a)

; -----------------------------------------------------------------------------
; COMPRESSED extents (lane compression-extents, PRF-326).  E = (FILE EOFF ELEN
; POFF PLEN TRAILER N DICT): an LZ4 block C at [POFF, POFF+PLEN) inside the
; entry, decoding against the dictionary octets DICT to N octets
; (books/payload-lz-record.lisp).  The handle's payload is
; `fn-lzr-lz-value DICT C N' of C's durable octets, read through the host's
; realizer `fn-durable-realize-lz' (A-DURABLE-LZ).  DICT is the dictionary's
; octets themselves (one shared list per dictionary): the value needs no
; table.

(defun fn-arn-lz-guardp (file eoff elen poff plen trailer n dict)
  (declare (xargs :guard t))
  (and (fn-arn-extent-guardp file eoff elen poff plen trailer)
       (natp n)
       (fn-cbor-octet-listp dict)))

(defun fn-arn-lz-extentp (e)
  (declare (xargs :guard t))
  (and (true-listp e)
       (equal (len e) 8)
       (fn-arn-lz-guardp (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e)
                         (nth 6 e) (nth 7 e))))

(defthm fn-arn-lz-extentp-of-list
  (equal (fn-arn-lz-extentp (list file eoff elen poff plen trailer n dict))
         (fn-arn-lz-guardp file eoff elen poff plen trailer n dict)))

(defthm fn-arn-lz-extent-not-extent
  (implies (fn-arn-lz-extentp e) (not (fn-arn-extentp e))))

(defun fn-arena$a-seal-lz-extent (file eoff elen poff plen trailer n dict fn-arena$a)
  (declare (xargs :guard (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (ignore eoff elen trailer))
  (fn-oct-snoc fn-arena$a (fn-lzr-lz-value dict (fn-durable-octets file poff plen) n)))

(defun fn-arena$a-reseat-lz-extent (h file eoff elen poff plen trailer n dict fn-arena$a)
  (declare (xargs :guard (and (natp h) (< h (fn-arena$a-count fn-arena$a))
                              (fn-arn-lz-guardp file eoff elen poff plen trailer n dict)))
           (ignore eoff elen trailer))
  (if (and (natp h) (< h (len fn-arena$a)))
      (fn-oct-update h (fn-lzr-lz-value dict (fn-durable-octets file poff plen) n) fn-arena$a)
    fn-arena$a))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-arn-extentp)
                    (:definition fn-arn-lz-extentp)
                    (:definition fn-arn-lz-guardp)))
