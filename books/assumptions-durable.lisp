; fn: the named assumptions about durable extents, A-DURABLE-EXTENT and
; A-DURABLE-LZ, a part of books/assumptions.lisp.
;
; books/assumptions.lisp includes this book, so every named assumption is still
; reached through it and listed there.  This part is its own book because the
; payload arena needs these two and nothing else of the trust boundary: when
; they sat in books/assumptions.lisp, every book above the arena (632 of that
; book's 751 dependents, the whole NNTP and owner towers) depended on the byte
; store's crash model and recertified with every new assumption (lane
; fan-in-cuts, 2026-09-28; tools/rule_usage.py).
(in-package "ACL2")
(include-book "cbor")
(include-book "payload-lz-value")

; A-DURABLE-EXTENT (lane arena-offheap-2, 2026-09-27; PRF-294; the payload
; arena's stage 2, planning/evidence/arena-offheap-2026-09-27.md section 3).
;
; "A durable file holds, at an extent the host durably wrote and never
; rewrites, the octets written there; and the host's realizer answers them."
;
; `(fn-durable-octets file off len)' is the octet list of length LEN that the
; durable file named FILE holds at [OFF, OFF+LEN).  FILE is a natural the host
; assigns to a file it holds open for the process's life (a log segment); a
; log segment is append-only per offset (an offset is written once, fenced,
; never rewritten; log recovery zeroes only past the last complete entry,
; which no extent names), and an unlinked segment stays readable through its
; open descriptor.
;
; `(fn-durable-realize-octet file eoff elen poff plen trailer i)' is the
; host's REALIZER: the payload extent [POFF, POFF+PLEN) lies inside the log
; entry whose protected prefix is [EOFF, EOFF+ELEN) and whose trailer (the
; entry's fn-frame-digest, read and checked by the open) is TRAILER.  The
; host's raw definition (host/native/extent.lisp) preads the entry into a
; bounded cache, checks the trailer through ACL2 (`fn-arx-entry-ok',
; books/payload-extent.lisp) and answers the payload's octet I; a mismatch
; is refused by name (arena-extent-digest: a recovery event), never
; answered.  The constraint says the realizer's answer is the durable octet.
; `(fn-durable-realize-octets file eoff elen poff plen trailer)' is the same
; realizer for the whole payload in one call (lane arena-offheap-3: one
; pread, one trailer check, one list, where the per-octet call took the
; realizer's lock once per octet); the constraint says it is the payload's
; durable octets.
;
; Theorems that take it: fn-arena-extent-payload (books/payload-arena.lisp:
; an extent handle's payload is fn-durable-octets of its extent), and every
; theorem of the arena's consumers through it; fn-arx-entry-ok-of-durable
; (books/payload-extent.lisp: a faithful read passes the trailer check).
(encapsulate
  (((fn-durable-octet * *) => *)
   ((fn-durable-octets * * *) => *)
   ((fn-durable-realize-octet * * * * * * *) => *)
   ((fn-durable-realize-octets * * * * * *) => *))

  (local (defun fn-durable-octet (file pos)
           (declare (ignore file pos))
           0))

  (local (defun fn-durable-octets (file off len)
           (if (zp len)
               nil
             (cons (fn-durable-octet file off)
                   (fn-durable-octets file (+ 1 (nfix off)) (1- len))))))

  (local (defun fn-durable-realize-octet (file eoff elen poff plen trailer i)
           (declare (ignore eoff elen trailer))
           (nth i (fn-durable-octets file poff plen))))

  (local (defun fn-durable-realize-octets (file eoff elen poff plen trailer)
           (declare (ignore eoff elen trailer))
           (fn-durable-octets file poff plen)))

  (defthm fn-durable-octet-is-octet
    (fn-cbor-octetp (fn-durable-octet file pos)))

  ; The extent's octets are the file's octets at its positions, one by one:
  ; two extents that overlap agree where they overlap.
  (defthm fn-durable-octets-unfold
    (equal (fn-durable-octets file off len)
           (if (zp len)
               nil
             (cons (fn-durable-octet file off)
                   (fn-durable-octets file (+ 1 (nfix off)) (1- len)))))
    :rule-classes ((:definition :controller-alist ((fn-durable-octets nil nil t)))))

  (defthm fn-durable-realize-octet-is-durable
    (equal (fn-durable-realize-octet file eoff elen poff plen trailer i)
           (nth i (fn-durable-octets file poff plen))))

  (defthm fn-durable-realize-octets-is-durable
    (equal (fn-durable-realize-octets file eoff elen poff plen trailer)
           (fn-durable-octets file poff plen))))

(local
 (defun fn-durable-ind (off len)
   (if (zp len) (list off) (fn-durable-ind (+ 1 (nfix off)) (1- len)))))

(defthm fn-durable-octets-are-octets
  (fn-cbor-octet-listp (fn-durable-octets file off len))
  :hints (("Goal" :induct (fn-durable-ind off len))))

(defthm fn-durable-octets-len
  (equal (len (fn-durable-octets file off len)) (nfix len))
  :hints (("Goal" :induct (fn-durable-ind off len))))

(in-theory (disable fn-durable-octets-unfold))

; -----------------------------------------------------------------------------
; A-DURABLE-LZ (lane compression-extents, 2026-09-27; PRF-326; brief C2 of
; planning/evidence/article-compression-2026-09-27.md section 6).
;
; "The host's realizer for a COMPRESSED extent answers the value its C
; decodes to."
;
; A compressed extent (books/payload-lz-record.lisp) is an LZ4 block C at
; [POFF, POFF+PLEN) inside a log entry (protected prefix [EOFF, EOFF+ELEN),
; trailer TRAILER), decoding against the dictionary DICT to N octets.
; `(fn-durable-realize-lz file eoff elen poff plen trailer n dict)' is the
; host's realizer (host/native/extent.lisp): it reads C through the extent
; realizer above (one pread of the entry, ACL2's trailer check,
; `fn-durable-realize-octets'), runs ACL2's decoder on it
; (`fn-lzr-lz-value''s decode, books/payload-lz-value.lisp) and answers the
; octets ACL2 produced; where the decode fails it REFUSES by name
; (:lz-decode, a recovery event) and answers nothing.  The constraint says
; what it answers is `fn-lzr-lz-value' of C's durable octets.  It is a
; named contract on host code (a cache keeps the last decoded payload so a
; reader that reads octet by octet decodes once), not on the decoder: the
; decoder is ACL2's, and what the octets are is A-DURABLE-EXTENT's.
;
; Theorems that take it: fn-arena-seal-lz-extent-payload and
; fn-arena-reseat-lz-extent-keeps-a-faithful-arena (books/payload-arena.lisp)
; through the arena's compressed exports, and every consumer theorem over
; the arena through them.
(encapsulate
  (((fn-durable-realize-lz * * * * * * * *) => *))

  (local (defun fn-durable-realize-lz (file eoff elen poff plen trailer n dict)
           (declare (ignore eoff elen trailer))
           (fn-lzr-lz-value dict (fn-durable-octets file poff plen) n)))

  (defthm fn-durable-realize-lz-is-the-lz-value
    (equal (fn-durable-realize-lz file eoff elen poff plen trailer n dict)
           (fn-lzr-lz-value dict (fn-durable-octets file poff plen) n))))
