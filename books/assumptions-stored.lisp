; fn: A-ARENA-STORED, the served read of a payload AS IT IS STORED (lane
; compress-5, NNT-055; docs/extensions/nntp-compress-dict.md "Negotiation").
;
; "What the host answers for handle H is the compressed block the arena's
; extent holds for H, with its dictionary and its decoded length, and that
; block decodes to H's payload."
;
; `(fn-arena-stored h fn-arena)' is nil, or (DICT C N): DICT the dictionary
; octets of H's COMPRESSED extent, C the durable octets of its block, N the
; payload's length.  The host (host/native/extent.lisp) reads H's extent
; entry in the concrete arena (books/payload-arena-extent.lisp EXT[H]); for
; a compressed extent it reads C through the extent realizer
; `fn-durable-realize-octets' (one pread, ACL2's trailer check,
; A-DURABLE-EXTENT) and decodes nothing; for any other handle it answers
; nil.  The constraint says an answer decodes to the payload: it is what
; A-DURABLE-EXTENT and A-DURABLE-LZ (books/assumptions-durable.lisp) give at
; the concrete arena, where the payload of a compressed extent IS
; `fn-durable-realize-lz' of it (fn-arena$xcorr's view).  It is a named
; assumption because the abstract arena (a list of payloads) does not carry
; the extent: no export of fn-arena can answer it.
;
; It is not included by books/assumptions.lisp: its signature needs the
; arena stobj (books/payload-arena.lisp), which is outside that book's
; closure and would enter 766 books' worlds.  An arena-free signature (an
; ordinary value in the stobj's place) cannot be called from executable
; code that holds the arena as a stobj, and a constraint over octets alone
; would drop the link to H's payload that the keystone needs.  It is
; registered instead: specs/failures.md's A-ARENA-STORED row names this
; file, and tools/check_scaffold.py refuses an assumption book that is
; neither included by assumptions.lisp nor named there.  The theorems that
; use it (books/nntp-zarticle.lisp) include it and name it.

(in-package "ACL2")
(include-book "payload-arena")

(encapsulate
  (((fn-arena-stored * fn-arena) => *))

  (local (defun fn-arena-stored (h fn-arena)
           (declare (xargs :stobjs fn-arena) (ignore h fn-arena))
           nil))

  (defthm fn-arena-stored-decodes-to-the-payload
    (let ((s (fn-arena-stored h fn-arena)))
      (implies s
               (equal (fn-lzr-lz-value (car s) (cadr s) (caddr s))
                      (nth h fn-arena))))))
