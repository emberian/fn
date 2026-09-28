; fn: the frame digest over an octet buffer (lane arena-offheap-3,
; 2026-09-27; PRF-295, recover-memory-2's P3; record
; planning/evidence/arena-offheap-3-2026-09-27.md).
;
; P3's obstruction.  Every frame's integrity trailer is `fn-frame-digest'
; (books/frame-octets.lisp), a CONSTRAINED function (A-CRYPTO: 32 octets,
; nothing else) to which books/crypto-attach.lisp attaches BLAKE3
; (`fn-blake3-stobj'; SHA-256 until 2026-09-28).  books/blake3-stobj.lisp
; proves a buffer reader equal to `fn-blake3', but nothing in the logic equates `fn-frame-digest' with
; its realiser (that is the point of the seam), so a frame check that reads
; the octet buffer by index could not be proved equal to the list check.
;
; The approach (arena-offheap's LANEDUMP, P3): a second constrained function
; `fn-frame-digest-buffer PREFIX BUF', constrained to BE the frame digest of
; PREFIX followed by the buffer's octets, and ONE defattach that attaches
; both together: fn-frame-digest to fn-blake3-stobj (as crypto-attach does)
; and fn-frame-digest-buffer to the buffer BLAKE3.  The attachment's obligation
; is exactly blake3-stobj's keystone (the buffer digest is the list digest
; of the concatenation); nothing new is assumed about BLAKE3, and the seam
; still says nothing beyond 32 octets.  A frame check over a buffer is then
; equal to the list frame check by `fn-frame-digest-buffer-is-the-frame-digest'.
;
; The first consumer is the served read of an extent handle
; (books/payload-extent-read.lisp): the entry's protected prefix is checked
; in the buffer the host preads into, with no octet list.

(in-package "ACL2")
(include-book "crypto-attach")
(include-book "blake3-stobj")
(include-book "octet-window")

(encapsulate
  (((fn-frame-digest-buffer * fn-octets) => *))

  (local (defun fn-frame-digest-buffer (prefix fn-octets)
           (declare (xargs :stobjs fn-octets :verify-guards nil))
           (fn-frame-digest (append prefix (fn-octets-list fn-octets)))))

  ; KEYSTONE (PRF-295): the buffer digest is the frame digest of the prefix
  ; followed by the buffer's octets (its logical value).
  (defthm fn-frame-digest-buffer-is-the-frame-digest
    (equal (fn-frame-digest-buffer prefix fn-octets)
           (fn-frame-digest (append prefix fn-octets)))))

; The buffer BLAKE3 with the constrained function's guard (t): a prefix that
; is not a true list is read up to its last cons, as `append' reads it.
(defun fn-blake3-of-prefixed-buffer-any (prefix fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-blake3-of-prefixed-buffer (true-list-fix prefix) fn-octets))

(local
 (defthm fn-fdb-append-true-list-fix
   (equal (append (true-list-fix x) y) (append x y))))

(defthm fn-blake3-of-prefixed-buffer-any-is-blake3
  (equal (fn-blake3-of-prefixed-buffer-any prefix fn-octets)
         (fn-blake3-stobj (append prefix fn-octets)))
  :hints (("Goal" :in-theory (enable fn-blake3-stobj-is-blake3))))

; The frame digest of a prefix followed by a WINDOW of the buffer (lane
; snapshot-open-2): a file read into one buffer holds many frames, and each
; frame's trailer is the digest of a window of it (the checkpoint's segments,
; the log's entries).  Constrained as the buffer digest is: the frame digest
; of PREFIX followed by the WN octets after A (books/octet-window.lisp
; `fn-shr-win').
(encapsulate
  (((fn-frame-digest-range * * * fn-octets) => *))

  (local (defun fn-frame-digest-range (prefix a wn fn-octets)
           (declare (xargs :stobjs fn-octets :verify-guards nil))
           (fn-frame-digest (append prefix (fn-shr-win a wn (fn-octets-list fn-octets))))))

  ; KEYSTONE: the window digest is the frame digest of the prefix followed
  ; by the window's octets.
  (defthm fn-frame-digest-range-is-the-frame-digest
    (equal (fn-frame-digest-range prefix a wn fn-octets)
           (fn-frame-digest (append prefix (fn-shr-win a wn fn-octets))))))

; The window BLAKE3 with the constrained function's guard (t): out of the
; reader's bounds (never on a host path) it digests the list model.
(defun fn-blake3-of-prefixed-range-any (prefix a wn fn-octets)
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-shr-win)))))
  (if (and (natp a) (natp wn) (<= (+ a wn) (fn-octets-len fn-octets)))
      (fn-blake3-of-prefixed-range (true-list-fix prefix) a wn fn-octets)
    (fn-blake3-stobj (append (true-list-fix prefix)
                             (take (nfix wn) (nthcdr (nfix a) (fn-octets-list fn-octets)))))))

(defthm fn-blake3-of-prefixed-range-any-is-blake3
  (equal (fn-blake3-of-prefixed-range-any prefix a wn fn-octets)
         (fn-blake3-stobj (append prefix (fn-shr-win a wn fn-octets))))
  :hints (("Goal" :in-theory (enable fn-blake3-stobj-is-blake3 fn-shr-win
                                     fn-blake3-of-prefixed-range-is-blake3))))

; The three attachments, together: fn-frame-digest's as crypto-attach made
; it, the buffer digest's and the window digest's.  The obligations are
; fn-frame-digest's constraints for fn-blake3-stobj (crypto-attach's three
; lemmas) and the keystones above for the pairs
; (fn-blake3-of-prefixed-buffer-any-is-blake3,
; fn-blake3-of-prefixed-range-any-is-blake3).
(defattach (fn-frame-digest fn-blake3-stobj)
           (fn-frame-digest-buffer fn-blake3-of-prefixed-buffer-any)
           (fn-frame-digest-range fn-blake3-of-prefixed-range-any))
