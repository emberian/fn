; fn: the frame digest over an octet buffer (lane arena-offheap-3,
; 2026-09-27; PRF-295, recover-memory-2's P3; record
; planning/evidence/arena-offheap-3-2026-09-27.md).
;
; P3's obstruction.  Every frame's integrity trailer is `fn-frame-digest'
; (books/frame-octets.lisp), a CONSTRAINED function (A-CRYPTO: 32 octets,
; nothing else) to which books/crypto-attach.lisp attaches SHA-256
; (`fn-sha256-stobj').  books/sha256-buffer.lisp proves a buffer reader equal
; to `fn-sha256', but nothing in the logic equates `fn-frame-digest' with
; `fn-sha256' (that is the point of the seam), so a frame check that reads
; the octet buffer by index could not be proved equal to the list check.
;
; The approach (arena-offheap's LANEDUMP, P3): a second constrained function
; `fn-frame-digest-buffer PREFIX BUF', constrained to BE the frame digest of
; PREFIX followed by the buffer's octets, and ONE defattach that attaches
; both together: fn-frame-digest to fn-sha256-stobj (as before) and
; fn-frame-digest-buffer to the buffer SHA-256.  The attachment's obligation
; is exactly sha256-buffer's keystone (the buffer digest is the list digest
; of the concatenation); nothing new is assumed about SHA-256, and the seam
; still says nothing beyond 32 octets.  A frame check over a buffer is then
; equal to the list frame check by `fn-frame-digest-buffer-is-the-frame-digest'.
;
; The first consumer is the served read of an extent handle
; (books/payload-extent-read.lisp): the entry's protected prefix is checked
; in the buffer the host preads into, with no octet list.

(in-package "ACL2")
(include-book "crypto-attach")
(include-book "sha256-buffer")
(include-book "sha256-range")

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

; The buffer SHA-256 with the constrained function's guard (t): a prefix that
; is not a true list is read up to its last cons, as `append' reads it.
(defun fn-sha256-of-prefixed-buffer-any (prefix fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-sha256-of-prefixed-buffer (true-list-fix prefix) fn-octets))

(local
 (defthm fn-fdb-append-true-list-fix
   (equal (append (true-list-fix x) y) (append x y))))

(defthm fn-sha256-of-prefixed-buffer-any-is-sha256
  (equal (fn-sha256-of-prefixed-buffer-any prefix fn-octets)
         (fn-sha256-stobj (append prefix fn-octets)))
  :hints (("Goal" :in-theory (enable fn-sha256-stobj-is-sha256))))

; The frame digest of a prefix followed by a WINDOW of the buffer (lane
; snapshot-open-2): a file read into one buffer holds many frames, and each
; frame's trailer is the digest of a window of it (the checkpoint's segments,
; the log's entries).  Constrained as the buffer digest is: the frame digest
; of PREFIX followed by the WN octets after A (books/sha256-range.lisp
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

; The window SHA-256 with the constrained function's guard (t): out of the
; reader's bounds (never on a host path) it digests the list model.
(defun fn-sha256-of-prefixed-range-any (prefix a wn fn-octets)
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-shr-win)))))
  (if (and (natp a) (natp wn) (<= (+ a wn) (fn-octets-len fn-octets)))
      (fn-sha256-of-prefixed-range (true-list-fix prefix) a wn fn-octets)
    (fn-sha256-stobj (append (true-list-fix prefix)
                             (take (nfix wn) (nthcdr (nfix a) (fn-octets-list fn-octets)))))))

(defthm fn-sha256-of-prefixed-range-any-is-sha256
  (equal (fn-sha256-of-prefixed-range-any prefix a wn fn-octets)
         (fn-sha256-stobj (append prefix (fn-shr-win a wn fn-octets))))
  :hints (("Goal" :in-theory (enable fn-sha256-stobj-is-sha256 fn-shr-win))))

; The three attachments, together: fn-frame-digest's as crypto-attach made
; it, the buffer digest's and the window digest's.  The obligations are
; fn-frame-digest's constraints for fn-sha256-stobj (crypto-attach's three
; lemmas) and the keystones above for the pairs
; (fn-sha256-of-prefixed-buffer-any-is-sha256,
; fn-sha256-of-prefixed-range-any-is-sha256).
(defattach (fn-frame-digest fn-sha256-stobj)
           (fn-frame-digest-buffer fn-sha256-of-prefixed-buffer-any)
           (fn-frame-digest-range fn-sha256-of-prefixed-range-any))
