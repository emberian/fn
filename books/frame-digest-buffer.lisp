; fn: concrete-buffer and range realizers of the current frame digest.
;
; fn-frame-digest is the closed concrete BLAKE3 function. The two buffer
; seams retain their logical source-octet constraints and attach together
; to guard-verified buffer implementations. Their obligations are proved
; against that concrete frame function; no frame=BLAKE3 axiom is introduced.
; The logical lists are abstraction values, not runtime extent copies.

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

; The two representation realizers satisfy the concrete frame contract.
(defthm fn-blake3-prefixed-buffer-realizes-frame
  (equal (fn-blake3-of-prefixed-buffer-any prefix fn-octets)
         (fn-frame-digest (append prefix fn-octets)))
  :hints (("Goal" :in-theory (enable fn-frame-digest))))

(defthm fn-blake3-prefixed-range-realizes-frame
  (equal (fn-blake3-of-prefixed-range-any prefix a wn fn-octets)
         (fn-frame-digest (append prefix (fn-shr-win a wn fn-octets))))
  :hints (("Goal" :in-theory (enable fn-frame-digest))))

(defattach (fn-frame-digest-buffer fn-blake3-of-prefixed-buffer-any)
           (fn-frame-digest-range fn-blake3-of-prefixed-range-any))
