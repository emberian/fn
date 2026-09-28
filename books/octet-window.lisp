;; fn: the window of an octet buffer's value, as a list (lane snapshot-open-2's
;; `fn-shr-win', moved here from the deleted SHA-256 range book by lane blake3-digest,
;; 2026-09-28, so that the digest seams' window form,
;; books/frame-digest-buffer.lisp `fn-frame-digest-range', does not depend on a
;; SHA-256 book).  WN octets of L after A; `take' pads past the end, so its
;; length is WN on every value.

(in-package "ACL2")
(include-book "octets-stobj")

; The window's list model: WN octets of the buffer's value after A (take pads
; past the end, so its length is WN on every value).
(defun fn-shr-win (a wn l)
  (declare (xargs :guard t :verify-guards nil))
  (take (nfix wn) (nthcdr (nfix a) l)))

(local
 (defthm fn-ow-len-of-take
   (equal (len (take n l)) (nfix n))))

(local
 (defthm fn-ow-nth-of-take
   (implies (and (natp k) (< k (nfix n)))
            (equal (nth k (take n l)) (nth k l)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-ow-nth-of-nthcdr
   (implies (and (natp k) (natp a))
            (equal (nth k (nthcdr a l)) (nth (+ a k) l)))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(defthm fn-shr-len-of-win
  (equal (len (fn-shr-win a wn l)) (nfix wn)))

(defthm fn-shr-nth-of-win
  (implies (and (natp k) (< k (nfix wn)))
           (equal (nth k (fn-shr-win a wn l))
                  (nth (+ (nfix a) k) l))))

(in-theory (disable fn-shr-win))

; The window inside the buffer is the reader's slice.
(defthm fn-shr-win-is-slice
  (implies (and (natp a) (natp wn) (<= (+ a wn) (len l)) (true-listp l))
           (equal (fn-shr-win a wn l)
                  (fn-oct-slice-list a (+ a wn) l)))
  :hints (("Goal" :in-theory (enable fn-shr-win nfix)
           :use ((:instance fn-oct-slice-list-is-take-nthcdr
                            (i a) (n (+ a wn)) (fn-octets l))))))
