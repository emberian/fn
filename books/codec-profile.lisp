; Shared upgrade staging follows the admitted connection RX class.
(in-package "ACL2")
(include-book "profile")
(fn2-book-layer :a)

(defun fn2-codec-seed-capacity (profile)
 (declare (xargs :guard t))
 (let ((classes (fn2-profile-pool-classes profile)))
  (if (and (consp classes) (consp (car classes))) (nfix (cdar classes)) 0)))
(defun fn2-codec-seed-reservation-bytes (profile)
 (declare (xargs :guard t))
 ; One codec layer. Stacked codecs reserve each layer's staging separately.
 (* (nfix (fn2-profile-c profile)) (fn2-codec-seed-capacity profile)))
(defun fn2-codec-upgrade-turns (seed-capacity copy-quantum)
 (declare (xargs :guard t))
 (if (and (unsigned-byte-p 32 seed-capacity) (posp copy-quantum)
          (unsigned-byte-p 32 copy-quantum))
     (mv :ok (+ 2 (ceiling seed-capacity copy-quantum)))
   (mv :bounds 0)))
