; Wire octets of the digest held by a page parent.
(in-package "ACL2")
(include-book "format-check")

(defun fn2-page-parent-octets (k n words)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil
    (cons (fn2-fc-word-byte (nth (floor k 4) words) (mod k 4))
          (fn2-page-parent-octets (1+ k) (1- n) words))))

(defthmd fn2-page-parent-word-from-list
   (implies (and (natp i) (< i 8))
            (equal (fn2-digest-word row i ds) (nth i (fn2-digest-list row ds))))
   :hints (("Goal" :cases ((equal i 0) (equal i 1) (equal i 2) (equal i 3)
                            (equal i 4) (equal i 5) (equal i 6))
            :in-theory (enable fn2-digest-word fn2-digest-list nth))))
