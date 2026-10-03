; A scalar execution seam over the existing A-DURABLE-LZ value. No new
; assumption is introduced: the native authenticated window implementation
; must return this same byte, or refuse without returning a byte.
(in-package "ACL2")
(include-book "assumptions-durable")
(include-book "octets-stobj")

(defun fn-durable-realize-lz-octet
    (file eoff elen poff compressed trailer decoded dict i)
  (declare (xargs :guard t))
  (fn-oct-nth i (fn-durable-realize-lz file eoff elen poff compressed
                                    trailer decoded dict)))

(defthm fn-durable-realize-lz-octet-is-decoded-nth
  (equal (fn-durable-realize-lz-octet
          file eoff elen poff compressed trailer decoded dict i)
         (nth i (fn-lzr-lz-value dict
                  (fn-durable-octets file poff compressed) decoded)))
  :hints (("Goal" :in-theory (enable fn-durable-realize-lz-octet))))

(in-theory (disable fn-durable-realize-lz-octet))
