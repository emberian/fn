; Fixed private requested-window storage. PRF-1109 component.
; No public accessor is authorized by this book; the verifier/controller
; publishes only after the entire protected prefix and trailer pass.
(in-package "ACL2")
(include-book "octets-stobj")

(defstobj fn-ew-buffer
  (fn-ew-bytes :type (array (unsigned-byte 8) (16384)) :initially 0)
  :inline t)

(defun fn-ewb-copy (src count dst fn-octets fn-ew-buffer)
  (declare (xargs :stobjs (fn-octets fn-ew-buffer)
                  :guard (and (natp src) (natp count) (<= count 64)
                              (natp dst) (<= (+ src count) (fn-octets-len fn-octets))
                              (<= (+ dst count) 16384))
                  :measure (nfix count)))
  (if (zp count) fn-ew-buffer
    (let ((fn-ew-buffer
            (update-fn-ew-bytesi dst (fn-octets-get src fn-octets) fn-ew-buffer)))
      (fn-ewb-copy (+ 1 src) (1- count) (+ 1 dst) fn-octets fn-ew-buffer))))

(local
 (defthm fn-ewb-nth-update
   (implies (and (natp i) (natp j))
            (equal (nth i (update-nth j v xs))
                   (if (equal i j) v (nth i xs))))))

; Every resulting byte is exactly the requested input byte or the untouched
; prior byte. This describes the entire output and all buffer effects,
; including the bytes outside the requested copy. There is no output list
; construction in the executable copy.
(defthm fn-ewb-copy-exact-output-and-effects
  (implies (and (natp src) (natp count) (natp dst) (natp j))
           (equal (nth j (nth 0 (fn-ewb-copy src count dst fn-octets fn-ew-buffer)))
                  (if (and (<= dst j) (< j (+ dst count)))
                      (nth (+ src (- j dst)) fn-octets)
                    (nth j (nth 0 fn-ew-buffer)))))
  :hints (("Goal" :induct (fn-ewb-copy src count dst fn-octets fn-ew-buffer)
           :in-theory (enable update-fn-ew-bytesi))))

(defthm fn-ewb-copy-preserves-buffer-length
  (implies (and (natp src) (natp count) (natp dst)
                (<= (+ dst count) (len (nth 0 fn-ew-buffer))))
           (equal (len (nth 0 (fn-ewb-copy src count dst fn-octets fn-ew-buffer)))
                  (len (nth 0 fn-ew-buffer)))))

(in-theory (disable fn-ewb-copy))
