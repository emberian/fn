; The image layout decision belongs to ACL2. The host submits these offsets.
(in-package "ACL2")
(include-book "format-physical")
(fn2-book-layer :b)
(defconst *fn2-checkpoint-unit-bytes* 4096)
(defconst *fn2-checkpoint-anchor-slots* 4)

; New-image layout, in physical units:
; [3*extents arena][genesis + groups][bootstrap][four checkpoint anchors]
; [optional slack][two writer-epoch records]. Existing boot records and checkpoint
; anchors have different encodings and must never alias. D68 requires no legacy
; layout migration. Boot consumers must switch together before enabling this.
(defun fn2-checkpoint-image-sizep (size extents groups)
 (declare (xargs :guard t))
 (and (unsigned-byte-p 60 size) (equal (mod size *fn2-checkpoint-unit-bytes*) 0)
      (posp extents) (unsigned-byte-p 32 extents) (unsigned-byte-p 32 groups)
      (<= (* *fn2-checkpoint-unit-bytes* (+ (* 3 extents) groups 8)) size)))

(defun fn2-checkpoint-bootstrap-unit (extents groups)
 (declare (xargs :guard (and (natp extents) (natp groups))))
 (+ (* 3 extents) groups 1))

(defun fn2-checkpoint-anchor-unit (slot extents groups)
 (declare (xargs :guard (and (natp slot) (< slot 4) (natp extents) (natp groups))))
 (+ (fn2-checkpoint-bootstrap-unit extents groups) 1 slot))

(defun fn2-checkpoint-anchor-offset (slot size extents groups)
 (declare (xargs :guard t))
 (if (and (fn2-checkpoint-image-sizep size extents groups) (natp slot) (< slot 4))
     (mv :ok (* *fn2-checkpoint-unit-bytes* (fn2-checkpoint-anchor-unit slot extents groups)))
  (mv :geometry 0)))

(defthm fn2-checkpoint-anchor-offset-outside-arena
 (implies (and (fn2-checkpoint-image-sizep size extents groups) (natp slot) (< slot 4))
  (<= (* 12288 extents) (mv-nth 1 (fn2-checkpoint-anchor-offset slot size extents groups)))))
(defthm fn2-checkpoint-anchor-offset-before-epoch-pair
 (implies (and (fn2-checkpoint-image-sizep size extents groups) (natp slot) (< slot 4))
  (<= (+ 4096 (mv-nth 1 (fn2-checkpoint-anchor-offset slot size extents groups))) (- size 8192))))
(defthm fn2-checkpoint-anchor-offset-distinct
 (implies (and (fn2-checkpoint-image-sizep size extents groups)
               (natp a) (< a 4) (natp b) (< b 4) (not (equal a b)))
  (not (equal (mv-nth 1 (fn2-checkpoint-anchor-offset a size extents groups))
              (mv-nth 1 (fn2-checkpoint-anchor-offset b size extents groups))))))
