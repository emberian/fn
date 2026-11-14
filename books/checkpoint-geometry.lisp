; The image layout decision belongs to ACL2. The host submits these offsets.
(in-package "ACL2")
(include-book "format-physical")
(fn2-book-layer :b)
(defconst *fn2-checkpoint-unit-bytes* *fn2-format-sector-size*)
(defconst *fn2-checkpoint-anchor-slots* 4)

; New-image layout, in physical units:
; [storage-extent-units*extents arena][genesis + groups][bootstrap][four checkpoint anchors]
; [optional slack][two writer-epoch records]. Existing boot records and checkpoint
; anchors have different encodings and must never alias. D68 requires no legacy
; layout migration. Boot consumers must switch together before enabling this.
(defun fn2-checkpoint-image-sizep (size extents groups)
 (declare (xargs :guard t))
 (and (unsigned-byte-p 60 size) (equal (mod size *fn2-checkpoint-unit-bytes*) 0)
      (posp extents) (unsigned-byte-p 32 extents) (unsigned-byte-p 32 groups)
      (<= (* *fn2-checkpoint-unit-bytes* (+ (* *fn2-storage-extent-units* extents) groups 8)) size)))

(defun fn2-checkpoint-bootstrap-unit (extents groups)
 (declare (xargs :guard (and (natp extents) (natp groups))))
 (+ (* *fn2-storage-extent-units* extents) groups 1))

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
  (<= (* *fn2-storage-extent-bytes* extents) (mv-nth 1 (fn2-checkpoint-anchor-offset slot size extents groups)))))
(defthm fn2-checkpoint-anchor-offset-before-epoch-pair
 (implies (and (fn2-checkpoint-image-sizep size extents groups) (natp slot) (< slot 4))
  (<= (+ *fn2-checkpoint-unit-bytes* (mv-nth 1 (fn2-checkpoint-anchor-offset slot size extents groups))) (- size (* 2 *fn2-checkpoint-unit-bytes*)))))
(defthm fn2-checkpoint-anchor-offset-distinct
 (implies (and (fn2-checkpoint-image-sizep size extents groups)
               (natp a) (< a 4) (natp b) (< b 4) (not (equal a b)))
  (not (equal (mv-nth 1 (fn2-checkpoint-anchor-offset a size extents groups))
              (mv-nth 1 (fn2-checkpoint-anchor-offset b size extents groups))))))

; Geometry hash v1 preimage: the exact 21 ASCII octets below, immediately
; followed by this generated codec's canonical encoding. No padding, newline,
; Lisp printing or terminating NUL enters the hash. Size is bytes; all physical
; positions are 4096-byte units. Epoch units are the final two units.
(defconst *fn2-checkpoint-geometry-domain* "fn2/image-geometry/v1")
(deflayout fn2-checkpoint-geometry-record
 '((version :u8) (image-bytes :varint) (sector-bytes :varint) (page-bytes :varint)
   (extent-units :varint) (extents :varint) (groups :varint) (bootstrap :varint)
   (anchor-0 :varint) (anchor-1 :varint) (anchor-2 :varint) (anchor-3 :varint)
   (epoch-0 :varint) (epoch-1 :varint) (storage-domain :varint)))
