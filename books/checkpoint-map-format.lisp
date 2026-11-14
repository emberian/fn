; Linked allocation-map/recovery-arena page bodies. One allocator identity owns
; each 64KiB page; the chain has no resident-length or stored-data ceiling.
(in-package "ACL2")
(include-book "format")
(fn2-book-layer :b)
(deflayout fn2-checkpoint-map-header
 (append
  '((kind (:enum checkpoint-map-body-kind (:allocation-map :recovery-arena :event-proof-directory)))
    (version :u8) (cut-commit (:id commit)) (cut-event (:id event))
    (total-entries :varint) (page-ordinal :varint) (first-ordinal :varint)
    (entry-count :varint) (has-next :u8)
    (retired-head (:id extent)) (retired-count :varint))
  (fn2-format-prefix "NEXT-" *fn2-format-ref*)))

(defconst *fn2-checkpoint-map-body-start*
 (* 32 (ceiling *fn2-format-page-header-max-size* 32)))
(defconst *fn2-checkpoint-map-entries-start*
 (+ *fn2-checkpoint-map-body-start*
    (* 32 (ceiling *fn2-checkpoint-map-header-max-size* 32))))
(defconst *fn2-checkpoint-map-entry-width* *fn2-format-allocation-map-entry-max-size*)
(defconst *fn2-checkpoint-arena-entry-width* *fn2-format-recovery-arena-entry-max-size*)
(defconst *fn2-checkpoint-map-slots*
 (floor (- *fn2-format-page-size* *fn2-checkpoint-map-entries-start*) *fn2-checkpoint-map-entry-width*))
(defconst *fn2-checkpoint-arena-slots*
 (floor (- *fn2-format-page-size* *fn2-checkpoint-map-entries-start*) *fn2-checkpoint-arena-entry-width*))
(assert-event (and (posp *fn2-checkpoint-map-slots*) (posp *fn2-checkpoint-arena-slots*)))

(defun fn2-checkpoint-map-page-count (total slots)
 (declare (xargs :guard (and (natp total) (posp slots))))
 (max 1 (ceiling (nfix total) (max 1 (nfix slots)))))
(defun fn2-checkpoint-map-page-entries (total ordinal slots)
 (declare (xargs :guard (and (natp total) (natp ordinal) (posp slots))))
 (min (nfix slots) (nfix (- (nfix total) (* (nfix ordinal) (nfix slots))))))

; The reader must require this exact shape, and canonical zero next-Ref when
; HAS-NEXT=0. It then checks each fixed-width slot's decoded length and zero
; padding. No page can silently omit rows or extend beyond the declared map.
(defun fn2-checkpoint-map-page-shapep (total ordinal first count has-next slots)
 (declare (xargs :guard t))
 (and (natp total) (natp ordinal) (posp slots)
      (< ordinal (fn2-checkpoint-map-page-count total slots))
      (equal first (* ordinal slots))
      (equal count (fn2-checkpoint-map-page-entries total ordinal slots))
      (equal has-next (if (< (+ ordinal 1) (fn2-checkpoint-map-page-count total slots)) 1 0))))

(defthm fn2-checkpoint-map-page-slot-fits
 (implies (and (natp i) (< i *fn2-checkpoint-map-slots*))
  (<= (+ *fn2-checkpoint-map-entries-start* (* (+ i 1) *fn2-checkpoint-map-entry-width*))
      *fn2-format-page-size*)))
(defthm fn2-checkpoint-arena-page-slot-fits
 (implies (and (natp i) (< i *fn2-checkpoint-arena-slots*))
  (<= (+ *fn2-checkpoint-map-entries-start* (* (+ i 1) *fn2-checkpoint-arena-entry-width*))
      *fn2-format-page-size*)))
