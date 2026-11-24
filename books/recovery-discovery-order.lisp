; Visit the seal, records and dependency units first. An empty extent also
; requires checking every later unit for debris.
(in-package "ACL2")
(include-book "commit-geometry")
(fn2-book-layer :b)

(defun fn2-rec-discovery-unit (index)
 (declare (xargs :guard (natp index)))
 (if (< (nfix index) *fn2-commit-write-resources*)
     (- (1- *fn2-commit-write-resources*) (nfix index))
   (nfix index)))

(defun fn2-rec-next-discovery-unit (unit)
 (declare (xargs :guard (natp unit)))
 (let ((next (+ 1 (fn2-rec-discovery-unit unit))))
  (and (< next *fn2-storage-extent-units*) (fn2-rec-discovery-unit next))))

; The same permutation takes a physical unit back to its visit index.
(defthm fn2-rec-discovery-unit-inverse
 (equal (fn2-rec-discovery-unit (fn2-rec-discovery-unit index)) (nfix index)))

(defthm fn2-rec-discovery-unit-in-extent
 (implies (and (natp index) (< index *fn2-storage-extent-units*))
          (and (natp (fn2-rec-discovery-unit index))
               (< (fn2-rec-discovery-unit index) *fn2-storage-extent-units*))))

(defthm fn2-rec-discovery-visits-successor
 (implies (and (natp index) (< index *fn2-storage-extent-units*))
          (equal (fn2-rec-next-discovery-unit (fn2-rec-discovery-unit index))
                 (and (< (+ 1 index) *fn2-storage-extent-units*)
                      (fn2-rec-discovery-unit (+ 1 index)))))
 :hints (("Goal" :in-theory (e/d (fn2-rec-next-discovery-unit) (fn2-rec-discovery-unit)))))

(assert-event (equal (fn2-rec-discovery-unit 0) 2))
