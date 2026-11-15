; Checkpoint event directory entries retain original journal allocations.
; SEMANTIC-SEAL authenticates the journal seal body, not a complete frame Ref.
(in-package "ACL2")
(include-book "checkpoint-map-format")
(fn2-book-layer :b)
(deflayout fn2-event-proof-entry
 '((commit (:id commit)) (event-first (:id event)) (members :varint)
   (extent (:id extent)) (writer-epoch (:id writer-epoch))
   (allocation (:id allocation)) (semantic-seal :digest)))
(defconst *fn2-event-proof-entry-width* *fn2-event-proof-entry-max-size*)
(defconst *fn2-event-proof-slots*
 (floor (- *fn2-format-page-size* *fn2-checkpoint-map-entries-start*) *fn2-event-proof-entry-width*))
(assert-event (posp *fn2-event-proof-slots*))
(defthm fn2-event-proof-entry-slot-fits
 (implies (and (natp i) (< i *fn2-event-proof-slots*))
  (<= (+ *fn2-checkpoint-map-entries-start* (* (+ i 1) *fn2-event-proof-entry-width*))
      *fn2-format-page-size*)))

; A frontier has exactly 60 possible peaks because event counts are u60.
; Occupancy comes from LEAF-COUNT's bits; unoccupied digest slots are zero.
; DIRECTORY is the actual sealed root3 Ref, constructed before this root4.
(deflayout fn2-event-frontier-header
 (append '((kind (:enum checkpoint-event-frontier-kind (:semantic-member-frontier)))
           (version :u8) (cut-commit (:id commit)) (cut-event (:id event))
           (leaf-count (:id event)))
         (fn2-format-prefix "DIRECTORY-" *fn2-format-ref*)))
(defconst *fn2-event-frontier-peaks-start*
 (+ *fn2-checkpoint-map-body-start* (* 32 (ceiling *fn2-event-frontier-header-max-size* 32))))
(defconst *fn2-event-frontier-bytes* (* 60 32))
(assert-event (<= (+ *fn2-event-frontier-peaks-start* *fn2-event-frontier-bytes*) *fn2-format-page-size*))
