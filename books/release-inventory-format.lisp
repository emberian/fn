; Authenticated pending RELEASE inventory entries. These are original physical
; journal identities, never an archive page's identity or a runtime catalog row.
; Only the frozen complete producer can give omission of settled rows meaning.
(in-package "ACL2")
(include-book "checkpoint-map-format")
(fn2-book-layer :b)
(deflayout fn2-release-inventory-entry
 (append
 '((journal-history (:id history)) (journal-incarnation (:id history-incarnation))
   (journal-extent (:id extent)) (journal-writer-epoch (:id writer-epoch))
   (journal-allocation (:id allocation)) (commit (:id commit)) (event (:id event))
   (extent (:id extent)) (writer-epoch (:id writer-epoch))
   (allocation (:id allocation)) (retirement-commit (:id commit))
   (checkpoint (:id checkpoint)) (cut-commit (:id commit)) (cut-event (:id event))
   (history (:id history)) (incarnation (:id history-incarnation))
   (installation-commit (:id commit)) (installation-event (:id event))
   (installation-history (:id history)) (installation-incarnation (:id history-incarnation))
   (installation-extent (:id extent)) (installation-writer-epoch (:id writer-epoch))
   (installation-allocation (:id allocation)))
 (fn2-format-prefix "DESCRIPTOR-" *fn2-format-ref*)))
(defconst *fn2-release-inventory-entry-width* *fn2-release-inventory-entry-max-size*)
(defconst *fn2-release-inventory-slots*
 (floor (- *fn2-format-page-size* *fn2-checkpoint-map-entries-start*) *fn2-release-inventory-entry-width*))
(assert-event (posp *fn2-release-inventory-slots*))
(defthm fn2-release-inventory-entry-slot-fits
 (implies (and (natp i) (< i *fn2-release-inventory-slots*))
  (<= (+ *fn2-checkpoint-map-entries-start* (* (+ i 1) *fn2-release-inventory-entry-width*))
      *fn2-format-page-size*)))
