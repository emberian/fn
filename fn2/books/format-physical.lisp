; Independent declaration family; format.lisp exports the complete catalog.
(in-package "ACL2")
(include-book "format-base")
(fn2-book-layer :b)

(deflayout fn2-format-bootstrap
  `((magic :u32) (version :u8) (sector-size :varint) (page-size :varint) (anchor-0 (:id physical-unit)) (anchor-1 (:id physical-unit)) (anchor-2 (:id physical-unit)) (anchor-3 (:id physical-unit)) (storage-domain (:id storage-domain)) (geometry-hash :digest)))
(assert-event (fn2-layoutp *fn2-format-bootstrap*))
(assert-event (equal (fn2-layout-max-size *fn2-format-bootstrap*) 101))

(deflayout fn2-format-anchor
  (append
    `((slot (:id anchor-slot)) (history (:id history)) (incarnation (:id incarnation)) (checkpoint (:id checkpoint)) (checkpoint-batch :digest))
    (fn2-format-prefix "DESCRIPTOR-" *fn2-format-ref*)
    `((previous-checkpoint :digest) (geometry :digest) (anchor-hash :digest))))
(assert-event (fn2-layoutp *fn2-format-anchor*))
(assert-event (equal (fn2-layout-max-size *fn2-format-anchor*) 247))

(deflayout fn2-format-page-header
  `((magic :u32) (version :u8) (page-kind ,*fn2-format-page-kind*) (history (:id history)) (incarnation (:id incarnation)) (physical-unit (:id physical-unit)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (header-length :varint) (payload-length :varint)))
(assert-event (fn2-layoutp *fn2-format-page-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-page-header*) 69))

(deflayout fn2-format-raw-source-context
  `((storage-domain (:id storage-domain)) (history (:id history)) (incarnation (:id incarnation)) (physical-unit (:id physical-unit)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (actual-length :varint) (logical-source-offset :varint)))
(assert-event (fn2-layoutp *fn2-format-raw-source-context*))
(assert-event (equal (fn2-layout-max-size *fn2-format-raw-source-context*) 72))

(deflayout fn2-format-frame-header
  `((magic :u32) (frame-kind (:enum frame-kind (:records :seal :continuation))) (history (:id history)) (incarnation (:id incarnation)) (writer-epoch (:id writer-epoch)) (commit (:id commit)) (extent (:id extent)) (extent-writer-epoch (:id writer-epoch)) (extent-allocation (:id allocation)) (ordinal :varint) (fragment-offset :varint) (payload-length :varint)))
(assert-event (fn2-layoutp *fn2-format-frame-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-frame-header*) 95))

(deflayout fn2-format-frame-trailer
  `((frame-hash :digest)))
(assert-event (fn2-layoutp *fn2-format-frame-trailer*))
(assert-event (equal (fn2-layout-max-size *fn2-format-frame-trailer*) 33))

