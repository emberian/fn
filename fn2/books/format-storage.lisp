; Independent declaration family; format.lisp exports the complete catalog.
(in-package "ACL2")
(include-book "format-base")

(deflayout fn2-format-root-recipe
  (append
    (fn2-format-prefix "CHECKPOINT-BASE-" *fn2-format-ref*)
    `((suffix-first (:id commit)) (suffix-last (:id commit)))
    (fn2-format-prefix "PHYSICAL-MANIFEST-" *fn2-format-ref*)
    (fn2-format-prefix "ALLOCATION-CHANGES-" *fn2-format-ref*)
    (fn2-format-prefix "EVENT-FRONTIER-" *fn2-format-ref*)
    (fn2-format-prefix "CONFIGURATION-GENERATIONS-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-root-recipe*))
(assert-event (equal (fn2-layout-max-size *fn2-format-root-recipe*) 413))

(deflayout fn2-format-sealed-batch
  (append
    `((history (:id history)) (incarnation (:id incarnation)) (extent (:id extent)) (extent-writer-epoch (:id writer-epoch)) (extent-allocation (:id allocation)) (commit (:id commit)) (previous-commit (:id commit)) (previous-seal :digest) (input-root :digest) (event-first (:id event)) (event-last (:id event)) (record-stream :digest))
    (fn2-format-prefix "DEPENDENCIES-" *fn2-format-ref*)
    (fn2-format-prefix "ALLOCATION-RETIREMENT-" *fn2-format-ref*)
    (fn2-format-prefix "METADATA-EDITS-" *fn2-format-ref*)
    (fn2-format-prefix "OUTPUT-" *fn2-format-root-recipe*)
    (fn2-format-prefix "EVENT-FRONTIER-" *fn2-format-ref*)
    `((final-seal :digest))))
(assert-event (fn2-layoutp *fn2-format-sealed-batch*))
(assert-event (equal (fn2-layout-max-size *fn2-format-sealed-batch*) 942))

(deflayout fn2-format-dependency-entry
  (append
    (fn2-format-prefix "TARGET-" *fn2-format-ref*)
    `((length :varint) (digest :digest))))
(assert-event (fn2-layoutp *fn2-format-dependency-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-dependency-entry*) 121))

(deflayout fn2-format-source-manifest-header
  `((source-length :varint) (block-size :varint) (source-identity :digest)))
(assert-event (fn2-layoutp *fn2-format-source-manifest-header*))
(assert-event (equal (fn2-layout-max-size *fn2-format-source-manifest-header*) 51))

(deflayout fn2-format-source-manifest-entry
  (append
    `((logical-offset :varint) (length :varint))
    (fn2-format-prefix "BLOCK-" *fn2-format-ref*)
    `((subtree-cv :digest))))
(assert-event (fn2-layoutp *fn2-format-source-manifest-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-source-manifest-entry*) 130))

(deflayout fn2-format-allocation-map-entry
  `((extent (:id extent)) (state (:enum allocation-state (:free :reserved :allocated :retire-pending))) (owner-kind :u8) (owner (:id owner)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation)) (retirement-commit (:id commit))))
(assert-event (fn2-layoutp *fn2-format-allocation-map-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-allocation-map-entry*) 47))

(deflayout fn2-format-checkpoint-descriptor
  (append
    `((checkpoint (:id checkpoint)) (cut-commit (:id commit)) (cut-event (:id event)))
    (fn2-format-prefix "METADATA-MANIFEST-" *fn2-format-ref*)
    (fn2-format-prefix "ALLOCATION-STATE-" *fn2-format-ref*)
    (fn2-format-prefix "EVENT-PROOF-DIRECTORY-" *fn2-format-ref*)
    (fn2-format-prefix "EVENT-FRONTIER-" *fn2-format-ref*)
    (fn2-format-prefix "RECOVERY-ARENA-" *fn2-format-ref*)))
(assert-event (fn2-layoutp *fn2-format-checkpoint-descriptor*))
(assert-event (equal (fn2-layout-max-size *fn2-format-checkpoint-descriptor*) 422))

(deflayout fn2-format-recovery-arena-entry
  `((extent-physical-unit (:id physical-unit)) (writer-epoch (:id writer-epoch)) (allocation (:id allocation))))
(assert-event (fn2-layoutp *fn2-format-recovery-arena-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-recovery-arena-entry*) 27))

(deflayout fn2-format-membership-entry
  `((group (:id group)) (group-number (:id group-number)) (article (:id article))))
(assert-event (fn2-layoutp *fn2-format-membership-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-membership-entry*) 27))

(deflayout fn2-format-key-entry
  `((key (:id key))))
(assert-event (fn2-layoutp *fn2-format-key-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-key-entry*) 9))

(deflayout fn2-format-configuration-generation-entry
  `((configuration (:id configuration))))
(assert-event (fn2-layoutp *fn2-format-configuration-generation-entry*))
(assert-event (equal (fn2-layout-max-size *fn2-format-configuration-generation-entry*) 9))

