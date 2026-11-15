; Shared field equality only. The caller still authenticates bytes, hash,
; namespace, publication provenance and strict cut/installation ordering.
(in-package "ACL2")
(include-book "format")
(include-book "columns")
(fn2-book-layer :b)
(defun fn2-checkpoint-installation-ref-fields-p (kind checkpoint domain unit epoch allocation kind-ref length base fn2-fields)
 (declare (xargs :stobjs fn2-fields :guard (fn2-fields-wfp fn2-fields)))
 (and (natp base) (<= (+ base *fn2-format-checkpoint-installation-num-fields*) (fn2-fields-rows fn2-fields))
      (equal kind *record-kind-checkpoint-installation*)
      (equal (fn2-fields-value (+ base
                            *fn2-format-checkpoint-installation-field-checkpoint*)
                         fn2-fields)
       checkpoint)
      (equal (fn2-fields-value (+ base
                            *fn2-format-checkpoint-installation-field-descriptor-storage-domain*
                            0)
                         fn2-fields)
       domain)
      (equal (fn2-fields-value (+ base
                            *fn2-format-checkpoint-installation-field-descriptor-storage-domain*
                            1)
                         fn2-fields)
       unit)
      (equal (fn2-fields-value (+ base
                            *fn2-format-checkpoint-installation-field-descriptor-storage-domain*
                            2)
                         fn2-fields)
       epoch)
      (equal (fn2-fields-value (+ base
                            *fn2-format-checkpoint-installation-field-descriptor-storage-domain*
                            3)
                         fn2-fields)
       allocation)
      (equal (fn2-fields-value (+ base
                            *fn2-format-checkpoint-installation-field-descriptor-storage-domain*
                            4)
                         fn2-fields)
       kind-ref)
      (equal (fn2-fields-value (+ base
                            *fn2-format-checkpoint-installation-field-descriptor-storage-domain*
                            5)
                         fn2-fields)
       length)
      (equal (fn2-fields-value (+ base
                            *fn2-format-checkpoint-installation-field-descriptor-storage-domain*
                            6)
                         fn2-fields)
       1)))
