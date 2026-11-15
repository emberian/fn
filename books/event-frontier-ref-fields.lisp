; One declaration-derived Ref field writer for frontier directory/inventory.
; The owning producer establishes the exact completed child; this only packs
; its verified identity and an already retained hash window into codec fields.
(in-package "ACL2")
(include-book "event-proof-format")
(include-book "checkpoint-page-state")
(fn2-book-layer :c)
(defun fn2-event-frontier-ref-bindings (fields prefix)
 (declare (xargs :verify-guards nil))
 (if (atom fields) nil
  (let* ((field (caar fields))
         (index (intern-in-package-of-symbol
          (concatenate 'string "*FN2-EVENT-FRONTIER-HEADER-FIELD-" prefix (symbol-name field) "*") 'fn2-core))
         (value (case field
          (storage-domain '*fn2-checkpoint-served-storage-domain*)
          (physical-unit '(* frontier-ref-extent *fn2-storage-extent-units*))
          (writer-epoch '(fn2-checkpoint-page-verified-epoch frontier-ref-extent fn2-checkpoint-page-verified))
          (allocation '(fn2-checkpoint-page-verified-allocation frontier-ref-extent fn2-checkpoint-page-verified))
          (page-kind '(fn2-checkpoint-page-verified-page-kind frontier-ref-extent fn2-checkpoint-page-verified))
          (encoded-length '(fn2-checkpoint-page-verified-encoded-length frontier-ref-extent fn2-checkpoint-page-verified))
          (otherwise (if (eq field 'expected-hash) nil
           (er hard 'fn2-event-frontier-ref-bindings "Unknown Ref field ~x0." field))))))
   (cons
    (if (eq field 'expected-hash)
     `(fn2-fields (fn2-fields-put (+ frontier-ref-base ,index)
       (value 1) (ref-slot frontier-ref-scratch) (ref-gen frontier-ref-sgen)
       (ref-off frontier-ref-offset) (ref-len 32)))
     `(fn2-fields (fn2-fields-set-value (+ frontier-ref-base ,index) ,value fn2-fields)))
    (fn2-event-frontier-ref-bindings (cdr fields) prefix)))))
(defmacro fn2-event-frontier-put-ref (prefix base extent offset scratch sgen)
 (if (not (member-equal prefix '("DIRECTORY-" "INVENTORY-")))
  (er hard 'fn2-event-frontier-put-ref "Unknown frontier Ref prefix ~x0." prefix)
  `(let* ((frontier-ref-base ,base) (frontier-ref-extent ,extent)
          (frontier-ref-offset ,offset) (frontier-ref-scratch ,scratch) (frontier-ref-sgen ,sgen)
          ,@(fn2-event-frontier-ref-bindings *fn2-format-ref* prefix)) fn2-fields)))
