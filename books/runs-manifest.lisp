; Layer C1c: the manifest schema (C-MANIFEST-IS-A-RUN). The engine's directory
; of sealed runs is itself a run, keyed (schema, run), one entry per live run:
; its height, its entry count, its root page's identity and parent-held hash,
; and its filter page's (zero when it has none). Pages kind :manifest. The
; per-schema MIN-/MAX- fences of a run descriptor are not in the entry: they
; differ in shape per schema and the root page holds them (C-MANIFEST-ENTRY).
; Declared before a world's run assembly (runs-served.lisp includes it). The
; sealer (sealer.lisp) installs runs resident until B's run-replacement
; member (GC2) carries the manifest's pages; then it writes this run.
(in-package "ACL2")
(include-book "runs-schema")
(fn2-book-layer :c)

(defrunschema fn2-manifest :id 10
 :key ((schema (:id schema)) (run (:id run)))
 :value ((height :u8) (entries :varint)
         (root-unit (:id physical-unit)) (root-epoch (:id writer-epoch)) (root-allocation (:id allocation)) (root-hash :digest)
         (filter-unit (:id physical-unit)) (filter-epoch (:id writer-epoch)) (filter-allocation (:id allocation)) (filter-hash :digest))
 :merge :latest
 :page-kind :manifest)

; Shared field binding only: callers derive subject/Ref/hash from their
; actual completed source. Both producers own a 64-byte root/zero-filter window.
(defun fn2-manifest-bind-unfiltered (base schema run height entries unit epoch allocation slot gen fn2-fields)
 (declare (xargs :stobjs fn2-fields :guard (fn2-fields-wfp fn2-fields)))
 (b* (((unless (and (natp base) (<= (+ base *fn2-manifest-entry-num-fields*) (fn2-fields-rows fn2-fields))
                    (unsigned-byte-p 60 schema) (unsigned-byte-p 60 run) (unsigned-byte-p 8 height)
                    (unsigned-byte-p 60 entries) (unsigned-byte-p 60 unit) (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 allocation)
                    (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))) (mv :bounds fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-manifest-entry-field-schema*) schema fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-manifest-entry-field-run*) run fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-manifest-entry-field-height*) height fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-manifest-entry-field-entries*) entries fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-manifest-entry-field-root-unit*) unit fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-manifest-entry-field-root-epoch*) epoch fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-manifest-entry-field-root-allocation*) allocation fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-manifest-entry-field-filter-unit*) 0 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-manifest-entry-field-filter-epoch*) 0 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-manifest-entry-field-filter-allocation*) 0 fn2-fields))
      (fn2-fields (fn2-fields-put (+ base *fn2-manifest-entry-field-root-hash*)
       (value 1) (ref-slot slot) (ref-gen gen) (ref-off 0) (ref-len 32)))
      (fn2-fields (fn2-fields-put (+ base *fn2-manifest-entry-field-filter-hash*)
       (value 1) (ref-slot slot) (ref-gen gen) (ref-off 32) (ref-len 32))))
  (mv :ok fn2-fields)))
(fn2-fields-preserves fn2-manifest-bind-unfiltered
 (base schema run height entries unit epoch allocation slot gen fn2-fields) :position 1 :raw-rows t)
