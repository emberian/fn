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
