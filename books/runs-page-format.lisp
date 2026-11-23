; On-disk run page layout and resident writer tables.
(in-package "ACL2")
(include-book "run-geometry")
(include-book "format-physical")
(include-book "format-storage")
(fn2-book-layer :c)


; B's header area, rounded to 32 bytes as the commit pages round it.
(defconst *fn2-run-header-area* (* 32 (ceiling *fn2-format-page-header-max-size* 32)))
(deflayout fn2-run-page-header
 '((schema (:id schema)) (schema-version :u8) (run (:id run)) (level :u8) (ordinal :varint)
   (entries :varint) (restarts :varint) (restart-interval :u8)))
(defconst *fn2-run-entries-base* (+ *fn2-run-header-area* *fn2-run-page-header-max-size*))
(deflayout fn2-run-restart '((offset :u32)))
(defconst *fn2-run-restart-bytes* *fn2-run-restart-max-size*)
; Every entry is at least one byte, so a 64 KiB page has at most this many
; restarts at interval 16; the interval is a page field, never below 16.
(defconst *fn2-run-restart-interval* 16)
(defconst *fn2-run-restart-capacity* 4096)
; A writer's fill limit (bytes of entries plus directory, from the page start)
; is a page-fill parameter like a block size; the encoded page stays 64 KiB.
(defconst *fn2-run-min-fill* 256)
(assert-event (<= (floor *fn2-run-page-size* *fn2-run-restart-interval*) *fn2-run-restart-capacity*))
; Per-writer field rows: the checker's decode range, the previous key, scratch.
(defconst *fn2-run-check-fields* *fn2-format-sealed-batch-num-fields*)
; An entry layout has at most 64 fields; its index layout adds the 8 fields of
; a child reference, so a decoded-entry region holds 80 rows.
(defconst *fn2-run-key-fields-max* 64)
(defconst *fn2-run-entry-rows* 80)
(defconst *fn2-run-prev-fields* *fn2-run-check-fields*)
(defconst *fn2-run-scratch-fields* (+ *fn2-run-prev-fields* *fn2-run-entry-rows*))
(defconst *fn2-run-writer-fields* (+ *fn2-run-scratch-fields* 2))

(defcolumns fn2-run-writers
 ((phase (:enum fn2-run-writer-phase (:idle :open :closing :heading :sealing :sealed :failed)))
  (schema :u60) (schema-version :u8) (level :u8) (run :u60) (ordinal :u60)
  (page-kind :u8) (slot :u32) (gen :u60) (cursor :u32) (entries :u32) (restarts :u32)
  (pos :u32) (prev :bool) (fields :u32) (limit :u32)
  (unit :u60) (epoch :u60) (counter :u60) (history :u60) (incarnation :u60)
  (okind :u8) (oslot :u32) (ogen :u60)))
(defcolumns fn2-run-restarts ((offset :u32)))
