; Exact required forms from the frozen actual shared cursor implementation.
(defcolumns fn2-run-cursors
 ((phase (:enum fn2-run-cursor-phase (:idle :header :seek :child :miss :found :absent :failed :at :up :end :lost)))
  (schema :u60) (level :u8) (top :u8) (left :bool) (slot :u32) (gen :u60) (lo :u32) (hi :u32) (idx :u32) (off :u32)
  (unit :u60) (counter :u60) (rb :u32) (okind :u8) (oslot :u32) (ogen :u60)
  (physical :bool) (source-row :u32) (catalog-tag :u60) (epoch :u60) (run :u60) (priority :u60) (resume-child :bool)
  (hash-0 :u32) (hash-1 :u32) (hash-2 :u32) (hash-3 :u32) (hash-4 :u32) (hash-5 :u32) (hash-6 :u32) (hash-7 :u32)))
(defun fn2-run-cursor-hash-word (c i fn2-run-cursors)
 (declare (xargs :stobjs fn2-run-cursors
  :guard (and (fn2-run-cursors-wfp fn2-run-cursors) (natp c) (< c (fn2-run-cursors-rows fn2-run-cursors)) (natp i) (< i 8))))
 (case i
  (0 (fn2-run-cursors-hash-0 c fn2-run-cursors))
  (1 (fn2-run-cursors-hash-1 c fn2-run-cursors))
  (2 (fn2-run-cursors-hash-2 c fn2-run-cursors))
  (3 (fn2-run-cursors-hash-3 c fn2-run-cursors))
  (4 (fn2-run-cursors-hash-4 c fn2-run-cursors))
  (5 (fn2-run-cursors-hash-5 c fn2-run-cursors))
  (6 (fn2-run-cursors-hash-6 c fn2-run-cursors))
  (otherwise (fn2-run-cursors-hash-7 c fn2-run-cursors))
))
