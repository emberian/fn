(defcolumns fn2-run-cursors
 ((phase (:enum fn2-run-cursor-phase (:idle :header :seek :child :miss :found :absent :failed :at :up :end :lost)))
  (schema :u60) (level :u8) (top :u8) (left :bool) (slot :u32) (gen :u60) (lo :u32) (hi :u32) (idx :u32) (off :u32)
  (unit :u60) (counter :u60) (rb :u32) (okind :u8) (oslot :u32) (ogen :u60)
  (physical :bool) (source-row :u32) (catalog-tag :u60) (epoch :u60) (run :u60) (resume-child :bool)
  (hash-0 :u32) (hash-1 :u32) (hash-2 :u32) (hash-3 :u32) (hash-4 :u32) (hash-5 :u32) (hash-6 :u32) (hash-7 :u32)))
