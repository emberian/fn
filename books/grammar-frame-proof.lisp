; Discharge the framer's totality, linear consumption and bounded
; retention. Every branch of fn2-gram-frame is closed by arithmetic on
; (start, pos, left, fill, cap) alone: the scan's answer is only ever read
; through nfix and compared with its window, so no property of the octets
; or of fn2-pool-scan is needed.
(in-package "ACL2")
(include-book "grammar")
(include-book "owed-discharge")

(defthm fn2-gram-frame-total-linear-proved
  (fn2-gram-frame-total-linear$owed left start pos overflow cap slot gen okind oslot ogen pool)
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-gram-frame-total-linear$owed fn2-gram-frame-outcome-p
                                   fn2-gram-frame-shape-p fn2-gram-frame)
                                  (fn2-pool-scan)))))

(fn2-owed-discharge fn2-gram-frame-total-linear fn2-gram-frame-total-linear-proved)
