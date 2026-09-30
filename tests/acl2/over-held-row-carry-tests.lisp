(in-package "ACL2")
(include-book "../../books/over-held-row-carry")

(defun-nx ohrct-conclusion (s fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((next (mv-nth 1 (fn-ohr-active-one s fn-arena))))
  (or (not next) (fn-ohr-carried-p next fn-arena))))

; Actual BEGIN/TICK trajectory at the last source byte, then actual ONE.
(defthm ohrct-positive-actual-parser-to-emitting-row
 (let* ((bytes '(83 117 98 106 101 99 116 58 32 120 13 10 13 10))
        (fn-arena (list bytes))
        (parser (mv-nth 0 (fn-lpc-tick (fn-lpc-begin 0 14 '(:source 17))
                                       13 fn-arena)))
        (s (fn-obc-make '("g" 1 3 7 nil t) '(:source 17) :parse parser nil 0)))
  (and (fn-ohr-carried-p s fn-arena)
       (ohrct-conclusion s fn-arena)
       (eq (nth 2 (mv-nth 1 (fn-ohr-active-one s fn-arena))) :emit)))
 :rule-classes nil)

(defthm ohrct-positive-actual-emitting-row
 (let* ((fn-arena nil)
        (s (fn-obc-make '("g" 2 3 7 nil nil) '(:source 17) :emit nil '("abc") 0)))
  (and (fn-ohr-carried-p s fn-arena) (ohrct-conclusion s fn-arena)))
 :rule-classes nil)

; Corrupted-state removal of the sole carried-domain premise.
(defthm ohrct-removal-carried-domain
 (let* ((fn-arena nil)
        (s (fn-obc-make '("g" 2 3 7 nil nil) '(:source 17)
                         :emit nil '("abc" 300) 0)))
  (and (not (fn-ohr-carried-p s fn-arena))
       (not (ohrct-conclusion s fn-arena))))
 :rule-classes nil)
