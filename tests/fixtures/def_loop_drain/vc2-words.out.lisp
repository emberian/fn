(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

; words I .. I+K-1 of the image, as a list
(def-loop fn-hp-x-words (i k pgs-mem)
  :shape :step :over (k i) :done (zp k)
  :body (pgs-wi i pgs-mem)
  :next ((1- k) (+ 1 i)) :measure (nfix k)
  :guard (and (natp i) (natp k) (<= (+ i k) (pgs-w-length pgs-mem))) :stobjs pgs-mem)

