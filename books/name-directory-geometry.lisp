; NAME limits shared by the existing writers and trusted startup accounting.
(in-package "ACL2")
(include-book "declare")
(fn2-book-layer :b)
(defconst *fn2-groups-name-max* 250)
(defconst *fn2-principals-name-max* 64)
(defconst *fn2-name-value-bytes* (ceiling 60 8))
