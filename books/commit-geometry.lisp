; Shared storage-unit geometry, independent of format checking.
(in-package "ACL2")
(include-book "format-base")
(fn2-book-layer :b)
; One geometry shared by packing, issuing, and the resource model.
(defconst *fn2-commit-unit-bytes* *fn2-format-sector-size*)
(defconst *fn2-commit-write-resources* 3)
(defconst *fn2-commit-pools* 4)
(defconst *fn2-commit-extent-bytes* *fn2-storage-extent-bytes*)
(defconst *fn2-commit-digest-bytes* 32)
