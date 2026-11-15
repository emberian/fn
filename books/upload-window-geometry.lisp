; Shared protocol workspace sizes consumed by actual upload TAKE and service admission.
(in-package "ACL2")
(include-book "commit-geometry")
(fn2-book-layer :b)

(defconst *fn2-upload-header-octets* 16384)
(defconst *fn2-upload-digest-octets* 32)
(defconst *fn2-overview-octets-max* 1024)

; Header references and the eventual digest/overview scratch survive body reuse.
(defconst *fn2-upload-header-workspace-bytes*
 (+ *fn2-upload-header-octets* *fn2-upload-digest-octets* *fn2-overview-octets-max*))
(defconst *fn2-upload-body-window-bytes* *fn2-commit-unit-bytes*)
