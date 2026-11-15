; Shared protocol workspace sizes consumed by actual upload TAKE and service admission.
(in-package "ACL2")
(include-book "commit-geometry")
(include-book "profile")
(fn2-book-layer :b)

(defconst *fn2-upload-header-octets* 16384)
(defconst *fn2-upload-digest-octets* 32)
(defconst *fn2-overview-octets-max* 1024)

; Header references and the eventual digest/overview scratch survive body reuse.
(defconst *fn2-upload-header-workspace-bytes*
 (+ *fn2-upload-header-octets* *fn2-upload-digest-octets* *fn2-overview-octets-max*))
(defconst *fn2-upload-body-window-bytes* *fn2-commit-unit-bytes*)


; Geometry only: existence, not a second minimum-class selector or quota
; promise. Actual initialization and TAKE use fn2-pool-class-for and the
; protected reservable counts, including aliases and zero-count classes.
(defun fn2-upload-window-size-fitp (bytes classes)
 (declare (xargs :guard t :measure (acl2-count classes)))
 (and (natp bytes) (consp classes)
      (or (and (consp (car classes)) (natp (cdar classes))
               (<= bytes (cdar classes)))
          (fn2-upload-window-size-fitp bytes (cdr classes)))))
(defun fn2-upload-window-profilep (profile)
 (declare (xargs :guard t))
 (let ((classes (fn2-profile-pool-classes profile)))
  (and (fn2-profile-classes-p classes)
       (fn2-upload-window-size-fitp *fn2-upload-header-workspace-bytes* classes)
       (fn2-upload-window-size-fitp *fn2-upload-body-window-bytes* classes))))
