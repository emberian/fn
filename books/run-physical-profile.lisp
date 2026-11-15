; Full-provider profile initialization, isolated from the physical resource leaf.
; These are the existing initializer bodies; no second initializer is defined.
(in-package "ACL2")
(include-book "run-physical-resources")
(fn2-book-layer :c)

(defun fn2-run-load-checker-init (c prefix fn2-run-loads)
 (declare (xargs :stobjs fn2-run-loads :measure (nfix (- (fn2-run-loads-rows fn2-run-loads) (nfix c)))
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (natp c) (natp prefix))))
 (if (>= (nfix c) (fn2-run-loads-rows fn2-run-loads)) fn2-run-loads
  (let ((fn2-run-loads (if (unsigned-byte-p 32 (+ prefix c))
                       (fn2-run-loads-set-checker c (+ prefix c) fn2-run-loads) fn2-run-loads)))
   (fn2-run-load-checker-init (+ c 1) prefix fn2-run-loads))))
(defun fn2-run-load-profile-init (profile fn2-run-loads)
 (declare (xargs :stobjs fn2-run-loads
 :guard (and (unsigned-byte-p 32 (fn2-b-run-cursor-rows profile))
             (unsigned-byte-p 32 (+ 4 (fn2-b-upload-windows profile) (fn2-b-run-cursor-rows profile))))))
 (let ((fn2-run-loads (fn2-run-loads-init (fn2-b-run-cursor-rows profile) fn2-run-loads)))
  (fn2-run-load-checker-init 0 (+ 4 (fn2-b-upload-windows profile)) fn2-run-loads)))
