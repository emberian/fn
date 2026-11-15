; Immutable initializer geometry for the physical C loader. The profile,
; rather than an adoption caller, assigns its cursor and checker regions.
(in-package "ACL2")
(include-book "run-physical-resources")
(fn2-book-layer :c)
(defcolumns fn2-run-load-geometry
 ((version :u8) (cursors :u32) (transactions :u32) (reads :u32) (operations :u32)
  (upload-hash-rows :u32) (controls :u32) (prefix :u32) (format-rows :u32) (field-rows :u32) (digest-rows :u32)))
(defcolumns fn2-run-load-readiness
 ((phase (:enum fn2-run-load-readiness-phase (:idle :cursors :operations :complete :refused)))
  (scope (:enum fn2-run-load-readiness-scope (:cold :live))) (cut-commit :u60) (cut-event :u60)
  (tag :u60) (selected-generation :u60) (candidate :u32)
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (admissions :u60) (row :u32) (cursor-end :u32)))

(defun fn2-run-load-geometry-profilep (profile)
 (declare (xargs :guard t))
 (and (unsigned-byte-p 32 (fn2-profile-t profile))
      (unsigned-byte-p 32 (fn2-b-read-rows profile))
      (and (posp (fn2-profile-o profile)) (unsigned-byte-p 32 (fn2-profile-o profile)))
      (unsigned-byte-p 32 (fn2-b-run-cursor-rows profile))
      (unsigned-byte-p 32 (fn2-b-upload-windows profile))
      (unsigned-byte-p 32 (fn2-b-ctl-rows profile))
      (and (<= 4 (fn2-b-run-loader-row 0 profile)) (unsigned-byte-p 32 (fn2-b-run-loader-row 0 profile)))
      (unsigned-byte-p 32 (fn2-b-format-slots profile))
      (<= (fn2-b-format-floor profile) (fn2-b-format-slots profile))
      (unsigned-byte-p 32 (fn2-b-capacity :format-field-slots (fn2-b-field-rows profile) profile))
      (<= (fn2-b-field-rows profile) (fn2-b-capacity :format-field-slots (fn2-b-field-rows profile) profile))
      (unsigned-byte-p 32 (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile))
      (<= (fn2-b-digest-minimum profile) (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile))))
(defun fn2-run-load-geometry-profile-init (profile fn2-run-load-geometry)
 (declare (xargs :stobjs fn2-run-load-geometry :guard t))
 (let ((fn2-run-load-geometry (fn2-run-load-geometry-init 1 fn2-run-load-geometry)))
  (if (not (fn2-run-load-geometry-profilep profile)) fn2-run-load-geometry
   (fn2-run-load-geometry-put 0 (version 1) (cursors (fn2-b-run-cursor-rows profile))
    (transactions (fn2-profile-t profile)) (reads (fn2-b-read-rows profile)) (operations (fn2-profile-o profile))
    (upload-hash-rows (nfix (- (fn2-b-run-loader-row 0 profile) 4))) (controls (fn2-b-ctl-rows profile))
    (prefix (fn2-b-run-loader-row 0 profile)) (format-rows (fn2-b-format-slots profile))
    (field-rows (fn2-b-capacity :format-field-slots (fn2-b-field-rows profile) profile))
    (digest-rows (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile))))))
; Only the real core initializer calls PROFILE-INIT. No served operation
; writes this carrier; callbacks consume it as a readonly child.
(fn2-run-load-geometry-preserves fn2-run-load-geometry-profile-init
 (profile fn2-run-load-geometry) :position nil
 :hyps ((fn2-run-load-geometryp fn2-run-load-geometry))
 :specs (("-TYPE" fn2-run-load-geometryp nil) ("-WFP" fn2-run-load-geometry-wfp nil)))
(defthm fn2-run-load-geometry-profile-init-rows
 (equal (fn2-run-load-geometry-rows (fn2-run-load-geometry-profile-init profile fn2-run-load-geometry)) 1)
 :hints (("Goal" :in-theory (enable fn2-run-load-geometry-profile-init))))
(defthm fn2-run-load-geometry-profile-init-cursors
 (implies (fn2-run-load-geometry-profilep profile)
  (equal (fn2-run-load-geometry-cursors 0 (fn2-run-load-geometry-profile-init profile fn2-run-load-geometry))
         (fn2-b-run-cursor-rows profile)))
 :hints (("Goal" :in-theory (enable fn2-run-load-geometry-profile-init))))
