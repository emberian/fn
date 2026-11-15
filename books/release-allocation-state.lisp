; One canonical release control, below machines/core declarations. Holding a
; staged/pending subject blocks disposal; it is not admission or FREE permission.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-allocation-release
 ((phase (:enum fn2-allocation-release-phase (:idle :staged :prepared :waiting :persisted :blocked :complete :uncertain)))
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (bank :bool) (candidate :u32) (checkpoint :u60) (cut-commit :u60) (cut-event :u60)
  (installation-commit :u60) (installation-event :u60) (history :u60) (incarnation :u60)
  (extent :u32) (epoch :u60) (allocation :u60) (retirement :u60) (next :u32)
  (storage-domain :u60) (physical-unit :u60) (descriptor-epoch :u60) (descriptor-allocation :u60)
  (page-kind :u60) (encoded-length :u60)
  (slot :u32) (gen :u60) (batch :u60) (event :u60)
  (journal :u32) (journal-epoch :u60) (journal-allocation :u60) (evidence-owned :bool))
 :extra-fields ((fn2-allocation-release-descriptor :type (array (unsigned-byte 8) (32)) :initially 0
  :why "Exact actual covering-Fence descriptor digest retained while a release packet is staged or uncertain.")))

(defun fn2-allocation-release-candidate-held-p (c checkpoint fn2-allocation-release)
 (declare (xargs :stobjs fn2-allocation-release :guard (fn2-allocation-release-wfp fn2-allocation-release)))
 (and (< 0 (fn2-allocation-release-rows fn2-allocation-release))
  (not (member-equal (fn2-allocation-release-phase 0 fn2-allocation-release)
    (list *fn2-allocation-release-phase-idle* *fn2-allocation-release-phase-complete*)))
  (equal c (fn2-allocation-release-candidate 0 fn2-allocation-release))
  (equal checkpoint (fn2-allocation-release-checkpoint 0 fn2-allocation-release))))

(defun fn2-release-descriptor-word (i fn2-allocation-release)
 (declare (xargs :stobjs fn2-allocation-release
  :guard (and (fn2-allocation-release-wfp fn2-allocation-release) (natp i) (< i 8))))
 (+ (fn2-allocation-release-descriptori (* 4 i) fn2-allocation-release)
    (ash (fn2-allocation-release-descriptori (+ 1 (* 4 i)) fn2-allocation-release) 8)
    (ash (fn2-allocation-release-descriptori (+ 2 (* 4 i)) fn2-allocation-release) 16)
    (ash (fn2-allocation-release-descriptori (+ 3 (* 4 i)) fn2-allocation-release) 24)))

(defthm fn2-release-descriptor-word-u32
 (implies (and (fn2-allocation-releasep fn2-allocation-release) (fn2-allocation-release-wfp fn2-allocation-release) (natp i) (< i 8))
  (unsigned-byte-p 32 (fn2-release-descriptor-word i fn2-allocation-release))))
