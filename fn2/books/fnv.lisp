; Shared FNV arithmetic for probe checksums and simulator evidence.
; This is not cryptographic identity; every runtime product is below 2^57.
(in-package "ACL2")
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)
(defun fn2-fnv-step (hash word)
  (declare (xargs :guard (and (unsigned-byte-p 32 hash) (unsigned-byte-p 32 word))))
  (mod (* 16777619 (logxor (ifix hash) (ifix word))) 4294967296))
(defthm fn2-fnv-step-type
  (unsigned-byte-p 32 (fn2-fnv-step hash word)))
(defthm fn2-fnv-step-natp
  (natp (fn2-fnv-step hash word)) :rule-classes :type-prescription)
(defthm fn2-fnv-step-bound
  (< (fn2-fnv-step hash word) 4294967296) :rule-classes :linear)
(in-theory (disable fn2-fnv-step))
