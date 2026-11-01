; Shared FNV arithmetic for probe checksums and simulator evidence.
; This is not cryptographic identity; every runtime product is below 2^57.
(in-package "ACL2")
(include-book "operations")
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)
(defun fn2-fnv-step (hash word)
  (declare (xargs :guard (and (unsigned-byte-p 32 hash) (unsigned-byte-p 32 word))))
  (mod (* *fn2-fnv-prime* (logxor (ifix hash) (ifix word))) 4294967296))
(defthm fn2-fnv-step-type
  (unsigned-byte-p 32 (fn2-fnv-step hash word)))
(defthm fn2-fnv-step-natp
  (natp (fn2-fnv-step hash word)) :rule-classes :type-prescription)
(defthm fn2-fnv-step-bound
  (< (fn2-fnv-step hash word) 4294967296) :rule-classes :linear)
; Known answers protect independent integrity judgments from a shared broken primitive.
(local (defun fn2-fnv-fold (octets hash)
         (if (atom octets) hash
           (fn2-fnv-fold (cdr octets) (fn2-fnv-step hash (car octets))))))
(assert-event (and (equal (fn2-fnv-fold nil *fn2-fnv-offset-basis*) *fn2-fnv-offset-basis*)
                   (equal (fn2-fnv-fold '(97) *fn2-fnv-offset-basis*) #xe40c292c)
                   (equal (fn2-fnv-fold '(102 111 111 98 97 114) *fn2-fnv-offset-basis*) #xbf9cf968)))
(in-theory (disable fn2-fnv-step))
