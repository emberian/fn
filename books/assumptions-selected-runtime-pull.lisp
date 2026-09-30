; A-SELECTED-RUNTIME-PULL-OBJECTS: reviewed scalar helper object path only.
; Qualification requires the exact source/component coordinate below. It is
; not attestation of a candidate image or whole call/frame/collector demand.
(in-package "ACL2")
(include-book "assumptions-selected-runtime-primitives")

(defconst *fn-srp-selected-pull-body*
 '("32c15d406048eaf68337dc9b6ae27ae9709a9c632e04cccd20bd5dc393faa1c2"
   "74b21cd673beea34570bf73e598af17de39d902acc356bf6b7ab3d42356d4cdb"
   "268777e192696bd00ded68c72cf0d1e8b8b7b5afde5126bd113c0dac34249b41"
   "84045032be25dcb9aac1f0f9570194b9a729be66231182ba230377ebf2e50228"))

(defun fn-srp-pull-coordinate-p (coordinate body)
 (declare (xargs :guard t))
 (and (fn-srp-coordinate-p coordinate)
      (equal body *fn-srp-selected-pull-body*)))

(defun fn-srp-pull-object-domain-p (bits nbits octet)
 (declare (xargs :guard t))
 (and (natp bits) (natp nbits) (<= nbits 31)
      (natp octet) (<= octet 255) (< bits (expt 2 nbits))))

; Executed selected CL ASH(1,n), 0<=n<=31, returns its tagged fixnum without
; allocation. GENERIC-* and GENERIC-+ likewise return fitting fixnum results;
; the source join separately proves every relevant mathematical bound.
; No result/workspace object is created in these selected arithmetic paths.
; XEP/control stack, wrappers/cache/fault/GC and other helper calls excluded.
(encapsulate
 (((fn-assume-srp-pull-object-octets * * * * *) => *))
 (local (defun fn-assume-srp-pull-object-octets
               (bits nbits octet coordinate body)
          (if (and (fn-srp-pull-coordinate-p coordinate body)
                   (fn-srp-pull-object-domain-p bits nbits octet)) 0 1)))
 (defthm fn-assume-srp-pull-object-octets-natural
  (natp (fn-assume-srp-pull-object-octets bits nbits octet coordinate body))
  :rule-classes :type-prescription)
 (defthm fn-assume-srp-pull-object-path-bound
  (implies (and (fn-srp-pull-coordinate-p coordinate body)
                (fn-srp-pull-object-domain-p bits nbits octet))
           (equal (fn-assume-srp-pull-object-octets
                    bits nbits octet coordinate body) 0))
  :rule-classes nil)
 ; Local countermodels only: unsupported-domain/coordinate behavior is not
 ; constrained to zero. These are not claims about the real allocator.
 (local
  (defthm fn-srp-pull-domain-removal-model-witness
   (and (fn-srp-pull-coordinate-p *fn-srp-selected-coordinate*
                                *fn-srp-selected-pull-body*)
        (not (fn-srp-pull-object-domain-p (expt 2 39) 0 0))
        (not (equal (fn-assume-srp-pull-object-octets
                      (expt 2 39) 0 0 *fn-srp-selected-coordinate*
                      *fn-srp-selected-pull-body*) 0)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-srp-pull-coordinate-p
                                      fn-srp-pull-object-domain-p)))))
 (local
  (defthm fn-srp-pull-coordinate-removal-model-witness
   (and (fn-srp-pull-object-domain-p 0 0 0)
        (not (fn-srp-pull-coordinate-p nil *fn-srp-selected-pull-body*))
        (not (equal (fn-assume-srp-pull-object-octets
                      0 0 0 nil *fn-srp-selected-pull-body*) 0)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-srp-pull-coordinate-p
                                      fn-srp-coordinate-p
                                      fn-srp-pull-object-domain-p))))))

(in-theory (disable fn-srp-pull-coordinate-p fn-srp-pull-object-domain-p))
