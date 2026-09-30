; A-SELECTED-RUNTIME-TABLE-OBJECTS: exact standalone TGET arithmetic/getter
; object path. Coordinate is a qualification requirement, not an attestation
; of actual inline callers, final candidate or full frames/cache/GC/lifetime.
(in-package "ACL2")
(include-book "assumptions-selected-runtime-primitives")

(defconst *fn-srp-selected-table-body*
 '("f44139b0130afd6ff0f081c8d58041d1618185128d5de5dbeb6f895aea9fb116"
   "44472fb1c9ed676a8132bc6d95a4814ab5b4444c282546fab59e043dc5b7f6bd"
   "268777e192696bd00ded68c72cf0d1e8b8b7b5afde5126bd113c0dac34249b41"
   "84045032be25dcb9aac1f0f9570194b9a729be66231182ba230377ebf2e50228"))

(defun fn-srp-table-coordinate-p (coordinate body)
 (declare (xargs :guard t))
 (and (fn-srp-coordinate-p coordinate)
      (equal body *fn-srp-selected-table-body*)))

(defun fn-srp-table-object-domain-p (entry low high table-length)
 (declare (xargs :guard t))
 (and (natp entry) (< entry 1747) (equal table-length 3494)
      (integerp low) (<= 0 low) (< low 256)
      (integerp high) (<= 0 high) (< high 256)))

; Reviewed standalone body: two fitting GENERIC-*2 sites, high-index ADD1,
; two direct UB8 getters, ASH8 and result ADD. Domain implies fitting fixnum
; inputs/intermediates/result and admitted physical table span. No result or
; workspace object allocation on these selected paths. The historical body
; diagnostic is COPY-only; the full coordinate remains a future qualification
; requirement. Never transfer that observation to an attached/inline caller.
(encapsulate
 (((fn-assume-srp-table-object-octets * * * * * *) => *))
 (local
  (defun fn-assume-srp-table-object-octets (entry low high table-length coordinate body)
   (if (and (fn-srp-table-coordinate-p coordinate body)
            (fn-srp-table-object-domain-p entry low high table-length)) 0 1)))
 (defthm fn-assume-srp-table-object-octets-natural
  (natp (fn-assume-srp-table-object-octets entry low high table-length coordinate body))
  :rule-classes :type-prescription)
 (defthm fn-assume-srp-table-object-path-bound
  (implies (and (fn-srp-table-coordinate-p coordinate body)
                (fn-srp-table-object-domain-p entry low high table-length))
           (equal (fn-assume-srp-table-object-octets
                    entry low high table-length coordinate body) 0))
  :rule-classes nil)
 ; Countermodels for the assumption's two premises, not real allocator tests.
 (local
  (defthm fn-srp-table-domain-removal-model-witness
   (and (fn-srp-table-coordinate-p *fn-srp-selected-coordinate* *fn-srp-selected-table-body*)
        (not (fn-srp-table-object-domain-p 1747 0 0 3494))
        (not (equal (fn-assume-srp-table-object-octets
                      1747 0 0 3494 *fn-srp-selected-coordinate* *fn-srp-selected-table-body*) 0)))
   :rule-classes nil))
 (local
  (defthm fn-srp-table-coordinate-removal-model-witness
   (and (fn-srp-table-object-domain-p 1746 255 255 3494)
        (not (fn-srp-table-coordinate-p nil *fn-srp-selected-table-body*))
        (not (equal (fn-assume-srp-table-object-octets
                      1746 255 255 3494 nil *fn-srp-selected-table-body*) 0)))
   :rule-classes nil)))
(in-theory (disable fn-srp-table-coordinate-p fn-srp-table-object-domain-p))
