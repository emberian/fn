; A-SELECTED-RUNTIME-CONSTRUCTOR-OBJECTS. Primary object requests only.
; The exact caller/XEP, allocation trampoline, TLS/cache/first-use/fault and
; retained capacity/GC envelope remain separate. No whole-job adequacy.
(in-package "ACL2")
(include-book "assumptions-selected-runtime-primitives")

; Each immutable event is inspected in the attachment-first measurement packet
; ff87bea8e/5379ad738. Source EVENT hashes are not runtime attestations.
(defun fn-sroc-object-row (subject)
 (declare (xargs :guard t))
 (case subject
  (:pool-three
   '("225965373be2a0c40a4339a8f9a4305f86b6d6e21d5152ffd22441cecebdb59a" 48))
  (:rx-foundation
   '("3fbd390317fe7c3527add9c3d831ec967e8dccd3247142f2fa37fa29423697c4" 48))
  (:native-job-twenty
   '("4f16dd6cecd8eeee5447df11db8c6a7a388ddb187e7655e6ad6945f344d12f74" 176))
  (:input-copy-ten
   '("d2eb01cd26877ceca1ffa053dc74742e20124973f97a3fbbec72dbc249a4d62a" 96))
  (:digest-sixteen-with-frames
   '("50b0feff7c2e3f7066a133ce595851548d9a9d82ddb5e04988019db2f73f9d7b" 672))
  (:extent-direct-16384
   '("eae13a6fc155c9819ce5cb46299312d40f82d4a106122c0d701f62f4ce06cf69" 16400))
  (otherwise nil)))
(defun fn-sroc-object-coordinate-p (subject source-coordinate coordinate)
 (declare (xargs :guard t))
 (let ((row (fn-sroc-object-row subject)))
  (and (consp row) (equal source-coordinate (car row))
       (fn-srp-coordinate-p coordinate))))
(defun fn-sroc-object-request (subject)
 (declare (xargs :guard t))
 (let ((row (fn-sroc-object-row subject)))
  (if (consp row) (cadr row) 0)))

; The opaque subject measures PRIMARY OBJECTS allocated by the exact body,
; not bytes-consed batches, all transitive allocation or physical high-water.
; A zero local witness establishes consistency, not a physical claim.
(encapsulate
 (((fn-assume-sroc-primary-object-octets * * *) => *))
 (local
  (defun fn-assume-sroc-primary-object-octets (subject source-coordinate coordinate)
   (declare (ignore subject source-coordinate coordinate)) 0))
 (defthm fn-assume-sroc-primary-object-octets-natural
  (natp (fn-assume-sroc-primary-object-octets subject source-coordinate coordinate))
  :rule-classes :type-prescription)
 (defthm fn-assume-sroc-primary-object-request-bound
  (implies (fn-sroc-object-coordinate-p subject source-coordinate coordinate)
   (<= (fn-assume-sroc-primary-object-octets subject source-coordinate coordinate)
       (fn-sroc-object-request subject)))
  :hints (("Goal" :in-theory (enable fn-sroc-object-coordinate-p
                                    fn-sroc-object-row fn-sroc-object-request)))
  :rule-classes nil))

; Admission code can decide absence/mismatch before constructor allocation.
; This status only selects an object row; it does not make the caller READY.
(defun fn-sroc-object-row-status (subject source-coordinate coordinate)
 (declare (xargs :guard t))
 (if (fn-sroc-object-coordinate-p subject source-coordinate coordinate)
     :object-row :unavailable))
