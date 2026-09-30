; Scalar actual-charge admission for one consumer publication. No query,
; credential or shared Store tree is traversed. The profile/carry adapter
; supplies these established coordinates before frontier allocation.
(in-package "ACL2")

(defun fn-cpc-admissiblep (txmax hmax rmax reserve used bytes debt charge)
  (declare (xargs :guard t))
  (and (natp txmax) (natp hmax) (natp rmax) (natp reserve)
       (natp used) (natp bytes) (natp debt) (posp charge)
       (<= reserve rmax) (<= charge rmax)
       (< (+ used 1 debt) txmax)
       (<= (+ bytes charge (* (+ 1 debt) reserve)) hmax)))

; The maintained resource vector after one publication still funds every
; open release plus the one maintenance release. This is a resource
; theorem, not a claim about txid uniqueness or guaranteed rescue execution.
(defthm fn-cpc-publication-retains-release-vector
  (implies (fn-cpc-admissiblep txmax hmax rmax reserve used bytes debt charge)
           (and (natp (+ used 1)) (natp (+ bytes charge))
                (<= (+ used 1 debt 1) txmax)
                (<= (+ bytes charge (* (+ 1 debt) reserve)) hmax)
                (<= charge rmax) (<= reserve rmax)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cpc-admissiblep))))

(in-theory (disable fn-cpc-admissiblep))
