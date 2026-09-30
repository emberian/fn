; Actual emitter provenance and retained digit scratch. This is a logical
; source bound, not a selected-runtime tariff or profile admission authority.
(in-package "ACL2")
(include-book "operator-report-fields")
(local (include-book "arithmetic-5/top" :dir :system))
; Keep the width proof self-contained: the target toolchain has no certificate
; for ihs/logops-lemmas. These natural-only lemmas use the actual binary width.
(local (defun fn-orf-width-induct (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n)) (equal n 0)) (list n k)
    (fn-orf-width-induct (floor n 2) (+ -1 k)))))
(local (defthm fn-orf-width-power-bound
  (implies (natp n) (< n (expt 2 (integer-length n))))
  :hints (("Goal" :induct (integer-length n)
           :in-theory (enable integer-length expt)))))
(local (defthm fn-orf-width-from-power
  (implies (and (natp n) (natp k) (< n (expt 2 k)))
           (<= (integer-length n) k))
  :hints (("Goal" :induct (fn-orf-width-induct n k)
           :in-theory (enable integer-length expt)))))

(defun fn-orf-original-number (c)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-car (fn-orf-fields c)))))

(defun fn-orf-original-kind (c)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-car (fn-orf-fields c))))

; Ghost only: LEN(digits) is not evaluated on the served path. The borrowed
; current descriptor retains the original natural while NUMBER is divided.
(defun fn-orf-space-relationp (c)
  (declare (xargs :guard t))
  (and (fn-orf-invariant c)
       (case (fn-orf-phase c)
         (:idle (and (equal (fn-orf-number c) 0) (equal (fn-orf-digits c) nil)))
         (:field (and (equal (fn-orf-number c) 0) (equal (fn-orf-digits c) nil)
                      (equal (fn-orf-text c) "")))
         (:text (and (equal (fn-orf-original-kind c) :text)
                     (equal (fn-orf-text c) (fn-orf-original-number c))
                     (equal (fn-orf-number c) 0) (equal (fn-orf-digits c) nil)))
         (:prepare
          (and (equal (fn-orf-original-kind c) :nat)
               (natp (fn-orf-original-number c)) (equal (fn-orf-text c) "")
               (<= (fn-orf-number c) (fn-orf-original-number c))
               (<= (+ (len (fn-orf-digits c)) (max 1 (integer-length (fn-orf-number c))))
                   (+ 1 (integer-length (fn-orf-original-number c))))))
         (:emit
          (and (equal (fn-orf-original-kind c) :nat)
               (natp (fn-orf-original-number c)) (equal (fn-orf-text c) "")
               (equal (fn-orf-number c) 0)
               (<= (len (fn-orf-digits c))
                   (+ 1 (integer-length (fn-orf-original-number c))))))
         (otherwise nil))))

(local (defthm fn-orf-half-power
  (implies (integerp k) (equal (* 2 (expt 2 (+ -1 k))) (expt 2 k)))
  :hints (("Goal" :in-theory (enable expt)))))
(local (defthm fn-orf-half-power-linear
  (implies (integerp k) (<= (expt 2 k) (* 2 (expt 2 (+ -1 k)))))
  :rule-classes :linear
  :hints (("Goal" :use fn-orf-half-power :in-theory (disable fn-orf-half-power)))))
(defthm fn-orf-quotient-bit-progress
  (implies (and (natp n) (<= 10 n))
           (< (integer-length (floor n 10)) (integer-length n)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-orf-width-power-bound)
                 (:instance fn-orf-width-from-power (n (floor n 10))
                            (k (+ -1 (integer-length n)))))
           :in-theory (e/d () (integer-length fn-orf-width-power-bound fn-orf-width-from-power)))))

(local (defthm fn-orf-quotient-bit-progress-linear
  (implies (and (natp n) (<= 10 n))
           (< (integer-length (floor n 10)) (integer-length n)))
  :rule-classes :linear
  :hints (("Goal" :use fn-orf-quotient-bit-progress
           :in-theory (disable integer-length fn-orf-quotient-bit-progress)))))

(defthm fn-orf-space-start
  (implies (fn-orf-fieldsp fields)
           (fn-orf-space-relationp (fn-orf-start fields)))
  :hints (("Goal" :in-theory
           (enable fn-orf-space-relationp fn-orf-start fn-orf-next-field))))

(local (defthm fn-orf-natural-zero-width
  (implies (natp n) (equal (equal (integer-length n) 0) (equal n 0)))
  :hints (("Goal" :use fn-orf-width-power-bound
           :in-theory (disable integer-length fn-orf-width-power-bound)))))

(defthm fn-orf-space-step
  (implies (fn-orf-space-relationp c)
           (fn-orf-space-relationp (mv-nth 0 (fn-orf-step c))))
  :hints (("Goal" :use fn-orf-step-preserves-invariant
           :in-theory
           (e/d (fn-orf-space-relationp fn-orf-step fn-orf-original-number
                 fn-orf-original-kind fn-orf-invariant fn-orf-ready-p
                 fn-orf-fieldsp fn-orf-fieldp)
                (integer-length fn-orf-step-preserves-invariant)))))

; Projections of the carried source relation; these are not independent
; keystones and do not claim a supported-runtime operand domain.
(defthm fn-orf-digit-cells-bound-by-definition
  (implies (and (fn-orf-space-relationp c)
                (member-eq (fn-orf-phase c) '(:prepare :emit)))
           (<= (len (fn-orf-digits c))
               (+ 1 (integer-length (fn-orf-original-number c)))))
  :hints (("Goal" :in-theory (enable fn-orf-space-relationp))))

(defthm fn-orf-quotient-input-bound-by-definition
  (implies (and (fn-orf-space-relationp c)
                (equal (fn-orf-phase c) :prepare))
           (and (natp (fn-orf-original-number c))
                (<= (fn-orf-number c) (fn-orf-original-number c))))
  :hints (("Goal" :in-theory (enable fn-orf-space-relationp))))
