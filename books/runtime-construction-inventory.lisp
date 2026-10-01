; Image-construction observations, not an operation allowance.  The native
; constructor enumerates its owned objects and supplies shallow runtime sizes.
; This arithmetic does not prove that the ownership recipe is complete, or
; identify the process RSS with these objects.  Shared image/runtime storage
; and a future constructor's reserved storage are separate named coordinates.
(in-package "ACL2")

(defun fn-rci-sum (sizes total limit)
  (declare (xargs :guard (and (natp total) (natp limit))))
  (cond ((> total limit) nil)
        ((atom sizes) (if (null sizes) total nil))
        ((not (and (natp (car sizes))
                   (<= (car sizes) (- limit total)))) nil)
        (t (fn-rci-sum (cdr sizes) (+ total (car sizes)) limit))))

(defthm fn-rci-sum-bounded
  (implies (and (natp total) (natp limit)
                (fn-rci-sum sizes total limit))
           (and (natp (fn-rci-sum sizes total limit))
                (<= total (fn-rci-sum sizes total limit))
                (<= (fn-rci-sum sizes total limit) limit)))
  :rule-classes nil)

; All successful intermediate sums fit LIMIT.  Only the constructor reserve
; is allowed to describe not-yet-created heap objects.  The collector-copy
; convention is the existing originalPRS one: twice heap, once native.
(defun fn-runtime-construction-inventory
    (sizes constructor-primary native-octets limit)
  (declare (xargs :guard t
    :guard-hints (("Goal" :in-theory (disable fn-rci-sum)
      :use ((:instance fn-rci-sum-bounded (total 0)))))))
  (if (not (and (natp constructor-primary) (natp native-octets)
                (posp limit) (<= native-octets limit)))
      '(:inventory-unavailable)
    (let ((primary (fn-rci-sum sizes 0 limit)))
      (if (not (and primary
                    (<= constructor-primary (- limit primary))))
          '(:inventory-unavailable)
        (let ((reserved (+ primary constructor-primary)))
          (if (> reserved (- (- limit native-octets) reserved))
              '(:inventory-unavailable)
            (list :inventory-observed primary constructor-primary
                  native-octets (+ (* 2 reserved) native-octets))))))))


(defthm fn-runtime-construction-inventory-bounds-resident
  (implies (equal (car (fn-runtime-construction-inventory
                        sizes constructor-primary native-octets limit))
                  :inventory-observed)
           (let ((answer (fn-runtime-construction-inventory
                           sizes constructor-primary native-octets limit)))
             (and (natp (nth 1 answer))
                  (natp (nth 4 answer))
                  (equal (nth 4 answer)
                         (+ (* 2 (+ (nth 1 answer) constructor-primary))
                            native-octets))
                  (<= (nth 4 answer) limit))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-rci-sum)
           :use ((:instance fn-rci-sum-bounded (total 0))))))
