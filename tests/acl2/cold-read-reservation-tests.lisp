(in-package "ACL2")
(include-book "../../books/cold-read-reservation")
(include-book "std/testing/assert-bang" :dir :system)

(assert-event
 (and (eq (symbol-class 'fn-crv-extend-reservation (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-crv-pool-budget (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-crv-native-baseline (w state)) :common-lisp-compliant)))

(defconst *crvt-base* '(:heap 512 :development 4096 1024 12))
(defconst *crvt-policy* '(67108864 2 16 10000 10000))
(defconst *crvt-core* 268435456)
(defconst *crvt-machine* '(4294967296))
(defconst *crvt-result*
  (fn-crv-extend-reservation *crvt-base* *crvt-policy* *crvt-core* *crvt-machine*))
(assert! (equal *crvt-result* '(:heap 576 :development 4096 1024 14)))
; Complete literal positive for observed machine and dynamic allowance.
(assert!
 (and (fn-crv-policy-p *crvt-policy*)
      (equal (fn-crv-nth 0 *crvt-result*) :heap)
      (<= (fn-heap-reservation-octets (fn-crv-nth 1 *crvt-result*) *crvt-core*
                                      (fn-crv-nth 4 *crvt-result*) (fn-crv-nth 5 *crvt-result*))
          (fn-heap-machine-octets *crvt-machine*))
      (<= (+ (* *fn-heap-mib* (nfix (fn-crv-nth 1 *crvt-base*)))
             (nfix (fn-crv-nth 0 *crvt-policy*)))
          (* *fn-heap-mib* (nfix (fn-crv-nth 1 *crvt-result*))))))
(assert! (equal (fn-crv-native-baseline *crvt-policy* nil) 10485760))
(assert! (equal (fn-crv-pool-budget *crvt-policy* nil) '(77594624 0 16 2 10000)))
; Remove accepted result: valid policy retained, returned refusal and its
; proposed reservation exceeds the new machine. Not a live claim from it.
(assert!
 (let* ((machine '(134217728))
        (d (fn-crv-extend-reservation *crvt-base* *crvt-policy* *crvt-core* machine)))
   (and (fn-crv-policy-p *crvt-policy*) (not (equal (fn-crv-nth 0 d) :heap))
        (not (<= (fn-heap-reservation-octets (fn-crv-nth 1 d) *crvt-core*
                                             (fn-crv-nth 4 d) (fn-crv-nth 5 d))
                 (fn-heap-machine-octets machine))))))
; Policy hypothesis removal, deliberately corrupted supplied base: absent
; policy bypasses the extension. Accepted result retained, old base is over
; the machine. Actual launch composition always validates base separately.
(assert!
 (let* ((machine '(536870912))
        (d (fn-crv-extend-reservation *crvt-base* nil *crvt-core* machine)))
   (and (not (fn-crv-policy-p nil)) (equal (fn-crv-nth 0 d) :heap)
        (not (<= (fn-heap-reservation-octets (fn-crv-nth 1 d) *crvt-core*
                                             (fn-crv-nth 4 d) (fn-crv-nth 5 d))
                 (fn-heap-machine-octets machine))))))
; Unchanged absent policy; partial explicit policy is not silently ignored.
(assert! (equal (fn-crv-extend-reservation *crvt-base* nil *crvt-core* *crvt-machine*) *crvt-base*))
(assert! (equal (fn-crv-nth 1 (fn-crv-extend-reservation *crvt-base* '(1 2 3 4)
                                                       *crvt-core* *crvt-machine*))
                 :invalid-cold-resource-profile))

; Dynamic allowance keystone has only accepted-result as hypothesis. Its
; omitted hypothesis fails on the valid policy refusal, and its conclusion
; fails affirmatively under the guard-safe numerical projections.
(assert!
 (let* ((d (fn-crv-extend-reservation *crvt-base* *crvt-policy* *crvt-core* '(134217728))))
   (and (not (equal (fn-crv-nth 0 d) :heap))
        (not (<= (+ (* *fn-heap-mib* (nfix (fn-crv-nth 1 *crvt-base*)))
                    (nfix (fn-crv-nth 0 *crvt-policy*)))
                 (* *fn-heap-mib* (nfix (fn-crv-nth 1 d))))))))
