(in-package "ACL2")
(include-book "../../books/output-reservation")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *orvt-base* '(:heap 512 :development 4096 1024 12))
(defconst *orvt-policy* '(16777216 1048576))
(defconst *orvt-core* 268435456)
(defconst *orvt-machine* '(4294967296))
(defconst *orvt-result*
  (fn-orv-extend-reservation *orvt-base* *orvt-policy* *orvt-core* *orvt-machine*))
(assert! (equal *orvt-result* '(:heap 528 :development 4096 1024 12)))
(assert-event
 (and (eq (symbol-class 'fn-orv-extend-reservation (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-orv-startup-grant (w state)) :common-lisp-compliant)))

; Literal positive, with every retained hypothesis and full conclusion.
(assert!
 (and (fn-orv-policy-p *orvt-policy*)
      (equal (fn-crv-nth 0 *orvt-result*) :heap)
      (<= (fn-heap-reservation-octets (fn-crv-nth 1 *orvt-result*) *orvt-core*
                                      (fn-crv-nth 4 *orvt-result*) (fn-crv-nth 5 *orvt-result*))
          (fn-heap-machine-octets *orvt-machine*))))
; Accepted-result hypothesis removed: real refusal, full conclusion false.
(assert!
 (let* ((machine '(134217728))
        (d (fn-orv-extend-reservation *orvt-base* *orvt-policy* *orvt-core* machine)))
   (and (fn-orv-policy-p *orvt-policy*) (not (equal (fn-crv-nth 0 d) :heap))
        (not (<= (fn-heap-reservation-octets (fn-crv-nth 1 d) *orvt-core*
                                             (fn-crv-nth 4 d) (fn-crv-nth 5 d))
                 (fn-heap-machine-octets machine))))))
; Policy removal, deliberately corrupted parent supplied to the absent-policy
; bypass. Actual launcher validates its parent before invoking the extension.
(assert!
 (let* ((machine '(536870912))
        (d (fn-orv-extend-reservation *orvt-base* nil *orvt-core* machine)))
   (and (not (fn-orv-policy-p nil)) (equal (fn-crv-nth 0 d) :heap)
        (not (<= (fn-heap-reservation-octets (fn-crv-nth 1 d) *orvt-core*
                                             (fn-crv-nth 4 d) (fn-crv-nth 5 d))
                 (fn-heap-machine-octets machine))))))

(assert!
 (and (equal (fn-crv-nth 0 *orvt-result*) :heap)
      (<= (+ (* *fn-heap-mib* (nfix (fn-crv-nth 1 *orvt-base*)))
             (nfix (fn-crv-nth 0 *orvt-policy*)))
          (* *fn-heap-mib* (nfix (fn-crv-nth 1 *orvt-result*))))))
(assert!
 (let ((d (fn-orv-extend-reservation *orvt-base* *orvt-policy* *orvt-core* '(134217728))))
   (and (not (equal (fn-crv-nth 0 d) :heap))
        (not (<= (+ (* *fn-heap-mib* (nfix (fn-crv-nth 1 *orvt-base*)))
                    (nfix (fn-crv-nth 0 *orvt-policy*)))
                 (* *fn-heap-mib* (nfix (fn-crv-nth 1 d))))))))

; Cold pool and output are both present: no output grant from cold bytes.
(defconst *orvt-cold* '(67108864 2 16 10000 10000))
(assert!
 (let ((d (fn-orv-startup-grant 637534208 536870912 *orvt-cold* *orvt-policy* 34)))
   (and (equal (car d) :hold)
        (<= (+ 536870912 (nfix (fn-crv-nth 0 *orvt-cold*)) (fn-crv-nth 0 *orvt-policy*)) 637534208)
        (<= (+ (fn-orv-bookkeeping-octets 34) (* 2 (fn-crv-nth 1 *orvt-policy*)))
            (fn-crv-nth 0 *orvt-policy*))
        (equal d '(:hold 16777216 1048576 17440 34)))))
(assert!
 (let ((d (fn-orv-startup-grant 536870912 536870912 *orvt-cold* *orvt-policy* 34)))
   (and (not (equal (car d) :hold))
        (not (and (<= (+ 536870912 (nfix (fn-crv-nth 0 *orvt-cold*)) (fn-crv-nth 0 *orvt-policy*)) 536870912)
                  (<= (+ (fn-orv-bookkeeping-octets 34) (* 2 (fn-crv-nth 1 *orvt-policy*)))
                      (fn-crv-nth 0 *orvt-policy*))))
        (equal d '(:refused :output-pool-not-held)))))
(assert! (equal (fn-orv-startup-grant 637534208 536870912 nil '(2097152 1048576) 34)
                '(:refused :minimum-output-quantum-unaffordable)))
(assert! (equal (fn-orv-startup-grant 637534208 536870912 nil nil 34)
                '(:partial :output-resources-unconfigured)))
(assert! (equal (fn-orv-startup-grant 637534208 536870912 nil *orvt-policy* (expt 2 32))
                '(:refused :invalid-output-resource-profile)))
(assert! (equal (fn-orv-extend-reservation *orvt-base* nil *orvt-core* *orvt-machine*) *orvt-base*))
(assert! (equal (fn-crv-nth 1 (fn-orv-extend-reservation *orvt-base* '(1) *orvt-core* *orvt-machine*))
                :invalid-output-resource-profile))

; Real external grammar recognizes both fields, refuses a partial pair or
; unrepresentable number, and does not claim the unsupported tariff frontier.
(assert! (equal (fn-ncfg-output-resources
                 '(("resources" "output_heap_octets" (:nat 16777216))
                   ("resources" "output_quantum_heap_octets" (:nat 1048576))))
                *orvt-policy*))
(assert! (equal (fn-ncfg-output-resources '(("resources" "output_heap_octets" (:nat 16777216)))) :bad))
(assert! (equal (fn-ncfg-output-resources
                 (list (list "resources" "output_heap_octets" (list :nat (expt 2 64)))
                       (list "resources" "output_quantum_heap_octets" '(:nat 1048576)))) :bad))
