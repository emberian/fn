; Nonempty actual-charge and live-debt witnesses for the scalar boundary.
(in-package "ACL2")
(include-book "../../books/consumer-publication-charge")

; Complete antecedent and conclusion of the resource-vector theorem.
(assert-event
 (and (fn-cpc-admissiblep 100 16384 4096 4096 10 1000 1 1024)
      (natp (+ 10 1)) (natp (+ 1000 1024))
      (<= (+ 10 1 1 1) 100)
      (<= (+ 1000 1024 (* (+ 1 1) 4096)) 16384)
      (<= 1024 4096) (<= 4096 4096)))

; 512 would fit, the actual1024 event cannot. Every other gate predicate
; holds; the actual history-plus-release inequality is affirmatively false.
(assert-event
 (and (fn-cpc-admissiblep 100 16384 4096 4096 10 11776 0 512)
      (natp 100) (natp 16384) (natp 4096) (natp 4096)
      (natp 10) (natp 11776) (natp 0) (posp 1024)
      (<= 4096 4096) (<= 1024 4096) (< (+ 10 1 0) 100)
      (not (<= (+ 11776 1024 (* (+ 1 0) 4096)) 16384))
      (not (fn-cpc-admissiblep 100 16384 4096 4096 10 11776 0 1024))))

; Event fits H on its own but the promised releases would not.
(assert-event
 (and (<= (+ 12000 1024) 16384)
      (not (<= (+ 12000 1024 (* (+ 1 1) 4096)) 16384))
      (not (fn-cpc-admissiblep 100 16384 4096 4096 10 12000 1 1024))))

; History has room but there is no transaction for the maintenance release.
(assert-event
 (and (<= (+ 1000 1024 (* (+ 1 1) 4096)) 16384)
      (not (<= (+ 98 1 1 1) 100))
      (not (fn-cpc-admissiblep 100 16384 4096 4096 98 1000 1 1024))))

(assert-event
 (and (not (fn-cpc-admissiblep 100 16384 4096 4096 10 1000 0 4097))
      (not (fn-cpc-admissiblep 100 16384 4096 4096 10 1000 0 0))
      (not (fn-cpc-admissiblep 100 16384 4096 4096 -1 1000 0 1024))))
