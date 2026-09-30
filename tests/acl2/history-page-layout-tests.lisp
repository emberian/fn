(in-package "ACL2")
(include-book "../../books/history-page-layout")

; Literal nonempty one- and multi-page directory allocation witnesses.
(assert-event
 (and (natp 4) (posp 1)
      (equal (pgs-alloc 4 1 '(nil 1))
             (list 1 (pgs-run (+ 1 1) 4) nil (+ 1 1 4)))))
(assert-event
 (and (natp 3) (posp 2)
      (equal (pgs-alloc 3 2 '(nil 1))
             (list 1 (pgs-run (+ 1 2) 3) nil (+ 1 2 3)))))

; Layout has actual data and table pages; its complete premise/conclusion.
(assert-event
 (let ((p (fn-hpl-layout 6)))
   (and (equal (car p) :layout)
        (equal p '(:layout 6 1 1 2 8 9))
        (equal (pgs-alloc (+ 6 (nth 2 p)) (nth 3 p) '(nil 1))
               (list 1 (pgs-run (nth 4 p) (+ 6 (nth 2 p))) nil (nth 6 p))))))
(assert-event
 (and (natp 2) (natp 4) (< 2 4) (posp 2)
      (equal (fn-hpl-single-address 2 2)
             (nth 2 (cadr (pgs-alloc 4 2 '(nil 1)))))))

; Each individual hypothesis removed, all retained hypotheses affirmed,
; omitted one false, literal conclusion false. Invalid guards are logical
; corrupted inputs, explicitly distinct from the reachable witnesses above.
(assert-event
 (with-guard-checking :none
  (and (not (natp -1)) (natp 4) (< -1 4) (posp 2)
       (not (equal (fn-hpl-single-address -1 2)
                   (nth -1 (cadr (pgs-alloc 4 2 '(nil 1)))))))))
(assert-event
 (with-guard-checking :none
  (and (natp 0) (not (natp 1/2)) (< 0 1/2) (posp 2)
       (not (equal (fn-hpl-single-address 0 2)
                   (nth 0 (cadr (pgs-alloc 1/2 2 '(nil 1)))))))))
(assert-event
 (and (natp 4) (natp 4) (not (< 4 4)) (posp 2)
      (not (equal (fn-hpl-single-address 4 2)
                  (nth 4 (cadr (pgs-alloc 4 2 '(nil 1))))))))
(assert-event
 (with-guard-checking :none
  (and (natp 0) (natp 4) (< 0 4) (not (posp 0))
       (not (equal (fn-hpl-single-address 0 0)
                   (nth 0 (cadr (pgs-alloc 4 0 '(nil 1)))))))))

; A layout refusal is checked before any allocation or address emission.
(assert-event (equal (fn-hpl-layout -1) '(:refused :out-of-range)))
(assert-event (equal (fn-hpl-layout 18446744073709551616)
                     '(:refused :out-of-range)))
; Mutation: omitting the reserved root/directory shifts a real data address.
(assert-event
 (and (natp 2) (natp 4) (< 2 4) (posp 2)
      (not (equal (+ 2 2) (nth 2 (cadr (pgs-alloc 4 2 '(nil 1))))))))
; Fresh-allocation theorem's two hypotheses each have literal counterexamples.
(assert-event
 (with-guard-checking :none
  (and (not (natp 1/2)) (posp 2)
       (not (equal (pgs-alloc 1/2 2 '(nil 1))
                   (list 1 (pgs-run (+ 1 2) 1/2) nil (+ 1 2 1/2)))))))
(assert-event
 (and (natp 4) (not (posp 0))
      (not (equal (pgs-alloc 4 0 '(nil 1))
                  (list 1 (pgs-run (+ 1 0) 4) nil (+ 1 0 4))))))
; Refused layout does not carry the accepted allocation theorem.
(assert-event
 (with-guard-checking :none
  (let ((p (fn-hpl-layout -1)))
   (and (not (equal (car p) :layout))
        (not (equal (pgs-alloc (+ -1 (nth 2 p)) (nth 3 p) '(nil 1))
                    (list 1 (pgs-run (nth 4 p) (+ -1 (nth 2 p)))
                          nil (nth 6 p))))))))
