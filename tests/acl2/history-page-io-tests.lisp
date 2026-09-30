(in-package "ACL2")
(include-book "../../books/history-page-io")
(assert-event
 (let ((p (fn-hpi-page 8 9 163840)))
  (and (equal (car p) :pwrite) (equal p '(:pwrite 147456 16384))
       (natp (nth 1 p)) (<= (fn-his-base-octets) (nth 1 p))
       (equal (nth 2 p) 16384)
       (<= (+ (nth 1 p) (nth 2 p)) (fn-his-region-octets 9))
       (<= (fn-his-region-octets 9) 163840))))
(assert-event
 (and (equal (car (fn-hpi-page 2 9 163840)) :pwrite)
      (equal (car (fn-hpi-page 3 9 163840)) :pwrite) (< 2 3)
      (<= (+ (nth 1 (fn-hpi-page 2 9 163840)) (nth 2 (fn-hpi-page 2 9 163840)))
          (nth 1 (fn-hpi-page 3 9 163840)))
      (equal (+ (nth 1 (fn-hpi-page 2 9 163840)) (nth 2 (fn-hpi-page 2 9 163840)))
             (nth 1 (fn-hpi-page 3 9 163840)))))
; Distinct-order hypothesis omission overlaps the actual same page.
(assert-event
 (and (equal (car (fn-hpi-page 2 9 163840)) :pwrite)
      (equal (car (fn-hpi-page 2 9 163840)) :pwrite) (not (< 2 2))
      (not (<= (+ (nth 1 (fn-hpi-page 2 9 163840)) (nth 2 (fn-hpi-page 2 9 163840)))
               (nth 1 (fn-hpi-page 2 9 163840))))))
; No byte of the following framed checkpoint region is addressable as a page.
(assert-event (equal (fn-hpi-page 9 9 163840) '(:refused :page)))
(assert-event (equal (fn-hpi-page 8 9 163839) '(:refused :extent)))
(assert-event (equal (fn-hpi-page 0 18446744073709551616 163840) '(:refused :domain)))
; Mutation: omitting the wrapper base writes into the previous physical page.
(assert-event
 (and (equal (car (fn-hpi-page 2 9 163840)) :pwrite)
      (not (equal (* 16384 2) (nth 1 (fn-hpi-page 2 9 163840))))))
