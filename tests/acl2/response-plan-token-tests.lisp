(in-package "ACL2")
(include-book "../../books/response-plan-token")

(defun rptt-conclusion (id owners st)
  (mv-let (next-owners next-st status) (fn-rpin-step owners st (list :acquire id))
    (declare (ignore status))
    (and (equal (fn-rpin-token id next-owners) (list :response id (car st)))
         (fn-rpin-tokenp (fn-rpin-token id next-owners))
         (< 0 (fn-arpn-pins-of (car st) (second next-st))))))

; @teeth fn-rpin-token-after-acquire-is-captured-generation positive
(assert-event
 (let ((id 2) (owners '((1 . 7))) (st '(7 ((7 . 1)) nil)))
   (and (fn-arpn-okp st) (natp id) (not (fn-rpin-owner id owners))
        (rptt-conclusion id owners st))))

; @teeth fn-rpin-token-after-acquire-is-captured-generation hypothesis-removal natp
(assert-event
 (let ((id -1) (owners '((1 . 7))) (st '(7 ((7 . 1)) nil)))
   (and (fn-arpn-okp st) (not (natp id)) (not (fn-rpin-owner id owners))
        (not (rptt-conclusion id owners st)))))

; @teeth fn-rpin-token-after-acquire-is-captured-generation hypothesis-removal owner-absent
(assert-event
 (let ((id 2) (owners '((2 . 3))) (st '(7 ((3 . 1)) nil)))
   (and (fn-arpn-okp st) (natp id) (fn-rpin-owner id owners)
        (not (rptt-conclusion id owners st)))))

; Logical corrupted-state witness intentionally violates the entry guard.
(set-guard-checking :none)
; @teeth fn-rpin-token-after-acquire-is-captured-generation corrupted-state
(assert-event
 (let ((id 2) (owners nil) (st '(7 ((7 . -4)) nil)))
   (and (not (fn-arpn-okp st)) (natp id) (not (fn-rpin-owner id owners))
        (not (rptt-conclusion id owners st)))))

(set-guard-checking t)

; @teeth fn-rpin-token-after-acquire-is-captured-generation mutation
(assert-event
 (let ((owners '((1 . 7))) (st '(7 ((7 . 1)) nil)) (view 31))
   (mv-let (next-owners next-st status) (fn-rpin-step owners st '(:acquire 2))
     (declare (ignore next-st status))
     (and (fn-arpn-okp st) (natp 2) (not (fn-rpin-owner 2 owners))
          (rptt-conclusion 2 owners st)
          (not (equal (fn-rpin-token 2 next-owners) (list :response 2 view)))))))
