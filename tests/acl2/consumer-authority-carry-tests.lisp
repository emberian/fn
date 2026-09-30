; CP7 raw authority carry: no served authentication or durable adoption claim.
(in-package "ACL2")
(include-book "../../books/consumer-store-projection")
(include-book "../../books/consumer-remote-position")

(defconst *cact-authority*
  '(:authority 9 4 (9) ((:account (97) 1 t (7 8))
                       (:account (98) 3 nil nil)) nil))
(defconst *cact-state*
  (fn-cp-state-carry '(1) '(2) 10 1 nil *cact-authority*))
(defconst *cact-register*
  (fn-cp-remote-register *cact-state* 10 '(3) '(4) '(5) 1 9
                          '((102 110 46 97) (102 110 46 98)) '(1)))
(defconst *cact-registered*
  (fn-cp-apply *cact-state* (cadr *cact-register*)))
(defconst *cact-cursor*
  (fn-cp-cursor '(1) '(2) '(4) '(3) '(5) 1 9 1 7))

; Nonempty adopted account plus a deletion tombstone, all recognizer facts.
(assert-event
 (and (fn-cp-authorityp *cact-authority*)
      (fn-cp-statep *cact-state*)
      (equal (len *cact-state*) 7)
      (equal (car *cact-register*) :write)
      (equal (fn-cp-nth 6 *cact-registered*) *cact-authority*)
      (fn-cp-statep *cact-registered*)))

(assert-event
 (let ((ack (fn-cp-ack *cact-registered* '(3) 1 9 *cact-cursor*)))
   (and (eq (car ack) :write)
        (equal (fn-cp-nth 6 (fn-cp-apply *cact-registered* (cadr ack)))
               *cact-authority*)
        (equal (fn-cp-nth 8
                          (fn-cp-find '(4) (fn-cp-nth 5
                           (fn-cp-apply *cact-registered* (cadr ack)))))
               '((102 110 46 97) (102 110 46 98))))))

; Ordinary append-frontier advancement cannot manufacture a view revision.
(assert-event
 (and (equal (fn-cp-nth 6 (fn-cpe-projection-advance *cact-registered* 11))
             *cact-authority*)
      (equal (fn-cp-nth 1 (fn-cp-nth 6
                           (fn-cpe-projection-advance *cact-registered* 11))) 9)))

; Old/missing authority schema is rejected, never supplied a default.
(assert-event
 (and (not (fn-cp-statep '(:consumer-state (1) (2) 10 1 nil)))
      (not (fn-cp-statep '(:consumer-state (1) (2) 10 1 nil nil)))
      (not (fn-cp-authorityp '(:authority 9 3 (9) ((:account (98) 3 nil nil)) nil)))
      (not (fn-cp-authorityp '(:authority 9 4 (9) ((:account (97) 1 nil (7))) nil)))))

; A staged candidate is not adopted authority. Its provisional account and
; fresh identity do not replace the admitted table before an atomic fence.
(defconst *cact-pending*
  (list :adoption '(10) 9 1 5 '((:account (99) 4 t (11)))
        '(99) (make-list 32 :initial-element 0) nil))
(defconst *cact-staged-authority*
  (list :authority 9 4 '(9) (fn-cp-nth 4 *cact-authority*) *cact-pending*))
(assert-event
 (and (fn-cp-adoptionp *cact-pending*)
      (fn-cp-authorityp *cact-staged-authority*)
      (equal (fn-cp-authority-find '(97) (fn-cp-nth 4 *cact-staged-authority*))
             '(:account (97) 1 t (7 8)))
      (not (fn-cp-authority-find '(99) (fn-cp-nth 4 *cact-staged-authority*)))
      (not (fn-cp-authorityp
            (list :authority 10 4 '(9) (fn-cp-nth 4 *cact-authority*)
                  *cact-pending*)))))
