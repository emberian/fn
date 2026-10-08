(in-package "ACL2")
(include-book "../../books/store-log-pipeline-profile")
(include-book "must-fail-checked")
(defconst *gcqp-ks*
  (fn-lgk-make nil (make-list 32 :initial-element 0) 0 2 '((65)) nil 0 :ready))
(defconst *gcqp-p* (fn-lgk-pipe-make *gcqp-ks* nil))
; Every hypothesis of queue-room-prevents-full, and its conclusion.
(assert-event
 (and (not (fn-lgk-pipe-behind *gcqp-p*))
      (fn-olr-gc-queue-roomp *gcqp-ks* 128 2 2048 512)
      (consp (fn-lgk-batch *gcqp-ks*)) (<= (len '(66)) 128)
      (natp 2) (equal 2 (fn-lgk-next-txid *gcqp-ks*))
      (not (equal (fn-lgk-phase *gcqp-ks*) :fault))
      (fn-olr-gc-profile-fitp *gcqp-ks* '(66) 2 2048 512)
      (equal (car (fn-lgk-pipe-take *gcqp-p* '(66) 2 1 5 2 2048 512)) :taken)))
; Both a record-count and an encoded-octet boundary stop before dequeue.
(assert-event
 (and (not (fn-olr-gc-queue-roomp *gcqp-ks* 128 1 2048 512))
      (not (fn-olr-gc-queue-roomp *gcqp-ks* 128 2 512 512))))
; Removing the profile-sized-record premise produces a real :full.
(defconst *gcqp-large* (make-list 2048 :initial-element 66))
(assert-event
 (and (fn-olr-gc-queue-roomp *gcqp-ks* 128 2 2048 512)
      (> (len *gcqp-large*) 128)
      (equal (car (fn-lgk-pipe-take *gcqp-p* *gcqp-large* 2 1 5 2 2048 512)) :full)))
(must-fail-checked
 (assert-event
  (equal (car (fn-lgk-pipe-take *gcqp-p* *gcqp-large* 2 1 5 2 2048 512)) :taken)))
; Empty batch can dequeue a candidate, but its exact fit still precedes
; publication. No singleton exemption in the actual profile-fit predicate.
(assert-event
 (let ((ks (fn-lgk-make nil (make-list 32 :initial-element 0) 0 1 nil nil 0 :ready)))
  (and (fn-olr-gc-queue-roomp ks 128 2 1 512)
       (not (fn-olr-gc-profile-fitp ks '(65) 2 1 512)))))
(value-triple :queue-preflight-positive-and-removal-passed)
