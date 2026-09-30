(in-package "ACL2")
(include-book "../../books/consumer-event-charge")

(defconst *cect-cursor* (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 2 3 4))
(defconst *cect-events*
  (list (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))
        (fn-cpe-make 1 1 1 '(:register (3) (4) (5) 1 2 3))
        (fn-cpe-make 2 2 2 (list :ack *cect-cursor*))
        (fn-cpe-make 3 3 3 '(:rebase (3) (4) (5) 1 2 4))
        (fn-cpe-make 4 4 4 '(:unregister (3) 4))
        (fn-cpe-make 5 5 5 '(:rollover (6)))))

(assert-event
 (and (fn-cpe-eventp (nth 0 *cect-events*))
      (equal (fn-cec-event-charge (nth 0 *cect-events*)) 22)
      (equal (fn-cec-event-charge (nth 0 *cect-events*))
             (len (fn-cpe-encode (nth 0 *cect-events*))))
      (fn-cpe-eventp (nth 1 *cect-events*))
      (equal (fn-cec-event-charge (nth 1 *cect-events*)) 36)
      (equal (fn-cec-event-charge (nth 1 *cect-events*))
             (len (fn-cpe-encode (nth 1 *cect-events*))))
      (fn-cpe-eventp (nth 2 *cect-events*))
      (equal (fn-cec-event-charge (nth 2 *cect-events*)) 49)
      (equal (fn-cec-event-charge (nth 2 *cect-events*))
             (len (fn-cpe-encode (nth 2 *cect-events*))))
      (fn-cpe-eventp (nth 3 *cect-events*))
      (equal (fn-cec-event-charge (nth 3 *cect-events*)) 36)
      (equal (fn-cec-event-charge (nth 3 *cect-events*))
             (len (fn-cpe-encode (nth 3 *cect-events*))))
      (fn-cpe-eventp (nth 4 *cect-events*))
      (equal (fn-cec-event-charge (nth 4 *cect-events*)) 24)
      (equal (fn-cec-event-charge (nth 4 *cect-events*))
             (len (fn-cpe-encode (nth 4 *cect-events*))))
      (fn-cpe-eventp (nth 5 *cect-events*))
      (equal (fn-cec-event-charge (nth 5 *cect-events*)) 20)
      (equal (fn-cec-event-charge (nth 5 *cect-events*))
             (len (fn-cpe-encode (nth 5 *cect-events*))))))

(assert-event
 (let* ((id (make-list 64 :initial-element 1))
        (cursor (fn-cp-cursor id id id id id 1 2 3 4))
        (event (fn-cpe-make 1 1 1 (list :ack cursor))))
   (and (fn-cpe-eventp event) (fn-cp-cursorp cursor)
        (equal (fn-cec-cursor-charge cursor) 346)
        (equal (fn-cec-event-charge event) 364)
        (equal (fn-cec-event-charge event) (len (fn-cpe-encode event))))))

; Remote/adoption kinds remain unavailable until their funded constructors
; and durable codec are implemented, rather than receiving a guessed charge.
(assert-event
 (and (not (fn-cpe-eventp (fn-cpe-make 1 1 1 '(:remote-register))))
      (equal (fn-cec-event-charge (fn-cpe-make 1 1 1 '(:remote-register))) 0)
      (equal (fn-cec-event-charge nil) (len (fn-cpe-encode nil)))))
