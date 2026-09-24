; The actual poll's bounded index window uses exact journal objects.
(in-package "ACL2")
(include-book "../../books/consumer-poll-index")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cpit-events*
  (list (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))
        (fn-cpe-make 1 1 1 '(:register (3) (4) (5) 1 1 1))
        (fn-cpe-make 2 2 2
                     (list :ack (fn-cp-cursor '(1) '(2) '(3) '(4) '(5)
                                               1 1 1 2)))))
(defconst *cpit-index* (fn-cei-build *cpit-events*))

(assert-event (fn-cei-correspondencep *cpit-index* *cpit-events*))
(assert-event
 (equal (fn-col-poll-index-window *cpit-index* 1 3 16)
        (cdr *cpit-events*)))
(assert-event
 (equal (fn-col-poll-scan
         (fn-col-poll-index-window *cpit-index* 1 3 16)
         '(4) 1 3 16)
        '(:scan 3 nil)))
(assert-event (null (fn-col-poll-index-window *cpit-index* 3 3 16)))

; Omitting the correspondence premise permits an indexed substitution.
(must-fail
 (assert-event
  (equal (fn-col-poll-index-window nil 1 3 2)
         (fn-col-poll-list-window *cpit-events* 1 3 2))))
