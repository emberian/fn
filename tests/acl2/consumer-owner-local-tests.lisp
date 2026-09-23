; Actual local-owner proposal subject, with committed Store witnesses.
(in-package "ACL2")
(include-book "../../books/consumer-owner-local")

(defun colt-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun colt-commit (s event)
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare-consumer (colt-reserve s) event)
               :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))

(defconst *colt-boot*
  (colt-commit (fn-sn-initial '("fn.test") 16)
               (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))))
(defconst *colt-o0* (fn-own-start *colt-boot* 2))
(defconst *colt-id* '(7))
(defconst *colt-group* '(102 110 46 116 101 115 116)) ; fn.test
(defconst *colt-register*
  (fn-col-register *colt-o0* *colt-id* *colt-group*))
(assert-event (eq (car *colt-register*) :write))
(assert-event (equal (fn-cpe-operation (cadr *colt-register*))
                     (list :register *colt-id* *fn-col-principal*
                           *colt-group* 1 0 1)))
(assert-event (equal (fn-col-position *colt-o0* *colt-id*)
                     '(:refused :scope)))
(assert-event (equal (fn-col-register *colt-o0* *colt-id* '(1 2 3))
                     '(:refused :query)))

(defconst *colt-s1* (colt-commit *colt-boot* (cadr *colt-register*)))
(defconst *colt-o1* (fn-own-start *colt-s1* 2))
(defconst *colt-position* (fn-col-position *colt-o1* *colt-id*))
(assert-event (eq (car *colt-position*) :position))
(assert-event (equal (fn-col-register *colt-o1* *colt-id* *colt-group*)
                     (list :no-op
                           (fn-cp-scope-cursor
                            (fn-sn-consumer *colt-s1*)
                            (fn-cp-find *colt-id*
                                        (fn-cp-nth 5 (fn-sn-consumer *colt-s1*)))))))

; A public cursor remains a declaration, not evidence that a poll or
; application transaction happened.  The local authenticated principal is
; pinned by this owner profile, so a changed principal cannot move progress.
(defconst *colt-cursor*
  (fn-cp-cursor '(1) '(2) *colt-id* *fn-col-principal*
                *colt-group* 1 0 1 2))
(defconst *colt-ack* (fn-col-ack *colt-o1* (fn-cp-cursor-encode *colt-cursor*)))
(assert-event (eq (car *colt-ack*) :write))
(assert-event (equal (fn-cpe-operation (cadr *colt-ack*))
                     (list :ack *colt-cursor*)))
(assert-event
 (equal (fn-col-ack
         *colt-o1*
         (fn-cp-cursor-encode
          (fn-cp-cursor '(1) '(2) *colt-id* '(88) *colt-group* 1 0 1 2)))
        '(:refused :scope)))
(assert-event
 (equal (fn-col-ack
         *colt-o1*
         (fn-cp-cursor-encode
          (fn-cp-cursor '(1) '(2) *colt-id* *fn-col-principal*
                        *colt-group* 1 0 1 3)))
        '(:refused :future)))

(defconst *colt-s2* (colt-commit *colt-s1* (cadr *colt-ack*)))
(defconst *colt-o2* (fn-own-start *colt-s2* 2))
(assert-event (eq (car (fn-col-ack *colt-o2*
                                     (fn-cp-cursor-encode *colt-cursor*)))
                  :no-op))
(assert-event
 (equal (fn-cp-nth 9
                   (fn-cp-nth 1
                    (fn-cp-cursor-decode
                     (cadr (fn-col-position *colt-o2* *colt-id*)))))
        2))
