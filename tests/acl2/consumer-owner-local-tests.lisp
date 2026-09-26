; Actual local-owner proposal subject, with committed Store witnesses.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
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
(defconst *colt-new-owner*
  (fn-own-start (fn-sn-initial '("fn.test") 16) 2))
(defconst *colt-history-id* (make-list 32 :initial-element 11))
(defconst *colt-incarnation-id* (make-list 32 :initial-element 12))
(defconst *colt-bootstrap-proposal*
  (fn-col-bootstrap *colt-new-owner*
                    *colt-history-id* *colt-incarnation-id*))
(assert-event (eq (car *colt-bootstrap-proposal*) :write))
(assert-event
 (equal (fn-cpe-operation (cadr *colt-bootstrap-proposal*))
        (list :bootstrap *colt-history-id* *colt-incarnation-id*)))
(assert-event
 (equal (fn-col-bootstrap *colt-new-owner*
                          *colt-history-id* *colt-history-id*)
        '(:refused :identity)))
(assert-event
 (equal (fn-col-bootstrap (fn-own-start *colt-boot* 2)
                          *colt-history-id* *colt-incarnation-id*)
        '(:refused :identity)))
(defconst *colt-o0* (fn-own-start *colt-boot* 2))
(defconst *colt-id* '(7))
(defconst *colt-group* '(102 110 46 116 101 115 116)) ; fn.test
(defconst *colt-register*
  (fn-col-register *colt-o0* 256 *colt-id* *colt-group*))
(assert-event (eq (car *colt-register*) :write))
(assert-event (equal (fn-cpe-operation (cadr *colt-register*))
                     (list :register *colt-id* *fn-col-principal*
                           *colt-group* 1 0 1)))
(assert-event (equal (fn-col-position *colt-o0* *colt-id*)
                     '(:refused :scope)))
(assert-event (equal (fn-col-register *colt-o0* 256 *colt-id* '(1 2 3))
                     '(:refused :query)))

(defconst *colt-s1* (colt-commit *colt-boot* (cadr *colt-register*)))
(defconst *colt-o1* (fn-own-start *colt-s1* 2))
(defconst *colt-position* (fn-col-position *colt-o1* *colt-id*))
(assert-event (eq (car *colt-position*) :position))
(defconst *colt-status-before-article* (fn-col-status *colt-o1* *colt-id*))
(assert-event (eq (car *colt-status-before-article*) :status))
(assert-event (posp (fn-cp-nth 3 *colt-status-before-article*)))
(assert-event
 (equal (fn-cp-nth 3 *colt-status-before-article*)
        (- (fn-cp-nth 2 *colt-status-before-article*)
           (fn-cp-nth 1 *colt-status-before-article*))))
(assert-event
 (equal (fn-cp-nth 1 *colt-status-before-article*)
        (fn-cp-nth 9
         (fn-cp-nth 1
          (fn-cp-cursor-decode (cadr *colt-position*))))))
(assert-event (equal (fn-col-status *colt-o1* '(88)) '(:refused :scope)))
(must-fail
 (assert-event
  (equal (fn-cp-nth 3 (fn-col-status *colt-o1* '(88)))
         (- (fn-cp-nth 2 (fn-col-status *colt-o1* '(88)))
            (fn-cp-nth 1 (fn-col-status *colt-o1* '(88)))))))
(defconst *colt-article*
  (fn-record-make 2 2 2 "<poll@fn.test>" '(65 66)
                  '("fn.test") "poll-pin" "poll-content" "poll-release"
                  2 841000000))
(defconst *colt-after-article*
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io
      (fn-sn-prepare (colt-reserve *colt-s1*) *colt-article*)
      :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(assert-event (equal (fn-sf-phase (fn-sn-files *colt-after-article*))
                     :ready))
(assert-event (equal (fn-sf-records (fn-sn-files *colt-after-article*))
                     (list (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))
                           (cadr *colt-register*) *colt-article*)))
(defconst *colt-poll*
  (fn-col-poll (fn-own-start *colt-after-article* 2) *colt-id*))
(assert-event (eq (car *colt-poll*) :poll))
(assert-event (equal (caddr *colt-poll*) *colt-article*))
(assert-event
 (equal (fn-cp-nth 9
         (fn-cp-nth 1 (fn-cp-cursor-decode (cadr *colt-poll*))))
        3))
(assert-event
 (equal (fn-col-position (fn-own-start *colt-after-article* 2) *colt-id*)
        *colt-position*))
(defconst *colt-second-article*
  (fn-record-make 3 3 3 "<poll-two@fn.test>" '(66)
                  '("fn.test") "poll-two-pin" "poll-two-content"
                  "poll-two-release" 1 841000001))
(assert-event
 (equal (fn-col-poll-scan (list *colt-article* *colt-second-article*)
                          *colt-group* 2 4 16)
        (list :scan 3 *colt-article*)))
(defconst *colt-other-article*
  (fn-record-make 2 2 2 "<other@fn.test>" '(67)
                  '("fn.other") "other-pin" "other-content"
                  "other-release" 1 841000000))
(assert-event
 (equal (fn-col-poll-scan (list *colt-other-article* *colt-second-article*)
                          *colt-group* 2 4 16)
        (list :scan 4 *colt-second-article*)))
(defun colt-neutral-window (sequence count)
  (if (zp count) nil
    (cons (fn-cpe-make sequence sequence sequence '(:rollover (1)))
          (colt-neutral-window (1+ sequence) (1- count)))))
(assert-event
 (equal (fn-col-poll-scan (colt-neutral-window 2 16)
                          *colt-group* 2 18 16)
        '(:scan 18 nil)))
(assert-event
 (equal (fn-col-poll-scan (list *colt-second-article*)
                          *colt-group* 2 4 16)
        '(:refused :history)))
(assert-event (equal (fn-col-register *colt-o1* 256 *colt-id* *colt-group*)
                     (list :no-op
                           (fn-cp-scope-cursor
                            (fn-sn-consumer *colt-s1*)
                            (fn-cp-find *colt-id*
                                        (fn-cp-nth 5 (fn-sn-consumer *colt-s1*)))))))

; The served subject under the operator's consumer count (store profile
; field 9): with one consumer registered, a second is a write under 2 and is
; refused by name under 1; the existing one stays a no-op under 1.
(assert-event (eq (car (fn-col-register *colt-o1* 2 '(8) *colt-group*)) :write))
(assert-event (equal (fn-col-register *colt-o1* 1 '(8) *colt-group*)
                     '(:refused :max-consumers)))
(assert-event (eq (car (fn-col-register *colt-o1* 1 *colt-id* *colt-group*))
                  :no-op))

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
(assert-event
 (equal (fn-cp-nth 1 (fn-col-status *colt-o2* *colt-id*)) 2))
(assert-event
 (equal (fn-cp-nth 2 (fn-col-status *colt-o2* *colt-id*))
        (1+ (fn-cp-nth 2 *colt-status-before-article*))))
(assert-event
 (equal (fn-cp-nth 3 (fn-col-status *colt-o2* *colt-id*))
        (- (fn-cp-nth 2 (fn-col-status *colt-o2* *colt-id*))
           (fn-cp-nth 1 (fn-col-status *colt-o2* *colt-id*)))))
(assert-event (eq (car (fn-col-ack *colt-o2*
                                     (fn-cp-cursor-encode *colt-cursor*)))
                  :no-op))
(assert-event
 (equal (fn-cp-nth 9
                   (fn-cp-nth 1
                    (fn-cp-cursor-decode
                     (cadr (fn-col-position *colt-o2* *colt-id*)))))
        2))
