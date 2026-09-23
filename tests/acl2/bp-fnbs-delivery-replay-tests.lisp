(in-package "ACL2")
(include-book "../../books/bp-fnbs-delivery-replay")
(include-book "bp-app-handoff-tests")
(include-book "../../books/bp-node-receive-boundary")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpahr-stored* (fn-bpnf-stored-record 3 0 *bpah-held*))
(defconst *bpahr-identity*
  (fn-bpp-primary-identity (fn-bpb-bundle-primary *bpah-bundle*)))
(defconst *bpahr-delivered*
  (fn-bpah-delivery-record 3 1 0 *bpahr-identity*
                           :request-accepted '(114 105 100)))
(defun bpahr-row5 ()
  (list (fn-bpnf-stored-record-name 3 0)
        (fn-bpnf-stored-record-frame *bpahr-stored*)))
(defun bpahr-row7 ()
  (list (fn-bpnf-stored-record-name 3 1)
        (fn-bpah-delivery-frame *bpahr-delivered*)))
(defun bpahr-rows () (list (bpahr-row5) (bpahr-row7)))

(assert-event (fn-bpnf-stored-recordp *bpahr-stored*))
(assert-event (fn-bpah-delivery-recordp *bpahr-delivered*))
(assert-event (equal (car (fn-bpah-replay-rows (bpahr-rows) 4 1048576)) :ready))
(assert-event
 (equal (nth 2 (fn-bpah-replay-rows (bpahr-rows) 4 1048576))
        (list (fn-bpnf-handoff
               '(114 105 100)
               (fn-bpnf-held-key (fn-bpnf-held-principal *bpah-held*)
                                  (fn-bpnf-held-id *bpah-held*))
               :owed))))
(make-event
 (let* ((replayed (fn-bpah-replay-rows (bpahr-rows) 4 1048576))
        (st (fn-bpnf-state (fn-bpnf-base *bpah-state*)
                            (nth 1 replayed) nil (nth 2 replayed)
                            nil nil nil 4 0)))
   (if (equal (fn-bpah-outbox-view st)
              (list :outbox '(114 105 100)
                    (fn-bpnf-held-key (fn-bpnf-held-principal *bpah-held*)
                                       (fn-bpnf-held-id *bpah-held*))
                    *bpah-adu* "dtn://sender/"
                    (append (fn-record-string-octets "bp-receipt:")
                            '(114 105 100 58 48))
                    (fn-record-string-octets "return") 0))
       '(assert-event t)
     '(assert-event nil))))
(make-event
 (let* ((replayed (fn-bpah-replay-rows (bpahr-rows) 4 1048576))
        (st (fn-bpnf-state (fn-bpnf-base *bpah-state*)
                            (nth 1 replayed) nil (nth 2 replayed)
                            nil nil nil 4 0))
        (view (fn-bpah-outbox-view st)))
   (if (and (fn-bpah-outbox-peer-matchp view "dtn://sender/")
            (not (fn-bpah-outbox-peer-matchp view "dtn://other/")))
       '(assert-event t)
     '(assert-event nil))))
(assert-event
 (equal (fn-bpn-nth 10 (car (nth 1 (fn-bpah-replay-rows
                                   (bpahr-rows) 4 1048576))))
        '(:delivered :request-accepted (114 105 100))))
(assert-event
 (equal (car (fn-bpah-replay-rows (list (bpahr-row7)) 4 1048576)) :fault))
(assert-event
 (equal (car (fn-bpah-replay-rows
              (list (bpahr-row5) (bpahr-row7) (bpahr-row7))
              4 1048576)) :fault))
(assert-event
 (equal (car (fn-bpah-replay-rows
              (list (bpahr-row5)
                    (list (fn-bpnf-stored-record-name 3 1)
                          (fn-bpah-delivery-frame
                           (fn-bpah-delivery-record
                            3 1 0 '(1 2 3) :request-accepted '(114)))))
              4 1048576)) :fault))
(assert-event
 (equal (car (fn-bpah-replay-rows
              (list (bpahr-row5)
                    (list (fn-bpnf-stored-record-name 3 1)
                          (fn-bpah-delivery-frame
                           (fn-bpah-delivery-record
                            3 1 0 *bpahr-identity*
                            :receipt-accepted '(114)))))
              4 1048576)) :fault))
(must-fail
 (assert-event
  (equal (car (fn-bpah-replay-rows (list (bpahr-row7)) 4 1048576))
         :ready)))

; The same application result is authorized through the host-called step.
(defconst *bpahr-key*
  (fn-bpnf-held-key (fn-bpnf-held-principal *bpah-held*)
                     (fn-bpnf-held-id *bpah-held*)))
(defconst *bpahr-live-start*
  (fn-bpnf-answer-state
   (fn-bpnf-step *bpah-state* (list :deliver *bpahr-key* *bpah-local*))))
(defconst *bpahr-live-result*
  (fn-bpnf-answer-state
   (fn-bpnf-step *bpahr-live-start*
                 (list :deliver-result 1 1 *bpahr-key*
                       :request-accepted '(114 105 100)))))
(defconst *bpahr-live-durable*
  (fn-bpnf-answer-state
   (fn-bpnf-step *bpahr-live-result* '(:persist-result 1 2 :durable))))
(assert-event (equal (fn-bpnf-waits *bpahr-live-start*)
                     (list :delivery 1 1 *bpahr-key*)))
(assert-event (equal (fn-bpn-nth 3 (fn-bpnf-issued *bpahr-live-result*))
                     :deliver))
(assert-event (equal (fn-bpnf-handoffs *bpahr-live-durable*)
                     (nth 2 (fn-bpah-replay-rows (bpahr-rows) 4 1048576))))
(assert-event (equal (fn-bpnf-held-list *bpahr-live-durable*)
                     (nth 1 (fn-bpah-replay-rows (bpahr-rows) 4 1048576))))
(assert-event
 (equal (fn-bpnf-answer-state
         (fn-bpnf-step *bpahr-live-start*
                       (list :deliver-result 1 0 *bpahr-key*
                             :request-accepted '(114 105 100))))
        *bpahr-live-start*))
(defconst *bpahr-live-uncertain*
  (fn-bpnf-answer-state
   (fn-bpnf-step *bpahr-live-start*
                 (list :deliver-result 1 1 *bpahr-key*
                       :uncertain nil))))
(assert-event (fn-bpah-delivery-uncertainp *bpahr-live-uncertain*))
(assert-event
 (equal (fn-bpnf-answer-state
         (fn-bpnf-step *bpahr-live-uncertain*
                       (list :deliver *bpahr-key* *bpah-local*)))
        *bpahr-live-uncertain*))
(assert-event
 (equal (fn-bpnf-answer-state
         (fn-bpnf-step *bpahr-live-uncertain*
                       (list :receive-bundle *bpah-bundle*
                             (fn-bpb-encode *bpah-bundle*) *bpah-ingress*)))
        *bpahr-live-uncertain*))
(assert-event
 (equal (fn-bpnf-host-eventp (list :deliver *bpahr-key* *bpah-local*)) t))
(assert-event
 (equal (fn-bpnf-host-eventp
         (list :deliver-result 1 1 *bpahr-key*
               :request-accepted '(114 105 100))) t))
(assert-event
 (equal (fn-bpnf-host-eventp
         (list :deliver-result 1 1 *bpahr-key*
               :request-accepted '(114 105 100) :extra)) nil))
(must-fail
 (assert-event
  (equal (fn-bpnf-handoffs *bpahr-live-start*)
         (fn-bpnf-handoffs *bpahr-live-durable*))))
