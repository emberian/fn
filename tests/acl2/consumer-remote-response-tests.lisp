(in-package "ACL2")
(include-book "../../books/consumer-remote-response")

(defconst *cr-response-cursor*
 (fn-cp-cursor-encode (fn-cp-cursor '(104) '(105) '(99) '(112) '(113) 1 2 3 4)))

; Every selected operation reads the existing typed consumer contract.
(assert-event
 (and (equal (fn-cr-response-client-read :register
               (fn-cr-response-encode :register :accepted nil nil nil nil nil nil))
             '(:reply (:consumer-reply :accepted nil)))
      (equal (fn-cr-response-client-read :rebase
               (fn-cr-response-encode :rebase :accepted nil *cr-response-cursor* nil nil nil nil))
             (list :reply (list :consumer-reply :accepted *cr-response-cursor*)))
      (equal (fn-cr-response-client-read :position
               (fn-cr-response-encode :position :accepted nil *cr-response-cursor* nil nil nil nil))
             (list :reply (list :consumer-reply :accepted *cr-response-cursor*)))
      (equal (fn-cr-response-client-read :ack
               (fn-cr-response-encode :ack :accepted nil *cr-response-cursor* nil nil nil nil))
             (list :reply (list :consumer-reply :accepted *cr-response-cursor*)))
      (equal (fn-cr-response-client-read :unregister
               (fn-cr-response-encode :unregister :accepted nil nil nil nil nil nil))
             '(:reply (:consumer-reply :accepted nil)))))

(assert-event
 (equal (fn-cr-response-client-read :status
          (fn-cr-response-encode :status :accepted nil nil 7 10 3 nil))
        '(:reply (:consumer-status-reply :accepted 7 10 3))))

(assert-event
 (and (equal (fn-cr-response-client-read :poll
               (fn-cr-response-encode :poll :accepted nil *cr-response-cursor* nil nil nil '(65 66)))
             (list :reply (list :consumer-poll-reply :accepted *cr-response-cursor* '(65 66))))
      (equal (fn-cr-response-client-read :wait
               (fn-cr-response-encode :wait :accepted nil *cr-response-cursor* nil nil nil nil))
             (list :reply (list :consumer-poll-reply :accepted *cr-response-cursor* nil)))))

(assert-event
 (and (equal (fn-cr-response-client-read :poll
               (fn-cr-response-encode :poll :refused :read-scope nil nil nil nil nil))
             (list :status :refused (fn-nctrl-reason-word :read-scope)))
      (equal (fn-cr-response-client-read :ack
               (fn-cr-response-encode :ack :uncertain :durable-write nil nil nil nil nil))
             (list :status :uncertain (fn-nctrl-reason-word :durable-write)))
      (equal (fn-cr-response-client-read :poll
               (fn-cr-response-encode :poll :unavailable :history-gap nil nil nil nil nil))
             (list :status :unavailable (fn-nctrl-reason-word :remote-source-unavailable)))
      (equal (fn-cr-response-client-read :poll
               (fn-cr-response-encode :poll :busy :another-request nil nil nil nil nil))
             (list :status :busy (fn-nctrl-reason-word :another-request)))))

; No private local request fallback and no operator operation on this route.
(assert-event
 (and (equal (fn-cr-response-client-read :poll
               (fn-native-control-reply-encode :refused)) '(:transport :remote-no-downgrade))
      (equal (fn-cr-response-encode :administration :accepted nil nil nil nil nil nil) :bad)
      (equal (fn-cr-response-client-read :administration '(0)) '(:transport))))

(assert-event
 (let* ((report (fn-ncr-withdrawal-report '(60 97 62)))
        (reply (fn-cr-response-client-read :poll
                  (fn-cr-response-encode :poll :accepted nil *cr-response-cursor* nil nil nil report))))
  (and (equal reply (list :reply (list :consumer-poll-reply :accepted *cr-response-cursor* report)))
       (equal (fn-ncr-withdrawal-decode report) '(:withdrawn (60 97 62))))))

(assert-event
 (and (not (fn-cr-response-profilep 0))
      (not (fn-cr-response-profilep (+ 1 *fn-stxa-max-octets*)))
      (fn-cr-response-profilep 1024)
      (equal (fn-cr-response-encode :status :accepted nil nil 11 10 -1 nil) :bad)))
