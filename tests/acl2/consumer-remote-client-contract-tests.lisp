; Actual exported PROGRAM client entry executions. These fixtures preserve
; shared FNCT reasons and old singleton paths, not physical parser funding.
(in-package "ACL2")
(include-book "../../books/records-attach")

(defun fn-crcol-client-host-fixtures ()
 (declare (xargs :mode :program))
 (let* ((cursor (fn-cp-cursor-encode (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 2)))
        (withdrawn (fn-ncr-withdrawal-report '(60 97 62)))
        (record (fn-record-encode-impl
          (fn-record-make 1 2 3 "<m@x>" '(65 66 67) '("a") "o" "s" "e" 3 0)))
        (collection (fn-crcol-encode-reference (list withdrawn record) 3 4096))
        (wire (fn-cr-response-encode :poll :accepted nil cursor nil nil nil collection))
        (expected (list :consumer-poll-reports cursor
                    '((:withdrawn (60 97 62)) (:article "<m@x>" (65 66 67) ("a")))))
        (single (fn-cr-response-encode :poll :accepted nil cursor nil nil nil record)))
  (list
   (list :poll wire 1 3 4096 expected)
   (list :wait wire 1 3 4096 expected)
   (list :poll wire nil 3 4096 '(:refused :remote-report-version))
   (list :poll wire 2 3 4096 '(:refused :remote-report-version))
   (list :poll wire 1 1 4096 '(:refused :remote-report-count))
   (list :poll wire 1 3 32 '(:refused :remote-report-profile))
   (list :poll (fn-cr-response-encode :poll :accepted nil cursor nil nil nil
                  (append collection '(0))) 1 3 4096 '(:refused :remote-report-tail))
   (list :poll single nil 3 4096
         (list :reply (list :consumer-poll-reply :accepted cursor record)))
   (list :poll (fn-cr-response-encode :poll :accepted nil cursor nil nil nil withdrawn) nil 3 4096
         (list :reply (list :consumer-poll-reply :accepted cursor withdrawn)))
   (list :poll (fn-cr-response-encode :poll :accepted nil cursor nil nil nil nil) nil 3 4096
         (list :reply (list :consumer-poll-reply :accepted cursor nil)))
   (list :poll (fn-cr-response-encode :poll :refused :read-forbidden nil nil nil nil nil) 1 3 4096
         (list :status :refused (fn-nctrl-reason-word :read-forbidden)))
   (list :ack (fn-cr-response-encode :ack :uncertain :persist-ambiguous nil nil nil nil nil) 1 3 4096
         (list :status :uncertain (fn-nctrl-reason-word :persist-ambiguous)))
   (list :wait (fn-cr-response-encode :wait :unavailable nil nil nil nil nil nil) 1 3 4096
         (list :status :unavailable (fn-nctrl-reason-word :remote-source-unavailable)))
   (list :register (fn-cr-response-encode :register :busy :account-busy nil nil nil nil nil) 1 3 4096
         (list :status :busy (fn-nctrl-reason-word :account-busy)))
   (list :rebase (fn-cr-response-encode :rebase :fault :recovery-required nil nil nil nil nil) 1 3 4096
         (list :status :fault (fn-nctrl-reason-word :recovery-required)))
   (list :position (fn-native-control-reply-encode :refused) 1 3 4096
         '(:transport :remote-no-downgrade))
   (list :status '(0) 1 3 4096 '(:transport))
   (list :unregister (fn-cr-response-encode :unregister :accepted nil cursor nil nil nil nil) 1 3 4096
         (list :reply (list :consumer-reply :accepted cursor))))))

