(in-package "ACL2")
(include-book "../../books/consumer-remote-semantic-state")

; Actual owner STATE refusal: shaped aliases never manufacture source custody.
(make-event
 (let* ((token '(:history-capture 20))
        (state (f-put-global 'fn-owner-history-capture nil state))
        (state (f-put-global 'fn-owner-history-read nil state))
        (state (f-put-global 'fn-owner-remote-scan
          (fn-crt-holder token :active '(scanner) nil '(:event-before-query row 1)
                         '(callback) '(key) nil) state))
        (before (fn-owner-remote-scan-read state)))
  (mv-let (answer state)
   (fn-owner-remote-semantic-step-internal token '(key) '(:authenticated) 9 nil nil 1
                                         fn-history-backing state)
   (let* ((ok (and (equal answer '(:unavailable :history-source))
                   (equal before (fn-owner-remote-scan-read state))))
          (state (f-put-global 'fn-owner-remote-scan nil state)))
    (if ok (value '(value-triple :passed))
      (er soft 'remote-semantic "A shaped source consumed held event aliases."))))))

; Corrupted-state fixture for the INTERNAL alias transition, not installation.
; A refusal preserves the semantic cursor plus actual callback and read aliases.
(make-event
 (let* ((token '(:history-capture 21))
        (state (f-put-global 'fn-owner-remote-scan
          (fn-crt-holder token :active '(scanner) '(reader) '(:semantic cursor)
                         '(callback) '(key) nil) state))
        (before (fn-owner-remote-scan-read state)))
  (mv-let (answer state)
   (fn-owner-remote-semantic-keep token '(:refused :remote-semantic-source-changed) state)
   (let* ((ok (and (equal answer '(:refused :remote-semantic-source-changed))
                   (equal before (fn-owner-remote-scan-read state))))
          (state (f-put-global 'fn-owner-remote-scan nil state)))
    (if ok (value '(value-triple :passed))
      (er soft 'remote-semantic "Refusal discarded a saved semantic child."))))))

; Saving a report input does not advance the cursor or relinquish a callback.
; Cancellation retains the complete target/report/resumption projection.
(make-event
 (let* ((token '(:history-capture 22))
        (state (f-put-global 'fn-owner-history-read nil state))
        (state (f-put-global 'fn-owner-remote-scan
          (fn-crt-holder token :active '(scanner) nil '(:semantic cursor)
                         '(callback) '(key) nil) state))
        (input '(:report-input :withdrawal-target (:report-input target ("a") (("a" . 1)))
                              (:yield continuation))))
  (mv-let (answer state) (fn-owner-remote-semantic-keep token input state)
   (mv-let (cancel state) (fn-owner-remote-scan-cancel token state)
    (let* ((held (fn-owner-remote-scan-read state))
           (ok (and (equal answer '(:report-input-held)) (equal cancel '(:cancellation-held))
                    (eq (fn-cp-nth 2 held) :cancelled) (equal (fn-cp-nth 3 held) '(scanner))
                    (equal (fn-cp-nth 5 held) (list :semantic-report input))
                    (equal (fn-cp-nth 6 held) '(callback))))
           (state (f-put-global 'fn-owner-remote-scan nil state)))
     (if ok (value '(value-triple :passed))
       (er soft 'remote-semantic "Cancellation consumed report/continuation/callback aliases.")))))))

(make-event
 (let* ((token '(:history-capture 23))
        (state (f-put-global 'fn-owner-remote-scan
          (fn-crt-holder token :active '(scanner) '(reader) '(:semantic cursor)
                         '(callback) '(key) nil) state))
        (before (fn-owner-remote-scan-read state)))
  (mv-let (answer state)
   (fn-owner-remote-semantic-step-internal token '(changed) '(:authenticated) 9 nil nil 1
                                         fn-history-backing state)
   (let* ((ok (and (equal answer '(:refused :consumer-source-changed))
                   (equal before (fn-owner-remote-scan-read state))))
          (state (f-put-global 'fn-owner-remote-scan nil state)))
    (if ok (value '(value-triple :passed))
      (er soft 'remote-semantic "Changed current semantic source consumed a continuation."))))))
