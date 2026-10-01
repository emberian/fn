(in-package "ACL2")
(include-book "../../books/consumer-remote-terminal-state")

; Actual STATE holder executions. Fixture tokens/aliases are bookkeeping
; values only; they are not a genuine capture or physical operation receipt.
(make-event
 (let ((state (f-put-global 'fn-owner-remote-scan nil state)))
  (mv-let (one state)
   (fn-owner-remote-scan-hold-internal '(:history-capture 7) '(scanner) '(reader)
                                      '(reply) '(callback) '(semantic-key) state)
   (mv-let (two state) (fn-owner-remote-scan-cancel '(:history-capture 7) state)
    (let ((cancelled (fn-owner-remote-scan-read state)))
     (mv-let (three state) (fn-owner-remote-scan-terminal '(:history-capture 7) state)
      (let* ((same (fn-owner-remote-scan-read state))
             (ok (and (equal one '(:held)) (equal two '(:cancellation-held))
                       (equal three '(:unavailable :remote-native-completion-issuer))
                       (equal same cancelled)
                       (equal same '(:remote-scan-holder (:history-capture 7) :cancelled
                                     (scanner) (reader) (reply) (callback) (semantic-key) nil))))
             (state (f-put-global 'fn-owner-remote-scan nil state)))
       (if ok (value '(value-triple :passed))
         (er soft 'remote-terminal "Cancellation/terminal changed a retained alias.")))))))))

(make-event
 (let ((state (f-put-global 'fn-owner-remote-scan nil state)))
  (mv-let (one state)
   (fn-owner-remote-scan-hold-internal '(:history-capture 8) '(scanner) '(reader) '(reply) '(callback) '(key) state)
   (let ((before (fn-owner-remote-scan-read state)))
    (mv-let (two state)
     (fn-owner-remote-scan-hold-internal '(:history-capture 9) nil nil nil nil nil state)
     (let* ((ok (and (equal one '(:held)) (equal two '(:refused :remote-scan-busy))
                     (equal before (fn-owner-remote-scan-read state))))
            (state (f-put-global 'fn-owner-remote-scan nil state)))
      (if ok (value '(value-triple :passed))
        (er soft 'remote-busy "Second hold overwrote the source/aliases."))))))))

; Empty pure continuations do not manufacture physical quiescence.
(make-event
 (let ((state (f-put-global 'fn-owner-remote-scan nil state)))
  (mv-let (one state)
   (fn-owner-remote-scan-hold-internal '(:history-capture 10) nil nil nil nil '(key) state)
   (let ((before (fn-owner-remote-scan-read state)))
    (mv-let (two state) (fn-owner-remote-scan-terminal '(:history-capture 10) state)
     (let* ((ok (and (equal one '(:held))
                     (equal two '(:unavailable :remote-native-completion-issuer))
                     (equal before (fn-owner-remote-scan-read state))))
            (state (f-put-global 'fn-owner-remote-scan nil state)))
      (if ok (value '(value-triple :passed))
        (er soft 'remote-empty "Empty cursor fabricated physical completion."))))))))

(make-event
 (let ((state (f-put-global 'fn-owner-remote-scan nil state)))
  (mv-let (one state)
   (fn-owner-remote-scan-hold-internal '(:history-capture 11) '(scanner) '(reader) '(reply) '(callback) '(key) state)
   (let ((before (fn-owner-remote-scan-read state)))
    (mv-let (two state) (fn-owner-remote-scan-cancel '(:history-capture 12) state)
     (mv-let (three state) (fn-owner-remote-scan-terminal '(:history-capture 12) state)
      (let* ((ok (and (equal one '(:held))
                      (equal two '(:refused :remote-scan-token))
                      (equal three '(:refused :remote-scan-token))
                      (equal before (fn-owner-remote-scan-read state))))
             (state (f-put-global 'fn-owner-remote-scan nil state)))
       (if ok (value '(value-triple :passed))
         (er soft 'remote-stale "Stale token modified retained aliases.")))))))))
