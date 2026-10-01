(in-package "ACL2")
(include-book "../../books/consumer-remote-reader-source")

; These are semantic coordinate fixtures, not source/custody issuer witnesses.
(defconst *fn-crr-test-source* '(:history-source 1 2 3 nil 4 5 6 7))
(defconst *fn-crr-test-request* '(:remote-consumer :poll "login" "secret" "consumer" nil nil 0))
(defconst *fn-crr-test-ingress*
 (list :authenticated *fn-crr-test-request* "principal" 11 "namespace" 12 13))
(defconst *fn-crr-test-cp* '(:cp nil nil 6 14 nil nil))
(defconst *fn-crr-test-key*
 (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* *fn-crr-test-ingress*
                     *fn-crr-test-cp* 15 6 16 4096))
(assert-event
 (equal *fn-crr-test-key*
   '(:remote-reader-source (:history-capture 9) 1 2 3 7 6 "login" "principal" :poll
     "consumer" 16 4096 (:remote-current 13 15 "namespace" 12 11 6 14 6))))

; Each changed retained-source or current authority scalar breaks equality.
(assert-event
 (not (member-equal *fn-crr-test-key*
  (list
   (fn-crr-source-key '(:history-capture 10) *fn-crr-test-source* *fn-crr-test-ingress* *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) (update-nth 1 100 *fn-crr-test-source*) *fn-crr-test-ingress* *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) (update-nth 2 100 *fn-crr-test-source*) *fn-crr-test-ingress* *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) (update-nth 3 100 *fn-crr-test-source*) *fn-crr-test-ingress* *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) (update-nth 7 100 *fn-crr-test-source*) *fn-crr-test-ingress* *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) (update-nth 8 100 *fn-crr-test-source*) *fn-crr-test-ingress* *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* (update-nth 2 "changed" *fn-crr-test-ingress*) *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* (update-nth 3 "changed" *fn-crr-test-ingress*) *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* (update-nth 4 "changed" *fn-crr-test-ingress*) *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* (update-nth 5 "changed" *fn-crr-test-ingress*) *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* (update-nth 6 "changed" *fn-crr-test-ingress*) *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* (update-nth 1 (update-nth 1 :wait *fn-crr-test-request*) *fn-crr-test-ingress*) *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* (update-nth 1 (update-nth 2 "other-login" *fn-crr-test-request*) *fn-crr-test-ingress*) *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* (update-nth 1 (update-nth 4 "other-consumer" *fn-crr-test-request*) *fn-crr-test-ingress*) *fn-crr-test-cp* 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* *fn-crr-test-ingress* (update-nth 3 100 *fn-crr-test-cp*) 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* *fn-crr-test-ingress* (update-nth 4 100 *fn-crr-test-cp*) 15 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* *fn-crr-test-ingress* *fn-crr-test-cp* 100 6 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* *fn-crr-test-ingress* *fn-crr-test-cp* 15 100 16 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* *fn-crr-test-ingress* *fn-crr-test-cp* 15 6 100 4096)
   (fn-crr-source-key '(:history-capture 9) *fn-crr-test-source* *fn-crr-test-ingress* *fn-crr-test-cp* 15 6 16 100)))))

; Actual STATE unavailable observation preserves every existing scanner,
; reader, reply, callback and custody alias; caller-shaped data grants nothing.
(make-event
 (let* ((prior (fn-owner-remote-scan-read state))
        (fixture (fn-crt-holder '(:history-capture 99) :active '(scanner) '(reader)
                               '(reply) '(callback) '(key) '(outcome)))
        (state (f-put-global 'fn-owner-remote-scan fixture state)))
  (mv-let (word state) (fn-owner-remote-reader-activation-status state)
   (let* ((ok (and (equal word '(:unavailable :consumer-current-publication))
                   (equal fixture (fn-owner-remote-scan-read state))))
          (state (f-put-global 'fn-owner-remote-scan prior state)))
    (if ok (value '(value-triple :passed))
     (er soft 'remote-reader "Unavailable observation changed held aliases."))))))
