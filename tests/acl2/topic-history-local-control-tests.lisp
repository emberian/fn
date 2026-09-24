(in-package "ACL2")
(include-book "../../books/topic-history-local-control")
(include-book "std/testing/must-fail" :dir :system)

(assert-event (equal (fn-thlc-request-decode
                      (fn-thlc-request-encode :install nil nil))
                     '(:topic :install nil nil)))
(assert-event (equal (fn-thlc-request-decode
                      (fn-thlc-request-encode :anchor 4294967295 64))
                     '(:topic :anchor 4294967295 64)))
(assert-event (equal (fn-thlc-request-decode
                      (fn-thlc-request-encode :report 7 nil))
                     '(:topic :report 7 nil)))
(assert-event (equal (fn-thlc-request-encode :anchor 1 65) :bad))
(assert-event (equal (fn-thlc-request-encode :report 1 1) :bad))
(assert-event (equal (fn-thlc-request-decode
                      (fn-nctrl-seal *fn-thlc-request-kind* '(1 0 0 0 1 0)))
                     '(:refused :request)))
(assert-event (equal (fn-thlc-request-decode
                      (fn-nctrl-seal *fn-thlc-request-kind* '(0 1)))
                     '(:refused :request)))
(assert-event (equal (fn-thlc-reply-decode
                      (fn-thlc-reply-encode :uncertain))
                     '(:topic-reply :uncertain)))
(must-fail
 (assert-event
  (equal (fn-thlc-request-decode
          (fn-nctrl-seal *fn-thlc-request-kind* '(1 0 0 0 1 0)))
         '(:topic :anchor 1 0))))
