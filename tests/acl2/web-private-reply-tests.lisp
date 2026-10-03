; PRF-1279: the same reached reply flow, with live table and private worker.
(in-package "ACL2")
(include-book "web-session-tests")

(defun wprt-compare (config sessions flow event in)
  (declare (xargs :mode :program))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (with-local-stobj fn-web-out
        (mv-let (r fn-web-in fn-web-out)
          (let ((fn-web-in (fn-octets-from-list in fn-web-in)))
            (mv-let (reference table fn-web-out)
              (fn-web-step config sessions flow event fn-web-in fn-web-out)
              (let* ((bytes (fn-octets-list fn-web-out))
                     (fn-web-out (fn-octets-clear fn-web-out)))
                (mv-let (private fn-web-out)
                  (fn-web-private-reply-step config flow event fn-web-in fn-web-out)
                  (mv (list (fn-web-private-reply-p flow event)
                            (equal reference private)
                            (equal bytes (fn-octets-list fn-web-out))
                            (equal table sessions)) fn-web-in fn-web-out)))))
          (mv r fn-web-in)))
      r)))

; The prior book reaches *flow-g* through parsed authenticated GET /g and
; its real :send action. This reply sends OVER without touching the table.
(assert-event
 (equal (wprt-compare *cfg* *ss* *flow-g* '(:reply)
                      (wsst-crlf (list "211 2 1 2 local.general"))) '(t t t t)))

; The resulting reached OVER flow plans its page in the host-enabled mode.
(defconst *wprt-over-flow* (nth 4 (car *st-g2*)))
(assert-event
 (equal (wprt-compare (append (take 6 *cfg*) (list :page-plan)) *ss*
                      *wprt-over-flow* '(:reply)
                      (wsst-crlf (list "224 overview" "1	First	carol	date	<one@local>		12	1" ".")))
        '(t t t t)))

; Hypothesis removal: the parsed authenticated BEGIN is reached, but is not
; private. It touches its live session and sends GROUP; the private boundary
; refuses to do either. There are no other hypotheses in the keystone.
(assert-event
 (equal (wprt-compare *cfg* *ss* nil *ev-g* (wsst-get "/g?name=local.general"))
        '(nil nil nil nil)))
