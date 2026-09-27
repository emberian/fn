; The actual poll's bounded index window uses exact journal objects.
(in-package "ACL2")
(include-book "../../books/consumer-poll-index")
(include-book "must-fail-checked")

; lane history-columns-3: the readers take the history stobj fn-hist.
(defun fn-col-poll-index-window-hx (hist position frontier budget)
  ; fn-col-poll-index-window over a history stobj loaded with HIST (R holds when HIST is the history it reads).
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist)))
        (mv (fn-col-poll-index-window fn-hist position frontier budget) fn-hist))
      ans)))

(defconst *cpit-events*
  (list (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))
        (fn-cpe-make 1 1 1 '(:register (3) (4) (5) 1 1 1))
        (fn-cpe-make 2 2 2
                     (list :ack (fn-cp-cursor '(1) '(2) '(3) '(4) '(5)
                                               1 1 1 2)))))
(defconst *cpit-index* *cpit-events*) ; the history stobj's logical value: the history

(assert-event (equal *cpit-index* *cpit-events*))
(assert-event
 (equal (fn-col-poll-index-window-hx *cpit-index* 1 3 16)
        (cdr *cpit-events*)))
(assert-event
 (equal (fn-col-poll-scan
         (fn-col-poll-index-window-hx *cpit-index* 1 3 16)
         '(4) 1 3 16)
        '(:scan 3 nil)))
(assert-event (null (fn-col-poll-index-window-hx *cpit-index* 3 3 16)))
(assert-event (equal (len (fn-col-poll-index-window-hx
                           *cpit-index* 0 3 1)) 1))

; Omitting the correspondence premise permits an indexed substitution.
(must-fail-checked
 (assert-event
  (equal (fn-col-poll-index-window-hx nil 1 3 2)
         (fn-col-poll-list-window *cpit-events* 1 3 2))))
