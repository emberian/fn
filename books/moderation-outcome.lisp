; Compose the result AFTER withdrawal is known in force. Never claim that a
; refused cause article undid an already-published configuration change.
(in-package "ACL2")

(defun fn-mwo-after-withdraw (cause)
 (declare (xargs :guard t))
 (let ((status (if (consp cause)
                   (if (and (eq (car cause) :reason) (consp (cdr cause)))
                       (cadr cause) :invalid)
                 cause)))
  (case status
   ((:accepted :duplicate) cause)
   (:fault (list :reason :fault :withdrawn-cause-fault))
   (:uncertain (list :reason :uncertain :withdrawn-cause-uncertain))
   (:refused (list :reason :uncertain :withdrawn-cause-refused))
   (:clock-unusable (list :reason :uncertain :withdrawn-cause-clock-unusable))
   (:busy (list :reason :uncertain :withdrawn-cause-busy))
   (:article-exceeds-profile-bound
    (list :reason :uncertain :withdrawn-cause-exceeds-profile-bound))
   (:conflict (list :reason :uncertain :withdrawn-cause-conflict))
   ;; Other named refusal statuses also cannot erase the completed first step.
   ((:author-not-enrolled :source-malformed :unknown-group :carrier-refused
     :control-not-filed :control-malformed :signed-event-not-formed)
    (list :reason :uncertain :withdrawn-cause-incomplete))
   (otherwise (list :reason :fault :withdrawn-cause-invalid)))))
