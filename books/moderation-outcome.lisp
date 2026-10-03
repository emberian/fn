; Compose the result AFTER the withdrawal authorization is known persisted. Never claim that a
; refused cause article undid an already-published configuration change.
(in-package "ACL2")

(defun fn-mwo-after-authorization (cause)
 (declare (xargs :guard t))
 (let ((status (if (consp cause)
                   (if (and (eq (car cause) :reason) (consp (cdr cause)))
                       (cadr cause) :invalid)
                 cause)))
  (case status
   ((:accepted :duplicate) cause)
   (:fault (list :reason :fault :withdrawal-authorized-cause-fault))
   (:uncertain (list :reason :uncertain :withdrawal-authorized-cause-uncertain))
   (:refused (list :reason :uncertain :withdrawal-authorized-cause-refused))
   (:clock-unusable (list :reason :uncertain :withdrawal-authorized-cause-clock-unusable))
   (:busy (list :reason :uncertain :withdrawal-authorized-cause-busy))
   (:article-exceeds-profile-bound
    (list :reason :uncertain :withdrawal-authorized-cause-exceeds-profile-bound))
   (:conflict (list :reason :uncertain :withdrawal-authorized-cause-conflict))
   ;; Other named refusal statuses also cannot erase the completed first step.
   ((:author-not-enrolled :source-malformed :unknown-group :carrier-refused
     :control-not-filed :control-malformed :signed-event-not-formed)
    (list :reason :uncertain :withdrawal-authorized-cause-incomplete))
   (otherwise (list :reason :fault :withdrawal-authorized-cause-invalid)))))
