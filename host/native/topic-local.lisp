;;; Experimental fixed local administrator topic operations.  ACL2 parses
;;; argv and frame bytes; this raw adapter only moves them over the socket.
(in-package "ACL2")

(defun fnn-command-topic-local (command argv)
  (let* ((bounded
           (and (<= (length argv) 3)
                (<= (length command) 512)
                (every (lambda (word) (<= (length word) 512)) argv)))
         (plan
           (if bounded
               (fnn-core 'fn-native-control-host-topic-cli-plan
                         (fnn-ascii-octet-list command)
                         (mapcar #'fnn-ascii-octet-list argv))
             '(:usage :argv))))
    (unless (and (consp plan) (eq (first plan) :run))
      (fnn-err "topic command refused by ACL2 argv grammar: ~a"
               (and (consp plan) (second plan)))
      (return-from fnn-command-topic-local +fnn-exit-usage+))
    (destructuring-bind (ignored operation control sequence quota) plan
      (declare (ignore ignored))
      (let ((status (fnn-control-topic-local
                     (fnn-octets control) operation sequence quota)))
        (unless (member status '(:accepted :refused :uncertain :fault))
          (fnn-fault "topic control returned malformed status"))
        (fnn-out "topic ~(~a~)" status)
        (fnn-core 'fn-native-control-host-status-exit-code status)))))

(fnn-register-verb "topic" #'fnn-command-topic-local)
