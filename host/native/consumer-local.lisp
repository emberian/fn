;;; Local owner consumer declarations over the existing 0600 control socket.
;;; ACL2 chooses argv grammar, request and reply bytes, scope and event.
(in-package "ACL2")

(defun fnn-command-consumer-local (command argv)
  (let* ((bounded
           (and (<= (length argv) 4)
                (<= (length command) 512)
                (every (lambda (word) (<= (length word) 512)) argv)))
         (plan
           (if bounded
               (fnn-core 'fn-native-control-host-consumer-cli-plan
                         (fnn-ascii-octet-list command)
                         (mapcar #'fnn-ascii-octet-list argv))
             '(:usage :argv)))
         (tag (and (consp plan) (first plan))))
    (unless (eq tag :run)
      (fnn-err "consumer command refused by ACL2 argv grammar: ~a"
               (and (consp plan) (second plan)))
      (return-from fnn-command-consumer-local +fnn-exit-usage+))
    (destructuring-bind (ignored operation control first second output) plan
      (declare (ignore ignored))
      (let* ((input
               (if (eq operation :ack)
                   (fnn-octet-list
                    (fnn-read-regular-bounded
                     (fnn-octets-string (fnn-octets first)) 512))
                 first))
             (reply
               (fnn-control-consumer-local
                (fnn-octets control) operation input
                (if (eq operation :poll) nil second)))
             (status (and (consp reply) (second reply)))
             (cursor (and (consp reply) (third reply))))
        (unless (and (eq (first reply)
                         (case operation
                           (:poll :consumer-poll-reply)
                           (:status :consumer-status-reply)
                           (otherwise :consumer-reply)))
                     (member status '(:accepted :refused :uncertain :fault))
                     (if (eq operation :status)
                         (if (eq status :accepted)
                             (and (every (lambda (value)
                                           (and (integerp value)
                                                (not (minusp value))))
                                         (cddr reply))
                                  (= (length reply) 5))
                           (and (null cursor) (null (fourth reply))
                                (null (fifth reply))))
                       (and (fnn-octet-list-p cursor)
                            (or (not (eq operation :poll))
                                (fnn-octet-list-p (fourth reply))))))
          (fnn-fault "local consumer control returned malformed reply"))
        (when (eq operation :status)
          (when (eq status :accepted)
            (fnn-out "consumer status accepted committed-ack=~d committed-journal-frontier=~d journal-event-distance=~d"
                     (third reply) (fourth reply) (fifth reply)))
          (unless (eq status :accepted)
            (fnn-out "consumer status ~(~a~)" status))
          (return-from fnn-command-consumer-local
            (fnn-core 'fn-native-control-host-status-exit-code status)))
        (when (and (eq status :accepted) (eq operation :poll))
          ;; Report first, cursor last: a cursor file implies both outputs
          ;; were created.  Poll is read-only; an output failure is a local
          ;; fault and a repeat poll may redeliver the same event.
          (handler-case
              (progn
                (fnn-write-staged
                 (fnn-octets-string (fnn-octets output))
                 (fnn-octets (fourth reply)))
                (fnn-write-staged
                 (fnn-octets-string (fnn-octets second))
                 (fnn-octets cursor)))
            (error () (setq status :fault))))
        (when (and (eq status :accepted) output
                   (not (eq operation :poll)))
          (unless (consp cursor)
            (fnn-fault "accepted consumer command returned no cursor"))
          ;; This output file is an application convenience, never fn's
          ;; durable ack authority.  If creating it fails after an accepted
          ;; Store write, report uncertainty; POSITION settles the outcome.
          (handler-case
              (fnn-write-staged
               (fnn-octets-string (fnn-octets output)) (fnn-octets cursor))
            (error ()
              (setq status :uncertain))))
        (fnn-out "consumer ~(~a~)" status)
        (fnn-core 'fn-native-control-host-status-exit-code status)))))

(fnn-register-verb "consumer" #'fnn-command-consumer-local)
