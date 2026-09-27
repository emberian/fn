;;; Local owner consumer declarations over the existing 0600 control socket.
;;; ACL2 chooses argv grammar, request and reply bytes, scope and event.
(in-package "ACL2")

(defun fnn-command-consumer-local (command argv)
  (let* ((bounded
           (and (<= (length argv) 7)
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
    (destructuring-bind (ignored operation control first second output
                         &optional secret-file seconds) plan
      (declare (ignore ignored))
      (let* ((input
               (if (member operation '(:ack :bound-ack))
                   (fnn-octet-list
                    (fnn-read-regular-bounded
                     (fnn-octets-string (fnn-octets first)) 512))
                 first))
             ;; PRF-234: the account's password, from a file; ACL2 strips
             ;; one final line end and alone compares it.
             (secret
               (and secret-file
                    (fnn-core 'fn-native-control-host-consumer-secret-of-file
                              (fnn-octet-list
                               (fnn-read-regular-bounded
                                (fnn-octets-string (fnn-octets secret-file))
                                498)))))
             (reply
               (fnn-control-consumer-local
                (fnn-octets control) operation input
                (cond ((member operation '(:bound-poll :bound-ack)) secret)
                      ((eq operation :poll) nil)
                      ;; PRF-252: a wait carries its timeout (and a bound
                      ;; wait the password) where a poll carries nothing.
                      ((eq operation :wait) seconds)
                      ((eq operation :bound-wait) (list seconds secret))
                      (t second))))
             (status (and (consp reply) (second reply)))
             (cursor (and (consp reply) (third reply))))
        (unless (and (eq (first reply)
                         (case operation
                           ((:poll :bound-poll :wait :bound-wait)
                            :consumer-poll-reply)
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
                            (or (not (member operation
                                             '(:poll :bound-poll :wait :bound-wait)))
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
        (when (and (eq status :accepted)
                   (member operation '(:poll :bound-poll :wait :bound-wait)))
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
                   (not (member operation
                                '(:poll :bound-poll :wait :bound-wait))))
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

(defun fnn-command-consumer-article (args)
  "Print the article a poll report carries (PRF-252): its Message-ID and its
octets as stored, hex, as ACL2 decodes them.  No Store authority."
  (unless (= (length args) 1)
    (error 'fnn-usage-error :message "usage: fn consumer-article REPORT"))
  (let* ((octets (handler-case
                     (fnn-octet-list
                      (fnn-read-regular-bounded
                       (first args) (fnn-core 'fn-cpj-max-event-octets)))
                   (fnn-input-overbound ()
                     (fnn-out "fn-consumer-article-refused-v1 limit")
                     (return-from fnn-command-consumer-article 1))))
         (article (fnn-core 'fn-native-control-host-consumer-report-article
                            octets)))
    (unless (and (consp article) (eq (first article) :ok)
                 (stringp (second article))
                 (fnn-octet-list-p (third article)))
      (fnn-out "fn-consumer-article-refused-v1 ~(~a~)"
               (if (consp article) (second article) "codec"))
      (return-from fnn-command-consumer-article 1))
    (fnn-out "fn-consumer-article-v1 ~a ~a"
             (fnn-hex (fnn-ascii-octet-list (second article)))
             (fnn-hex (third article)))
    0))

(fnn-register-verb "consumer-article"
                   (lambda (first rest)
                     (fnn-command-consumer-article (cons first rest))))
