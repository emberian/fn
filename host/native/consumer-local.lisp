;;; Local owner consumer declarations over the existing 0600 control socket.
;;; ACL2 chooses argv grammar, request and reply bytes, scope and event.
(in-package "ACL2")

(defun fnn-consumer-say (json operation status word &optional counts summary)
  "Print the command's outcome: ACL2's JSON line (PKT-709) or the text line,
`consumer STATUS' followed by the refusal's reason word when it named one."
  (if json
      (fnn-out "~a" (fnn-octets-string
                     (fnn-octets (fnn-core 'fn-native-control-host-consumer-json-line
                                           operation status word counts summary))))
    (let ((detail (and word (fnn-core 'fn-native-control-host-reply-detail
                                      status word))))
      (if detail
          (fnn-out "consumer ~(~a~) ~a" status
                   (fnn-octets-string (fnn-octets detail)))
        (fnn-out "consumer ~(~a~)" status)))))

(defun fnn-command-consumer-local (command argv)
  (let* ((bounded
           (and (<= (length argv) 8)
                (<= (length command) 512)
                (every (lambda (word) (<= (length word) 512)) argv)))
         (plan
           (if bounded
               (fnn-core 'fn-native-control-host-consumer-cli-plan
                         (fnn-ascii-octet-list command)
                         (mapcar #'fnn-ascii-octet-list argv))
             '(:usage :argv)))
         ;; PKT-709: `--json COMMAND ...' is (:json PLAN).
         (json (and (consp plan) (eq (first plan) :json)))
         (plan (if json (second plan) plan))
         (tag (and (consp plan) (first plan))))
    (when (eq tag :help)
      (fnn-out "~a" (fnn-core 'fn-ncl-usage-text))
      (return-from fnn-command-consumer-local +fnn-exit-ok+))
    (unless (eq tag :run)
      (fnn-err "consumer command refused by ACL2 argv grammar: ~a"
               (and (consp plan) (second plan)))
      (fnn-err "~a" (fnn-core 'fn-ncl-usage-text))
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
             (argument
               (cond ((member operation '(:bound-poll :bound-ack)) secret)
                     ((eq operation :poll) nil)
                     ;; PRF-252: a wait carries its timeout (and a bound
                     ;; wait the password) where a poll carries nothing.
                     ((eq operation :wait) seconds)
                     ((eq operation :bound-wait) (list seconds secret))
                     (t second)))
             (reply nil) (word nil))
        (multiple-value-setq (reply word)
          (fnn-control-consumer-local (fnn-octets control) operation input argument))
        ;; PKT-709: a register the owner refused for want of the node's
        ;; consumer history (or an old owner refused with no reason)
        ;; bootstraps it and registers once more (fn-ncr-cli-after); the
        ;; last reply is the command's.
        (when (fnn-core 'fn-native-control-host-consumer-cli-after
                        operation (and (consp reply) (second reply)) word)
          (multiple-value-setq (reply word)
            (fnn-control-consumer-local (fnn-octets control) :bootstrap nil nil))
          ;; An uncertain bootstrap may have persisted.  Preserve its outcome
          ;; and stop; ACL2 permits registration only after acceptance.
          (when (fnn-core 'fn-native-control-host-consumer-cli-after
                          :bootstrap (and (consp reply) (second reply)) word)
            (multiple-value-setq (reply word)
              (fnn-control-consumer-local (fnn-octets control)
                                          operation input argument))))
        (let ((status (and (consp reply) (second reply)))
              (cursor (and (consp reply) (third reply))))
          (when (eq operation :status)
            (cond (json
                   (fnn-consumer-say t operation status word
                                     (and (eq status :accepted)
                                          (list (third reply) (fourth reply)
                                                (fifth reply)))))
                  ((eq status :accepted)
                   (fnn-out "consumer status accepted committed-ack=~d committed-journal-frontier=~d journal-event-distance=~d"
                            (third reply) (fourth reply) (fifth reply)))
                  (t
                   (let ((detail (and word (fnn-core 'fn-native-control-host-reply-detail
                                                     status word))))
                     (if detail
                         (fnn-out "consumer status ~(~a~) ~a" status
                                  (fnn-octets-string (fnn-octets detail)))
                       (fnn-out "consumer status ~(~a~)" status)))))
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
          (fnn-consumer-say
           json operation status word nil
           (and (eq status :accepted)
                (member operation '(:poll :bound-poll :wait :bound-wait))
                (fnn-core 'fn-native-control-host-consumer-report-summary
                          (fourth reply))))
          (fnn-core 'fn-native-control-host-status-exit-code status))))))

(fnn-register-verb "consumer" #'fnn-command-consumer-local)

(defun fnn-command-consumer-article (args)
  "Print the article a poll report carries (PRF-252): its Message-ID and its
octets as stored, hex, as ACL2 decodes them.  A withdrawal report (PKT-710)
prints `fn-consumer-withdrawn-v1 MSGID-HEX'.  With --json (PKT-709), ACL2's
one JSON line.  No Store authority."
  (let ((json (and (= (length args) 2) (equal (first args) "--json"))))
    (when json (setq args (rest args)))
    (unless (= (length args) 1)
      (error 'fnn-usage-error :message "usage: fn consumer-article [--json] REPORT"))
    (let* ((octets (handler-case
                       (fnn-octet-list
                        (fnn-read-regular-bounded
                         (first args) (fnn-core 'fn-cpj-max-event-octets)))
                     (fnn-input-overbound ()
                       (fnn-out "fn-consumer-article-refused-v1 limit")
                       (return-from fnn-command-consumer-article 1))))
           (summary (fnn-core 'fn-native-control-host-consumer-report-summary
                              octets)))
      (when json
        (fnn-out "~a" (fnn-octets-string
                       (fnn-octets (fnn-core 'fn-native-control-host-consumer-article-json
                                             summary))))
        (return-from fnn-command-consumer-article
          (if (member (first summary) '(:article :withdrawn)) 0 1)))
      (case (first summary)
        (:withdrawn
         (fnn-out "fn-consumer-withdrawn-v1 ~a" (fnn-hex (second summary)))
         0)
        (:article
         (fnn-out "fn-consumer-article-v1 ~a ~a"
                  (fnn-hex (second summary)) (fnn-hex (third summary)))
         0)
        (otherwise
         (fnn-out "fn-consumer-article-refused-v1 ~(~a~)"
                  (if (eq (first summary) :empty) "empty" "codec"))
         1)))))

(fnn-register-verb "consumer-article"
                   (lambda (first rest)
                     (fnn-command-consumer-article (cons first rest))))
