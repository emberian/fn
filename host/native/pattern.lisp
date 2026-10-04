;;; `fn pattern NAME ROLE ARG...' (D50; planning/design/zmq-surface-2026-10-04.md
;;; section 4).  ACL2 chose the role's plan and bound its arguments
;;; (books/app-pattern.lisp fn-pat-cli-plan, KEYSTONE
;;; fn-pat-cli-run-binds-every-step); this file is ONE loop over the closed
;;; step vocabulary, each step an existing control request (hybrid-author,
;;; consumer register / wait / ack) or an ACL2 function, (:select) the
;;; partition of a fixed worker set (fn-pat-select-is-one-worker)
;;; (books/app-pattern-delivery.lisp).  A new pattern is a `def-pattern'
;;; declaration and adds nothing here.
;;;
;;; The three acknowledgements stay three: a posting role's exit is the
;;; RETENTION RECEIPT (hybrid-author's status: 0 stored, 3 uncertain -- rerun
;;; with the same SPOOL, which resends the same signed request); a reading
;;; role writes each payload file before it acks (the APPLICATION OUTCOME),
;;; so a crash between them redelivers, never loses.
(in-package "ACL2")

(defun fnn-pattern-arg (bindings key)
  (fnn-octets-string (fnn-octets (cdr (assoc key bindings)))))

(defun fnn-pattern-arg-octets (bindings key)
  (cdr (assoc key bindings)))

(defun fnn-pattern-path (directory name-octets)
  (fnn-concat directory "/" (fnn-octets-string (fnn-octets name-octets))))

(defun fnn-pattern-say (role-word control &rest args)
  (fnn-out "pattern ~a ~?" role-word control args))

(define-condition fnn-pattern-stop (error)
  ((code :initarg :code :reader fnn-pattern-stop-code)))

(defun fnn-pattern-stop (code)
  (error 'fnn-pattern-stop :code code))

(defun fnn-pattern-status-stop (role-word step status word)
  "Report a control status that is not an acceptance and stop with its exit."
  (let ((detail (and word (fnn-core 'fn-native-control-host-reply-detail status word))))
    (if detail
        (fnn-pattern-say role-word "~(~a~) ~(~a~) ~a" step status
                         (fnn-octets-string (fnn-octets detail)))
      (fnn-pattern-say role-word "~(~a~) ~(~a~)" step status)))
  (fnn-pattern-stop (fnn-core 'fn-native-control-host-status-exit-code status)))

(defun fnn-pattern-write-payload (path payload)
  "Write PAYLOAD at PATH; a file already there is a redelivery and must hold
the same octets."
  (if (fnn-check-regular path)
      (unless (equalp (fnn-read-regular-bounded path (1+ (length payload)))
                      (fnn-octets payload))
        (fnn-fault "delivered payload file differs from the redelivered payload: ~a" path))
    (fnn-write-staged path (fnn-octets payload))))

;;; The steps.  ST is a property list carried through the plan.

(defun fnn-pattern-step (step st)
  (let* ((op (first step))
         (bindings (getf st :bindings))
         (role-word (getf st :role-word))
         (arg (lambda (key) (fnn-pattern-arg bindings key)))
         (octets (lambda (key) (fnn-pattern-arg-octets bindings key))))
    (ecase op
      ;; Posting role.
      (:encode
       (let* ((payload (fnn-octet-list
                        (fnn-read-regular-bounded
                         (funcall arg :payload)
                         (fnn-core 'fn-hsig-host-max-source-octets))))
              (seconds (sb-ext:get-time-of-day))
              (bad (fnn-core 'fn-pat-values-check (getf st :name-word)
                             (funcall octets :from) seconds
                             (funcall octets :group) (funcall octets :msgid)))
              (source (and (not bad)
                           (fnn-core 'fn-pat-encode (getf st :name-word)
                                     (funcall octets :from) seconds
                                     (funcall octets :group) (funcall octets :msgid)
                                     payload))))
         (when bad
           (fnn-pattern-say role-word "encode refused ~(~a~)" bad)
           (fnn-pattern-stop +fnn-exit-refused+))
         (unless source
           (fnn-pattern-say role-word "encode refused payload")
           (fnn-pattern-stop +fnn-exit-refused+))
         (setf (getf st :payload) payload (getf st :source) source)
         st))
      (:sign
       (let ((spool (funcall arg :spool))
             (generation (fnn-core 'fn-native-hybrid-control-host-uint32
                                   (funcall arg :generation))))
         (if (fnn-check-regular spool)
             ;; A rerun: resend the request this SPOOL holds, once ACL2 has
             ;; found it to be this message (never sign again).
             (let* ((request (fnn-octet-list
                              (fnn-read-regular-bounded
                               spool (fnn-core 'fn-native-control-host-max-frame))))
                    (bad (fnn-core 'fn-pat-spool-check request generation
                                   (getf st :name-word) (funcall octets :from)
                                   (funcall octets :group) (funcall octets :msgid)
                                   (getf st :payload))))
               (when bad
                 (fnn-pattern-say role-word "sign refused ~(~a~)" bad)
                 (fnn-pattern-stop +fnn-exit-refused+))
               (setf (getf st :request) request)
               st)
           (let* ((keys (mapcar (lambda (name)
                                  (fnn-pattern-path (funcall arg :keys) name))
                                (fnn-core 'fn-pat-key-names)))
                  (signatures
                   (nth-value 3 (apply #'fnn-hsig-sign-source
                                       (append keys (list (getf st :source))))))
                  (request
                   (fnn-core 'fn-native-hybrid-control-host-author-encode
                             generation (getf st :source)
                             (cdr (first signatures)) (cdr (second signatures))
                             (fnn-octet-list (fnn-string-octets (fourth keys))))))
             (unless (fnn-octet-list-p request)
               (fnn-fault "ACL2 refused the pattern's author request"))
             ;; The signed request is kept before it is sent, so an uncertain
             ;; send is settled by resending exactly it.
             (fnn-write-staged spool (fnn-octets request))
             (setf (getf st :request) request)
             st))))
      (:author
       (let ((status (fnn-hybrid-control-send (funcall arg :control)
                                              (getf st :request))))
         (fnn-pattern-say role-word "~(~a~) ~(~a~)"
                          (fnn-core 'fn-native-control-host-status-class status) status)
         (fnn-pattern-stop (fnn-core 'fn-native-control-host-status-exit-code status))))
      ;; Reading role.
      (:register
       (multiple-value-bind (reply word)
           (fnn-consumer-local-exchange (funcall octets :control) :register
                                        (funcall octets :consumer) (funcall octets :group))
         (let ((status (and (consp reply) (second reply))))
           (unless (eq status :accepted)
             (fnn-pattern-status-stop role-word :register status word))
           st)))
      (:wait
       (multiple-value-bind (reply word)
           (fnn-consumer-local-exchange (funcall octets :control) :wait
                                        (funcall octets :consumer) (getf st :timeout))
         (let ((status (and (consp reply) (second reply))))
           (unless (eq status :accepted)
             (fnn-pattern-status-stop role-word :wait status word))
           (setf (getf st :cursor) (third reply) (getf st :report) (fourth reply))
           st)))
      (:project
       (setf (getf st :projected) (fnn-core 'fn-pat-project (getf st :cursor) (getf st :report)))
       st)
      (:decode
       (setf (getf st :decision) (fnn-core 'fn-pat-decode (second step) (getf st :projected)))
       st)
      (:select
       (setf (getf st :decision)
             (fnn-core 'fn-pat-select (getf st :decision)
                       (funcall octets :index) (funcall octets :workers)))
       st)
      (:deliver
       (let ((decision (getf st :decision)))
         (case (first decision)
           (:skip
            ;; Another worker's partition: acknowledged past, never delivered.
            (fnn-pattern-say role-word "skip ~a" (fnn-hex (second decision)))
            st)
           (:deliver
            (destructuring-bind (sequence msgid payload) (rest decision)
              (let ((path (fnn-pattern-path (funcall arg :out)
                                            (fnn-core 'fn-pat-delivery-name sequence))))
                (fnn-pattern-write-payload path payload)
                (fnn-pattern-say role-word "message ~d ~a ~d ~a"
                                 sequence (fnn-hex msgid) (length payload) path)
                (setf (getf st :delivered) (1+ (getf st :delivered 0)))
                st)))
           (:withdrawn
            (fnn-pattern-say role-word "withdrawn ~a" (fnn-hex (second decision)))
            st)
           (:empty (setf (getf st :ended) :timeout) st)
           (otherwise
            (fnn-pattern-say role-word "foreign ~(~a~) ~a" (second decision)
                             (fnn-hex (or (third decision) nil)))
            st))))
      (:ack
       (multiple-value-bind (reply word)
           (fnn-consumer-local-exchange (funcall octets :control) :ack
                                        (getf st :cursor) nil)
         (let ((status (and (consp reply) (second reply))))
           (unless (eq status :accepted)
             (fnn-pattern-status-stop role-word :ack status word))
           st))))))

(defun fnn-pattern-run (st once loop count)
  (dolist (step once) (setq st (fnn-pattern-step step st)))
  (when loop
    (loop
      (dolist (step loop) (setq st (fnn-pattern-step step st)))
      (let ((delivered (getf st :delivered 0)))
        (when (or (getf st :ended) (and (plusp count) (>= delivered count)))
          (fnn-pattern-say (getf st :role-word) "end delivered=~d~@[ ~(~a~)~]"
                           delivered (getf st :ended))
          (return-from fnn-pattern-run
            (if (or (zerop count) (>= delivered count))
                +fnn-exit-ok+
              +fnn-exit-refused+))))))
  +fnn-exit-ok+)

(defun fnn-command-pattern (name argv)
  (let* ((words (cons name argv))
         (bounded (and (<= (length words) 16)
                       (every (lambda (w) (and (stringp w) (<= (length w) 4096))) words)))
         (plan (if bounded
                   (fnn-core 'fn-pat-cli-plan
                             (fnn-octet-list (fnn-string-octets name))
                             (and argv (fnn-octet-list (fnn-string-octets (first argv))))
                             (mapcar (lambda (w) (fnn-octet-list (fnn-string-octets w)))
                                     (rest argv)))
                 '(:usage :argv))))
    (case (first plan)
      (:help
       (fnn-out "~a" (fnn-octets-string (fnn-octets (second plan))))
       +fnn-exit-ok+)
      (:run
       (destructuring-bind (pattern role kind steps bindings timeout count) (rest plan)
         (declare (ignore pattern kind))
         (handler-case
             (fnn-pattern-run (list :bindings bindings
                                    :role-word (string-downcase (symbol-name role))
                                    :name-word (fnn-octet-list (fnn-string-octets name))
                                    :timeout timeout)
                              (first steps) (second steps) count)
           (fnn-pattern-stop (condition) (fnn-pattern-stop-code condition)))))
      (otherwise
       (fnn-err "pattern command refused by ACL2 argv grammar: ~(~a~)" (second plan))
       (fnn-err "~a" (fnn-octets-string (fnn-octets (fnn-core 'fn-pat-usage-text))))
       +fnn-exit-usage+))))

(fnn-register-verb "pattern" #'fnn-command-pattern)
