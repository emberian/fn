;;; Native administrative configuration executor.
;;;
;;; This internal verb has one job: execute an ACL2-native-admin plan while
;;; holding the store's existing exclusive writer lock.  It deliberately does
;;; not add public CLI grammar; the operator/control owner can project the
;;; same plan.  No raw group table, decimal capacity, configuration record, or
;;; durable final filename is computed here.

(in-package "ACL2")

(defun fnn-admin-argv-octets (arguments)
  "Marshal raw process words only.  ACL2 rejects non-ASCII, empty, oversized,
or syntactically unsupported requests in `fn-native-admin-plan'."
  (mapcar (lambda (argument) (fnn-ascii-octet-list argument)) arguments))

(defun fnn-admin-plan (arguments)
  (fnn-core 'fn-native-admin-host-plan (fnn-admin-argv-octets arguments)))

(defun fnn-admin-plan-acceptedp (plan)
  (eq (fnn-core 'fn-native-admin-host-status plan) :accepted))

(defun fnn-admin-plan-reason (plan)
  (fnn-core 'fn-native-admin-host-reason plan))

(defun fnn-admin-config-record-name (generation)
  (let ((name (fnn-core 'fn-native-admin-host-config-name generation)))
    (unless (and (stringp name) (= (length name) 12)
                 (null (position #\/ name)))
      (fnn-fault "ACL2 returned an invalid configuration record name"))
    name))

(defun fnn-admin-clock-monotonic ()
  ; Clock readings are host observations; the record codec owns their uint32
  ; admissibility.  This projection keeps the raw clock within that wire field.
  (mod (floor (fnn-now) internal-time-units-per-second) 4294967296))

(defun fnn-admin-clock-wall ()
  (mod (get-universal-time) 4294967296))

(defun fnn-admin-reconfigure (plan)
  "Invoke the existing ACL2 configuration transaction constructor.
On :ok it returns the exact record octets the core admitted; on refusal it
returns NIL and the core's named reason."
  (let* ((kind (fnn-core 'fn-native-admin-host-kind plan))
         (name (fnn-core 'fn-native-admin-host-name plan))
         (capacity (fnn-core 'fn-native-admin-host-capacity plan))
         (status (fnn-core-state 'fn-store-cfg-reconfigure
                                 kind (or name nil) capacity
                                 (fnn-admin-clock-monotonic)
                                 (fnn-admin-clock-wall))))
    (if (eq status :ok)
        (let ((octets (fnn-core-state 'fn-store-cfg-last-octets)))
          (unless (fnn-octet-list-p octets)
            (fnn-fault "ACL2 accepted an administrative record without octets"))
          octets)
      (values nil (fnn-core-state 'fn-store-cfg-last-reason)))))

(defun fnn-admin-candidate-openp (records frontier config-records)
  "The byte decoders are the existing host/store-node boundary; candidate
validity itself is the ACL2 logical fn-native-admin-candidate-openp function."
  (eq (fnn-core-state 'fn-store-cfg-candidate-openp
                      (mapcar #'fnn-octet-list records) frontier
                      (mapcar #'fnn-octet-list config-records))
      t))

(defun fnn-admin-stage-path (store)
  ; A stage is not a durable namespace.  The final name comes only from the
  ; ACL2 codec above and the shared publisher provides every durable barrier.
  (fnn-join (fnn-staging store)
            (format nil ".admin-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))

(defun fnn-admin-publish (store records record generation)
  (let* ((name (fnn-admin-config-record-name generation))
         (directory (fnn-config-dir store))
         (final (fnn-join directory name))
         (candidate-config-records (append (fnn-config-records store)
                                           (list (fnn-octets record)))))
    ; `config/' is created and parent-fenced by initialization.  Standalone
    ; administration never creates it, so fn-jpub's final-directory barrier is
    ; exactly the committed config namespace barrier, without a second raw
    ; publication sequence.
    (when (fnn-lstat final)
      (fnn-fault "configuration generation is already occupied: ~a" name))
    (unless (fnn-admin-candidate-openp records (fnn-store-frontier store)
                                       candidate-config-records)
      (fnn-refuse "ACL2 refused candidate configuration history"))
    (case (fnn-immutable-publish-effect
           (fnn-core 'fn-jpub-host-initial t)
           (fnn-admin-stage-path store) final directory (fnn-octets record)
           :cleanup-directory (fnn-staging store))
      (:durable name)
      (:refused (fnn-refuse "configuration record publication refused"))
      (:uncertain (fnn-indeterminate "configuration record publication is uncertain"))
      (otherwise (fnn-fault "ACL2 returned invalid configuration publication outcome")))))

(defun fnn-admin-reopen (root expected-generation)
  "A durable outcome is accepted only after a fresh ordinary open sees it."
  (multiple-value-bind (reopened records) (fnn-open-live-store root nil)
    (declare (ignore records))
    (unwind-protect
         (if (= (fnn-store-config-generation reopened) expected-generation)
             t
           (fnn-fault "reopened configuration generation differs from publication"))
      (fnn-store-close reopened))))

(defun fnn-admin-execute (root plan)
  "Private callback for the one public native operator entry.
PLAN is the exact ACL2 `fn-native-admin-plan' result; no command words reach
this executor.  The defensive status check keeps a malformed raw caller from
turning a refusal into a physical mutation."
  (unless (fnn-admin-plan-acceptedp plan)
    (fnn-refuse "administrative request refused: ~a" (fnn-admin-plan-reason plan)))
    ; fnn-open-live-store(... t) takes the same nonblocking exclusive lock as
    ; owner.  A live owner therefore reaches the explicit `already locked'
    ; refusal; this command never starts another owner.
    (let ((store nil))
      (unwind-protect
           (multiple-value-bind (opened records) (fnn-open-live-store root t)
             (setq store opened)
             (fnn-require-writer store)
             (multiple-value-bind (record reason) (fnn-admin-reconfigure plan)
               (unless record
                 (fnn-refuse "administrative configuration refused: ~a" reason))
               (let* ((generation (+ 1 (fnn-store-config-generation store))
                      (name (fnn-admin-publish store records record generation)))
                 ; Close the exclusive descriptor before the independent
                 ; recovery open; it makes the reopen evidence a real new lock
                 ; acquisition rather than an in-process replay shortcut.
                 (fnn-store-close store)
                 (setq store nil)
                 (fnn-admin-reopen root generation)
                 (fnn-out "configured generation=~d record=~a" generation name)
                 +fnn-exit-ok+)))
        (when store (fnn-store-close store)))))

(defun fnn-command-admin (root arguments)
  "Unregistered internal test helper.  Production reaches fnn-admin-execute
only through the ACL2 native-operator action plan."
  (fnn-admin-execute root (fnn-admin-plan arguments)))
