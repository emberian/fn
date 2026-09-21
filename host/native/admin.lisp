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

(defun fnn-admin-clock-plan ()
  "Raw Lisp observes clock values but does not coerce or wrap them.  ACL2
builds the record stamp and refuses values that its durable schema cannot
represent."
  (let ((result (fnn-core 'fn-native-admin-host-clock-observation
                          (floor (fnn-now) internal-time-units-per-second)
                          (get-universal-time))))
    (unless (eq (fnn-core 'fn-native-admin-host-clock-status result) :accepted)
      (fnn-refuse "ACL2 refused an unrepresentable clock observation"))
    (fnn-core 'fn-native-admin-host-clock-stamp result)))

(defun fnn-admin-reconfigure (plan stamp)
  "Invoke the existing ACL2 configuration transaction constructor.
On :ok it returns the exact record octets the core admitted; on refusal it
returns NIL and the core's named reason."
  (let* ((kind (fnn-core 'fn-native-admin-host-kind plan))
         (name (fnn-core 'fn-native-admin-host-name plan))
         (capacity (fnn-core 'fn-native-admin-host-capacity plan))
         (status (fnn-core-state 'fn-store-cfg-reconfigure
                                 kind (or name nil) capacity
                                 (fnn-core 'fn-native-admin-host-clock-monotonic stamp)
                                 (fnn-core 'fn-native-admin-host-clock-wall stamp))))
    (if (eq status :ok)
        (let ((octets (fnn-core-state 'fn-store-cfg-last-octets)))
          (unless (fnn-octet-list-p octets)
            (fnn-fault "ACL2 accepted an administrative record without octets"))
          octets)
      (values nil (fnn-core-state 'fn-store-cfg-last-reason)))))

(defun fnn-admin-authorize (store records config-records record observed-names)
  "The one ACL2 publication operation binds the observed lock, occupied-name
set, exact record, candidate replay/open result and generated final name."
  (let ((result (fnn-core-state
                 'fn-store-cfg-native-admin-authorize
                 (mapcar #'fnn-octet-list records) (fnn-store-frontier store)
                 (mapcar #'fnn-octet-list config-records) (fnn-octet-list record)
                 t (mapcar (lambda (name) (fnn-octet-list (fnn-string-octets name)))
                           observed-names))))
    (if (eq (fnn-core 'fn-native-admin-host-publication-status result) :accepted)
        result
      (fnn-refuse "ACL2 refused administrative publication: ~a"
                  (fnn-core 'fn-native-admin-host-publication-reason result)))))

(defun fnn-admin-stage-path (store)
  ; Reuse the admitted `.stage-' ephemeral namespace.  Recovery's ACL2-owned
  ; sweep recognizes this exact prefix; administrative publication has no
  ; separate residue grammar.  The final name remains ACL2's config codec.
  (fnn-join (fnn-staging store)
            (format nil ".stage-~d-~a" (sb-posix:getpid) (fnn-random-hex 12))))

(defun fnn-admin-publish (store record authorization)
  (let* ((generation (fnn-core 'fn-native-admin-host-publication-generation authorization))
         (name (fnn-core 'fn-native-admin-host-publication-name authorization))
         (directory (fnn-config-dir store))
         (final (fnn-join directory name)))
    (unless (and (integerp generation) (>= generation 0)
                 (stringp name) (= (length name) 12) (null (position #\/ name)))
      (fnn-fault "ACL2 returned an invalid administrative publication plan"))
    (case (fnn-immutable-publish-effect
           (fnn-core 'fn-native-admin-host-publication-jpub authorization)
           (fnn-admin-stage-path store) final directory (fnn-octets record)
           :cleanup-directory (fnn-staging store))
      (:durable (values generation name))
      (:refused (fnn-refuse "configuration record publication refused"))
      (:uncertain (setf (fnn-store-fenced store) t)
                  (fnn-indeterminate "configuration record publication is uncertain"))
      (otherwise (fnn-fault "ACL2 returned invalid configuration publication outcome")))))

(defun fnn-admin-verify-under-lock (store expected-generation)
  "Reconstruct the just-published configuration while this command still owns
the writer lock.  A later administrator cannot advance the generation between
publication and this observation.  The immutable publisher's :DURABLE result
is already this command's accepted persistence outcome, so an independent
diagnostic failure is reported without retroactively recasting that durable
result as a refusal or uncertainty."
  (handler-case
      (progn
        (fnn-bridge-reset)
        (fnn-recover store)
        (if (= (fnn-store-config-generation store) expected-generation)
            :verified
          (progn
            (setf (fnn-store-fenced store) t)
            :generation-mismatch)))
    (error ()
      (setf (fnn-store-fenced store) t)
      :unavailable)))

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
             (multiple-value-bind (record reason) (fnn-admin-reconfigure plan (fnn-admin-clock-plan))
               (unless record
                 (fnn-refuse "administrative configuration refused: ~a" reason))
               (let* ((observation (fnn-config-record-observation store))
                      (names (mapcar #'car observation))
                      (config-records (fnn-config-records-from-observation observation))
                      (authorization (fnn-admin-authorize store records config-records record names)))
                 (multiple-value-bind (generation name) (fnn-admin-publish store record authorization)
                 ; The durable publisher is the acceptance boundary.  Verify
                 ; its candidate under the retained exclusive lock: releasing
                 ; it before an exact-generation reopen would let a later
                 ; administrator make this already durable command appear to
                 ; fail merely by advancing the history.
                 (fnn-out "configured generation=~d record=~a verification=~a"
                          generation name
                          (fnn-admin-verify-under-lock store generation))
                 +fnn-exit-ok+))))
        (when store (fnn-store-close store)))))

(defun fnn-command-admin (root arguments)
  "Unregistered internal test helper.  Production reaches fnn-admin-execute
only through the ACL2 native-operator action plan."
  (fnn-admin-execute root (fnn-admin-plan arguments)))
