;;; Native administrative configuration executor.
;;;
;;; This internal verb has one job: execute an ACL2-native-admin plan while
;;; holding the store's existing exclusive writer lock.  It deliberately does
;;; receives public CLI grammar only through the operator's ACL2 plan. No raw
;;; group/peer table, port/default, decimal capacity, configuration record, or
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
  ;; The wall reading is DTN seconds, the unit of the live owner's
  ;; configuration stamps (books/owner-config.lisp `fn-ocfg-config-stamp').
  ;; It was get-universal-time (seconds since 1900), so an offline record's
  ;; stamp was 3155673600 s ahead of a live one's (PKT-665, 2026-09-27).
  (let ((result (fnn-core 'fn-native-admin-host-clock-observation
                          (floor (fnn-now) internal-time-units-per-second)
                          (floor (fnn-owner-wall-milliseconds) 1000))))
    (unless (eq (fnn-core 'fn-native-admin-host-clock-status result) :accepted)
      (fnn-refuse "ACL2 refused an unrepresentable clock observation"))
    (fnn-core 'fn-native-admin-host-clock-stamp result)))

(defun fnn-admin-reconfigure (plan stamp)
  "Invoke the existing ACL2 configuration transaction constructor.
On :ok it returns the exact record octets the core admitted; on refusal it
returns NIL and the core's named reason."
  (let* ((status
           (fnn-core-state
            'fn-native-admin-host-apply plan
            (fnn-core 'fn-native-admin-host-clock-monotonic stamp)
            (fnn-core 'fn-native-admin-host-clock-wall stamp))))
    (if (eq status :ok)
        (let ((octets (fnn-core-state 'fn-store-cfg-last-octets)))
          (unless (fnn-octet-list-p octets)
            (fnn-fault "ACL2 accepted an administrative record without octets"))
          octets)
      (values nil (fnn-core-state 'fn-store-cfg-last-reason)))))

(defun fnn-admin-lock-observation (store)
  "Whether STORE holds the exclusive writer lock: the store was opened writable
and its lock descriptor is live.  This is an observation, not a decision;
`fn-native-admin-publication-authorize' refuses `:lock' when it is NIL."
  (and (fnn-store-writable store) (fnn-store-lock-fd store) t))

(defun fnn-admin-authorize (store records config-records record observed-names)
  "The one ACL2 publication operation binds the observed lock, occupied-name
set, exact record, candidate replay/open result and generated final name."
  (let ((result (fnn-core
                 'fn-store-cfg-native-admin-authorize
                 (mapcar #'fnn-octet-list records) (fnn-store-frontier store)
                 (mapcar #'fnn-octet-list config-records) (fnn-octet-list record)
                 (fnn-admin-lock-observation store) (mapcar (lambda (name) (fnn-octet-list (fnn-string-octets name)))
                           observed-names)
                 ;; The profile the store opened; ACL2 reads its
                 ;; max-config-generations (D27, PRF-102).
                 (fnn-store-config store))))
    (if (eq (fnn-core 'fn-native-admin-host-publication-status result) :accepted)
        result
      (fnn-refuse "ACL2 refused administrative publication: ~a"
                  (fnn-core 'fn-native-admin-host-publication-reason result)))))

(defun fnn-admin-authorize-owner (store config-records record observed-names)
  "A live owner's authorization: ACL2's fn-owner-cfg-native-admin-authorize
from the owner's carried state (books/config-owner-live-authorize.lisp
fn-olau-authorize, PKT-837), equal to the decision fnn-admin-authorize asks
over a history it reads (fn-olau-authorize-is-the-replayed-authorization)."
  (let ((result (fnn-owner-core
                 'fn-owner-cfg-native-admin-authorize
                 (mapcar #'fnn-octet-list config-records) (fnn-octet-list record)
                 (fnn-admin-lock-observation store)
                 (mapcar (lambda (name) (fnn-octet-list (fnn-string-octets name)))
                         observed-names)
                 (fnn-store-config store))))
    (if (eq (fnn-core 'fn-native-admin-host-publication-status result) :accepted)
        result
      (fnn-refuse "ACL2 refused administrative publication: ~a"
                  (fnn-core 'fn-native-admin-host-publication-reason result)))))

(defun fnn-admin-authorize-carried (store config-records record observed-names)
  "The offline request's authorization from the open's carried fold
(PKT-510 (1)): ACL2's fn-store-cfg-native-admin-authorize-carried, which is
fn-store-cfg-native-admin-authorize over the history the open replayed
(books/config-carried-open.lisp
fn-cfgc-cvec-native-admin-authorize-is-the-replayed-authorization) without
replaying it again.  When ACL2 answers NIL (no carried open, or a
configuration history that is not the open's) the request authorizes over the
history it read, as before."
  (let ((result (fnn-core-state
                 'fn-store-cfg-native-admin-authorize-carried
                 (fnn-store-frontier store)
                 (mapcar #'fnn-octet-list config-records) (fnn-octet-list record)
                 (fnn-admin-lock-observation store)
                 (mapcar (lambda (name) (fnn-octet-list (fnn-string-octets name)))
                         observed-names)
                 (fnn-store-config store))))
    (cond ((null result) nil)
          ((eq (fnn-core 'fn-native-admin-host-publication-status result) :accepted)
           result)
          (t (fnn-refuse "ACL2 refused administrative publication: ~a"
                         (fnn-core 'fn-native-admin-host-publication-reason result))))))

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

(defun fnn-admin-verify-under-lock (store record authorization)
  "Read the just-published configuration record back while this command still
owns the writer lock, and let ACL2 compare it with the authorized octets.
A later administrator cannot advance the generation between publication and
this observation.  The reopen this replaces (PKT-601 (2)) is decided already:
the authorization accepted only a candidate whose open over the observed
history and RECORD succeeds, and when the file holds RECORD at the named
generation the open of the history the directory now holds is that candidate
(books/config-carried-open.lisp fn-cfgc-readback-verified-is-the-reopen).
The immutable publisher's :DURABLE result is already this command's accepted
persistence outcome, so an independent diagnostic failure is reported
without retroactively recasting that durable result as a refusal or
uncertainty."
  (handler-case
      (let* ((name (fnn-core 'fn-native-admin-host-publication-name authorization))
             (generation (fnn-core 'fn-native-admin-host-publication-generation
                                   authorization))
             (path (fnn-join (fnn-config-dir store) name)))
        (fnn-check-regular path)
        (let ((word (fnn-core 'fn-cfgc-readback-verdict
                              (fnn-octet-list
                               (fnn-read-regular-bounded path +fnn-config-record-bytes+))
                              record generation (fnn-store-frontier store))))
          (if (eq word :verified)
              :verified
            (progn
              (setf (fnn-store-fenced store) t)
              word))))
    (error ()
      (setf (fnn-store-fenced store) t)
      :unavailable)))

(defun fnn-owner-refresh-config-cache (service expected-generation)
  "Install one coherent native projection of the ACL2 owner's durable config.

The Store bridge is a separate ACL2 global and does not follow live owner
reconfiguration.  A failed observation after publication fences this writer;
it cannot continue with its old group-code table."
  (let ((store (fnn-owner-service-store service)))
    (handler-case
        (let* ((generation (fnn-owner-core 'fn-owner-config-generation))
               (served (fnn-decode-joined-names
                        (fnn-owner-core 'fn-owner-config-served)))
               (domain (fnn-decode-joined-names
                        (fnn-owner-core 'fn-owner-domain))))
          (unless (and (integerp generation) (>= generation 0)
                       (= generation expected-generation))
            (fnn-fault "owner configuration generation changed after publication"))
          (setf (fnn-store-config-generation store) generation
                (fnn-store-config-served store) served
                (fnn-store-config-domain store) domain)
          :refreshed)
      (error (e)
        (setf (fnn-store-fenced store) t)
        (fnn-indeterminate
         "durable configuration needs owner cache recovery: ~a" e)))))

;; lane prepare-served: ACL2's un-stage of a configuration record whose
;; publication was refused before anything was written (host/owner-host.lisp
;; fn-owner-reconfigure-unstage: books/owner-prepare-served.lisp
;; fn-psrv-unstage).  The caller holds the owner mutex.
(defun fnn-owner-reconfigure-unstage ()
  (let ((word (fnn-owner-action 'fn-owner-reconfigure-unstage)))
    (unless (member word '(:unstaged :none))
      (fnn-fault "owner returned a malformed un-stage word ~a" word))
    word))

(defun fnn-owner-live-reconfigure-locked (service stage)
  "Stage, publish and complete one ACL2-constructed configuration record.

The caller holds the owner mutex.  STAGE is called with a private logical
connection id and answers the owner's ConfigResult (books/owner-results.lisp,
checked by fnn-owner-result); only :staged continues, and its octets are the
one configuration record to publish.
Answers :accepted once the record is durable and the owner installed it, or
:refused before any publication."
  ;; Reuse the model's existing generation pin: a private logical
  ;; connection is opened and closed under this mutex without acquiring
  ;; a socket.  Its pin is therefore the current generation checked by
  ;; fn-ocfg-reconfig-refusal; raw Lisp never supplies that decision.
  ;; `fn-owner-open' answers the new connection's integer id, or NIL
  ;; when the model refused the open, as the socket path reads it
  ;; (host/native/owner.lisp).  It is not an action keyword: through
  ;; `fnn-owner-action' every live request faulted here and stopped the
  ;; owner (the dabebb84 matrix run, V0-CFG-LIVE).
  (let ((record nil))
  (let* ((cid (let ((opened (fnn-owner-core 'fn-owner-open)))
                (unless (or (null opened) (and (integerp opened) (>= opened 0)))
                  (fnn-fault "owner returned a malformed connection id"))
                opened))
         (result (and (integerp cid) (funcall stage cid)))
         (staged (and result (fnn-core 'fn-ores-config-word result))))
    (when (integerp cid) (fnn-owner-action 'fn-owner-close cid))
    (unless (eq staged :staged)
      ;; The second value is the staging step's reason, a field of its
      ;; ConfigResult (fn-cfg-delta-reason's word, :no-such-grant and the
      ;; rest), or NIL when nothing was staged.
      (return-from fnn-owner-live-reconfigure-locked
        (values :refused
                (and (eq staged :refused)
                     (fnn-core 'fn-ores-config-reason result)))))
    (setq record (fnn-octets (fnn-core 'fn-ores-config-octets result))))
  ;; PKT-827 (b), PRF-287: authorized from the owner's carried state before
  ;; anything is published: ACL2 answers whether the staged record applies to
  ;; the carried node and configuration (host/owner-host.lisp
  ;; fn-owner-reconfigure-authorizedp).  A refusal here is a refusal before
  ;; publication, as fnn-admin-authorize's below.
  (unless (fnn-owner-core 'fn-owner-reconfigure-authorizedp)
    (fnn-owner-reconfigure-unstage)
    (fnn-refuse "ACL2 refused administrative publication: the staged record does not apply to the carried configuration"))
  (let ((store (fnn-owner-service-store service)))
    (multiple-value-bind (published ignored-name)
        ;; lane prepare-served: a refusal here is before anything was written
        ;; (the candidate open's refusal, or the immutable publisher's
        ;; :refused), so the staged record is dropped (ACL2's
        ;; fn-psrv-unstage) and the refusal passes on.  An uncertain
        ;; publication or a fault is not a refusal: the owner keeps the
        ;; stage, the store is fenced, and recovery decides.
        (handler-case
            (let* ((observation (fnn-config-record-observation store))
                   (config-records (fnn-config-records-from-observation observation))
                   (authorization
                     ;; Over the state the owner carries (PKT-837, dev's
                     ;; PKT-840): no Store record read, no history replayed.
                     (fnn-admin-authorize-owner store config-records record
                                                (mapcar #'car observation))))
              (fnn-admin-publish store record authorization))
          (fnn-store-error (e)
            (when (eq (type-of e) 'fnn-store-error)
              (fnn-owner-reconfigure-unstage))
            (error e)))
      (declare (ignore ignored-name))
      (unless (eq (fnn-owner-action
                   'fn-owner-reconfigure-complete published)
                  :durable)
        (fnn-indeterminate
         "owner rejected a durably published configuration"))
      (fnn-owner-refresh-config-cache service published)
      (fnn-owner-feed-refresh-configuration service)
      :accepted))))

;;; PRF-164 (PKT-439): the owner's side of XREDEEM.  The connection CID
;;; holds (books/nntp-auth.lisp fn-auth-redeem-waitp) after its read; the
;;; caller, host/native/owner.lisp fnn-owner-redeem-quantum, holds the owner
;;; mutex in a quantum of its own, of ACL2's publication class (never while a
;;; batch is in flight; PKT-828 open item 2).  The NNTP session
;;; reaches the publication in-process, the way peer accept does
;;; (host/native/peer-invite.lisp), not over the control socket: no control
;;; request kind is used.
(defun fnn-owner-account-redeem (service cid)
  "Plan, publish, then answer: 281 only after the redeem record is durable.

Returns the ACL2-rendered reply octets for CID."
  (let* ((salt (fnn-csprng-octets (fnn-core 'fn-acct-host-salt-octets)
                                  "credential salt"))
         (bound (fnn-profile-nat 'fn-store-profile-max-credentials
                                 (fnn-owner-service-store service)))
         (published
           (fnn-owner-live-reconfigure-locked
            service
            (lambda (pcid)
              (fnn-owner-result 'fn-ores-config-result-p
                                'fn-acct-host-owner-redeem-stage
                                pcid cid salt bound)))))
    (unless (member published '(:accepted :refused))
      (fnn-fault "owner returned a malformed publication word"))
    ;; The model's crash cut after fn-ocl-publish's root barrier and before
    ;; the reply (books/accounts.lisp
    ;; fn-acct-redeem-bounded-plan-after-its-redeem-is-bound); a developer
    ;; image dies here on request.
    (when (and (eq published :accepted)
               (fnn-developer-selector "FN_ACCOUNT_TEST_STOP_AFTER_PUBLISH"))
      (fnn-err "account redeem: developer stop after the publication")
      (sb-ext:exit :code 137 :abort t))
    (fnn-log-line (fnn-owner-core 'fn-acct-host-owner-redeem-log-line published))
    (let ((word (fnn-owner-core 'fn-acct-host-owner-redeem-word published)))
      (unless (member word '(:bound :refused))
        (fnn-fault "owner returned a malformed redeem word"))
      (unless (eq (fnn-owner-action 'fn-owner-account-outcome cid word) :ok)
        (fnn-fault "owner rejected the redeem outcome"))
      (fnn-owner-octets-global 'fn-owner-output))))

(defun fnn-owner-live-admin-serialized (service argv)
  "Publish one ACL2-planned configuration mutation through the live owner."
  (fnn-owner-serialized
   service nil
   (lambda ()
     ;; PKT-453 (a): a refusal answers (:reason :refused REASON), the
     ;; plan's reason or the staging step's, both ACL2's.
     (let ((plan (fnn-core 'fn-native-admin-host-plan argv)))
       (unless (fnn-admin-plan-acceptedp plan)
         (return-from fnn-owner-live-admin-serialized
           (list :reason :refused (fnn-admin-plan-reason plan))))
       (multiple-value-bind (word reason)
           (fnn-owner-live-reconfigure-locked
            service
            (lambda (cid)
              (fnn-owner-result 'fn-ores-config-result-p
                                'fn-native-admin-host-owner-reconfigure cid plan)))
         (if (eq word :refused) (list :reason :refused reason) word))))))

(defun fnn-admin-publish-record (store record)
  "Authorize, publish and read back one configuration RECORD (ACL2's octets)
on STORE, opened writable under the exclusive lock: the offline
administrative path (fnn-admin-execute) and the reclaim's instant
(host/native/checkpoint.lisp fnn-log-reclaim-steps) both take it.  Answers
(values GENERATION NAME VERIFICATION).  The durable publisher is the
acceptance boundary; the read-back runs under the retained exclusive lock:
releasing it before the readback would let a later administrator make this
already durable publication appear to fail merely by advancing the history."
  (let* ((observation (fnn-config-record-observation store))
         (names (mapcar #'car observation))
         (config-records (fnn-config-records-from-observation observation))
         (authorization
           (or (fnn-admin-authorize-carried store config-records record names)
               (fnn-admin-authorize store (fnn-history-records store)
                                    config-records record names))))
    (multiple-value-bind (generation name) (fnn-admin-publish store record authorization)
      (values generation name
              (fnn-admin-verify-under-lock store record authorization)))))

(defun fnn-admin-query (root plan)
  "Execute one read-only ACL2 configuration query against ROOT.

`fn-native-admin-result-queryp' is what selects this executor, so the host
does not decide which plan kinds are safe to read.  The store is opened
non-writable, which takes the shared writer lock and publishes nothing: a
live owner therefore refuses this command the way it refuses `status', and
this path can neither mutate the configuration nor take the lock from it."
  (unless (fnn-admin-plan-acceptedp plan)
    (fnn-refuse "administrative request refused: ~a" (fnn-admin-plan-reason plan)))
  (multiple-value-bind (store ignored-records) (fnn-open-live-store root nil)
    (declare (ignore ignored-records))
    (unwind-protect
         (let ((report (fnn-core-state 'fn-native-admin-host-query-report plan)))
           (unless (fnn-octet-list-p report)
             (fnn-fault "ACL2 returned a malformed configuration listing"))
           (when report
             (write-sequence (fnn-octets report) *fnn-stdout*)
             (finish-output *fnn-stdout*))
           +fnn-exit-ok+)
      (fnn-store-close store))))

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
           (multiple-value-bind (opened count) (fnn-open-live-store root t)
             (declare (ignore count))
             (setq store opened)
             (fnn-require-writer store)
             (multiple-value-bind (record reason) (fnn-admin-reconfigure plan (fnn-admin-clock-plan))
               (unless record
                 (fnn-refuse "administrative configuration refused: ~a" reason))
               (multiple-value-bind (generation name verification)
                   (fnn-admin-publish-record store record)
                 (fnn-out "configured generation=~d record=~a verification=~a"
                          generation name verification)
                 +fnn-exit-ok+)))
        (when store (fnn-store-close store)))))
