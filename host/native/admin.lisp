;;; Native administrative configuration executor.
;;;
;;; This internal verb has one job: execute an ACL2-native-admin plan while
;;; holding the store's existing exclusive writer lock.  It deliberately does
;;; receives public CLI grammar only through the operator's ACL2 plan. No raw
;;; group/peer table, port/default, decimal capacity, configuration record, or
;;; durable final filename is computed here.

(in-package "ACL2")

(defun fnn-admin-plan-acceptedp (plan)
  (eq (fnn-core 'fn-native-admin-host-status plan) :accepted))

(defun fnn-admin-plan-reason (plan)
  (fnn-core 'fn-native-admin-host-reason plan))

(defun fnn-admin-clock-plan ()
  "Raw Lisp observes clock values but does not coerce or wrap them.  ACL2
builds the record stamp and refuses values that its durable schema cannot
represent."
  ;; Both readings are MILLISECONDS, the owner clock's unit and the
  ;; configuration record stamp's (books/clock-unit.lisp; PRF-378): the
  ;; monotonic reading as fnn-owner-monotonic-ms reads it, the wall reading
  ;; DTN milliseconds.  Whether the wall reading is usable is ACL2's
  ;; (fnn-owner-wall-milliseconds's second value, books/owner-time-model.lisp
  ;; fn-otm-wall-reading) and the stamp keeps it: an unreadable wall clock
  ;; stamps a record with no wall claim, and a stopped `account invite'
  ;; refuses :no-clock (PRF-379).  It was floored to seconds and the claim
  ;; dropped, so such a record claimed 2000-01-01.
  (multiple-value-bind (wall has-wall) (fnn-owner-wall-milliseconds)
    (let ((result (fnn-core 'fn-native-admin-host-clock-observation
                            (floor (* (get-internal-real-time) 1000)
                                   internal-time-units-per-second)
                            wall has-wall)))
      (unless (eq (fnn-core 'fn-native-admin-host-clock-status result) :accepted)
        (fnn-refuse "ACL2 refused an unrepresentable clock observation"))
      (fnn-core 'fn-native-admin-host-clock-stamp result))))

(defun fnn-admin-reconfigure (plan stamp)
  "Invoke the existing ACL2 configuration transaction constructor with the
record stamp ACL2 built (fnn-admin-clock-plan).  On :ok it returns the exact
record octets the core admitted; on refusal it returns NIL and the core's
named reason."
  (let* ((status (fnn-core-state 'fn-native-admin-host-apply plan stamp)))
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

(defun fnn-owner-compaction-request (service)
  "PKT-868: the operator's compaction request on the running owner.  ACL2
answers it (host/owner-host.lisp fn-owner-sco-request, books/owner-compact-
request.lisp fn-ock-request-word) under the owner mutex, from the free space
read before (statvfs is I/O: never under the mutex); a request it answers
:requested starts the owner's publication now, off the mutex
(fnn-owner-maybe-publish: the spare, the capture, the bounded batches, the
install, the drop).  The reply names the word; :blocked is a refusal (a
deferral stands, and `status' names it)."
  (let* ((free (fnn-disk-free-octets (fnn-owner-service-store service)))
         (word (fnn-owner-serialized
                service nil
                (lambda ()
                  (fnn-owner-core 'fn-owner-sco-request
                                  (fnn-checkpoint-budget-test-override nil) free)))))
    (unless (member word '(:requested :coalesced :nothing-to-compact :blocked))
      (fnn-fault "owner returned a malformed compaction answer ~a" word))
    (fnn-err "COMPACTION request answer=~(~a~)" word)
    (when (eq word :requested)
      (fnn-owner-maybe-publish service))
    (list :reason (fnn-core 'fn-ock-request-status word) word)))

(defun fnn-owner-inspect-request (service msgid)
  "Row S3: `store inspect ID' on the running owner: the owner's own lookup of
ID (the Message-ID table, O(1)) under the owner mutex, answered as ACL2's
word (books/owner-maintenance-request.lisp fn-omr-inspect-word) with the
status fn-omr-inspect-status decides: accepted when found, refused when
absent.  The client renders the offline report from the word."
  (let* ((octets (fnn-octets (fnn-core 'fn-record-string-octets msgid)))
         (found (fnn-owner-serialized
                 service nil (lambda () (and (fnn-bridge-lookup-found-p octets) t))))
         (word (fnn-core 'fn-omr-inspect-word found)))
    (list :reason (fnn-core 'fn-omr-inspect-status word) word)))
(defun fnn-owner-reclaim-request (service mode)
  "Q16: `store reclaim' on the running owner (books/owner-reclaim.lisp).  ACL2
answers it under the owner mutex (host/owner-host.lisp fn-owner-orc-request):
a dry run the owner runs now, off its mutex, on this control thread
(host/native/owner.lisp fnn-owner-reclaim-dry-run: the capture by pointer,
then the fold over the rows, the classes and the decision), its report in the
owner's log as `store reclaim --dry-run' prints it offline; a pass in flight
answers :in-flight; `--recorded' runs the pass that installs
(fnn-owner-reclaim-pass: :installed, :none, or deferred by name);
`store reclaim' without it is :offline-only until the pass records the
instant live.  The reply names the word."
  (let* ((free (fnn-disk-free-octets (fnn-owner-service-store service)))
         (word (fnn-owner-serialized
                service nil
                (lambda ()
                  (fnn-owner-core 'fn-owner-orc-request mode
                                  (fnn-checkpoint-budget-test-override nil) free)))))
    (unless (member word '(:requested :in-flight :queued :blocked :no-recorded-instant
                           :offline-only))
      (fnn-fault "owner returned a malformed reclaim answer ~a" word))
    (fnn-err "RECLAIM request mode=~(~a~) answer=~(~a~)" mode word)
    (when (eq word :requested)
      (setq word (if (eq mode :dry-run)
                     (fnn-owner-reclaim-dry-run service free)
                   ;; Q16 (a): `--recorded' installs (fnn-owner-reclaim-pass)
                   (fnn-owner-reclaim-pass service free))))
    (list :reason (fnn-core 'fn-owner-orc-request-status word) word)))

;;; Row S1 (books/limits-live.lisp, PRF-940): `policy set
;;; max-transactions|max-history-octets|max-article-octets N'.  ACL2 decides
;;; the change (fn-lim-decide) before anything is staged, over the profile
;;; the configuration history records (fn-store-lim-effective), the store's
;;; use, the reservation this process runs in and the launcher's
;;; observations (heap-reservation.lisp fn-heap-status-decide): applied now,
;;; recorded for the next start (no data moved), or refused by name with the
;;; number.  The host observes, publishes and installs; the words are ACL2's.

(defun fnn-lim-plan-p (plan)
  (and (fnn-admin-plan-acceptedp plan)
       (eq (fnn-core 'fn-native-admin-result-kind plan) :set-store-limit)))

(defun fnn-lim-plan-field (plan)
  (fnn-core 'fn-record-octets-string (fnn-core 'fn-native-admin-result-name plan)))

(defun fnn-lim-plan-n (plan)
  (fnn-nat (fnn-core 'fn-native-admin-result-capacity plan)))

(defun fnn-lim-recorded-profile (store)
  "The profile STORE's configuration history records: the sealed one under
every :set-limit row (ACL2's fn-store-lim-effective over the records)."
  (let ((observation (fnn-config-record-observation store)))
    (fnn-core 'fn-store-lim-effective (fnn-store-sealed-config store)
              (mapcar #'fnn-octet-list (mapcar #'cdr observation)))))

(defun fnn-lim-decision (store plan values use run-mb core observations)
  (fnn-core 'fn-lim-decide (fnn-lim-plan-field plan) (fnn-lim-plan-n plan)
            values use run-mb core +fnn-gc-nursery-octets+ observations
            (fnn-heap-history-observation (fnn-store-root store) values)))

(defun fnn-lim-reason (plan decision store)
  (fnn-core 'fn-lim-decision-reason (fnn-lim-plan-field plan) (fnn-lim-plan-n plan)
            decision (fnn-store-open-ms store)))

(defun fnn-lim-line (plan decision store)
  (fnn-core 'fn-lim-decision-line (fnn-lim-plan-field plan) (fnn-lim-plan-n plan)
            decision (fnn-store-open-ms store)))

(defun fnn-owner-limit-serialized (service plan)
  "The live owner's limit change: decided under the owner mutex (the
configuration history does not move under it), published through the
ordinary live reconfiguration, and on :applied served at once."
  (let* ((store (fnn-owner-service-store service))
         ;; The machine and image observations, off the mutex.
         (core (fnn-heap-image-observation))
         (observations (fnn-heap-observations))
         (run-mb (floor (sb-ext:dynamic-space-size) 1048576)))
    (fnn-owner-serialized
     service nil
     (lambda ()
       (let* ((values (fnn-lim-recorded-profile store))
              (use (fnn-owner-core 'fn-owner-limit-use))
              (d (fnn-lim-decision store plan values use run-mb core observations)))
         (fnn-err "LIMIT ~a" (fnn-lim-line plan d store))
         (if (not (eq (fnn-core 'fn-lim-decision-status d) :accepted))
             (list :reason :refused (fnn-lim-reason plan d store))
           (multiple-value-bind (word reason)
               (fnn-owner-live-reconfigure-locked
                service
                (lambda (cid)
                  (fnn-owner-result 'fn-ores-config-result-p
                                    'fn-native-admin-host-owner-reconfigure cid plan)))
             (cond
               ((eq word :refused) (list :reason :refused reason))
               (t
                (when (eq (first d) :applied)
                  ;; The profile every later open computes from the history
                  ;; this record ended (fn-lim-effective-of-append-record).
                  (let ((served (fnn-core 'fn-lim-apply-row values
                                          (fnn-lim-plan-field plan) (fnn-lim-plan-n plan))))
                    (unless (eq (fnn-owner-core 'fn-owner-apply-limit-profile served)
                                :installed)
                      (fnn-indeterminate
                       "owner refused a durably recorded limit's profile"))
                    (setf (fnn-store-config store) served)))
                (list :reason :accepted (fnn-lim-reason plan d store)))))))))))

(defun fnn-admin-execute-limit (store plan)
  "The offline limit change: no process holds a reservation (run-mb 0), so an
accepted change is recorded for the next start.  Prints ACL2's line."
  (let* ((values (fnn-lim-recorded-profile store))
         (use (fnn-core-state 'fn-store-lim-use))
         (d (fnn-lim-decision store plan values use 0
                              (fnn-heap-image-observation) (fnn-heap-observations)))
         (line (fnn-lim-line plan d store)))
    (unless (eq (fnn-core 'fn-lim-decision-status d) :accepted)
      (fnn-refuse "~a" line))
    (multiple-value-bind (record reason) (fnn-admin-reconfigure plan (fnn-admin-clock-plan))
      (unless record
        (fnn-refuse "administrative configuration refused: ~a" reason))
      (multiple-value-bind (generation name verification)
          (fnn-admin-publish-record store record)
        (fnn-out "configured generation=~d record=~a verification=~a"
                 generation name verification)
        (fnn-out "~a" line)
        +fnn-exit-ok+))))

(defun fnn-owner-live-admin-serialized (service argv)
  "Publish one ACL2-planned configuration mutation through the live owner,
or answer the one owner request an admin vector carries (PKT-868: the
compaction request; row S3: the inspect request; Q16: the reclaim request;
ACL2's fn-native-admin-result-owner-requestp, -inspect-msgid and
-reclaim-mode)."
  (let ((plan (fnn-core 'fn-native-admin-host-plan argv)))
    (when (fnn-core 'fn-native-admin-host-owner-requestp plan)
      (let ((mode (fnn-core 'fn-native-admin-host-reclaim-mode plan))
            (msgid (fnn-core 'fn-native-admin-result-inspect-msgid plan)))
        (return-from fnn-owner-live-admin-serialized
          (if (or mode msgid)
              (if mode
                  (fnn-owner-reclaim-request service mode)
                (fnn-owner-inspect-request service msgid))
            (fnn-owner-compaction-request service))))))
  (let ((plan (fnn-core 'fn-native-admin-host-plan argv)))
    (when (fnn-lim-plan-p plan)
      (return-from fnn-owner-live-admin-serialized
        (fnn-owner-limit-serialized service plan))))
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
             (when (fnn-lim-plan-p plan)
               (return-from fnn-admin-execute (fnn-admin-execute-limit store plan)))
             (multiple-value-bind (record reason) (fnn-admin-reconfigure plan (fnn-admin-clock-plan))
               (unless record
                 (fnn-refuse "administrative configuration refused: ~a" reason))
               (multiple-value-bind (generation name verification)
                   (fnn-admin-publish-record store record)
                 (fnn-out "configured generation=~d record=~a verification=~a"
                          generation name verification)
                 +fnn-exit-ok+)))
        (when store (fnn-store-close store)))))
