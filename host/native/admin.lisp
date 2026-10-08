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

;;; Lane ACTORS (rebuild step 0, the admin pilot).  Every owner quantum in
;;; this file is a declared section (host/native/owner.lisp def-section
;;; fnn-quantum-control: run by the control thread or the startup command,
;;; admitted :live), so ACL2 decides its failure, admission and unwind
;;; (books/failure-scope.lisp) and the fence is installed before the owner
;;; mutex is released.  No function below classifies a condition itself.
;;; The selector raises inside a named section so the natives observe the
;;; boundary (tests/test_native_admin.py AdminSectionBoundaryTests);
;;; production has no injection branch (fnn-developer-selector).

(defparameter +fnn-admin-sections+
  '("compaction" "inspect" "export" "reclaim" "reclaim-instant"
    "limit-carry" "limit" "admin" "login-bindings" "login-bindings-record")
  "This file's owner sections, by the name FN_NATIVE_ADMIN_FAULT uses.")

(defun fnn-admin-test-fault (section)
  "Developer-only FN_NATIVE_ADMIN_FAULT=SECTION:fault|uncertain: raise inside
the named owner section of this file, before its body runs."
  (let ((raw (fnn-developer-selector "FN_NATIVE_ADMIN_FAULT")))
    (when raw
      (let* ((colon (position #\: raw :from-end t))
             (name (and colon (subseq raw 0 colon)))
             (kind (and colon (subseq raw (1+ colon)))))
        (unless (and name (member name +fnn-admin-sections+ :test #'string=)
                     (member kind '("fault" "uncertain") :test #'string=))
          (fnn-fault "invalid FN_NATIVE_ADMIN_FAULT (expected SECTION:fault|uncertain)"))
        (when (string= name section)
          (if (string= kind "fault")
              (fnn-fault "FN_NATIVE_ADMIN_FAULT ~a" raw)
            (fnn-indeterminate "FN_NATIVE_ADMIN_FAULT ~a" raw)))))))

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
                            (fnn-monotonic-ms)
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

(defun fnn-admin-publish-effect (store record authorization)
  "Execute ACL2's publication plan for RECORD: the immutable publication's
steps (open, write, fsync, link, directory fsync, close), which set
*fnn-section-step*; the stage cleanup is queued, and the caller drains it
(fnn-immutable-drain-cleanups) after releasing its locks.  Answers (values OUTCOME GENERATION NAME), OUTCOME the
publication's own classification (books/journal-publish.lisp: :durable,
:refused or :uncertain).  It touches no owner state: the offline command and
a live reconfiguration's window A (fnn-owner-live-reconfigure) both run it."
  (let* ((generation (fnn-core 'fn-native-admin-host-publication-generation authorization))
         (name (fnn-core 'fn-native-admin-host-publication-name authorization))
         (directory (fnn-config-dir store))
         (final (fnn-join directory name)))
    (unless (and (integerp generation) (>= generation 0)
                 (stringp name) (= (length name) 12) (null (position #\/ name)))
      (fnn-fault "ACL2 returned an invalid administrative publication plan"))
    (values (fnn-immutable-publish-deferred
             (fnn-core 'fn-native-admin-host-publication-jpub authorization)
             (fnn-admin-stage-path store) final directory (fnn-octets record)
             :cleanup-directory (fnn-staging store))
            generation name)))

(defun fnn-admin-publish (store record authorization)
  "The offline command's publication: the outcome as a result or a condition."
  (multiple-value-bind (outcome generation name)
      (fnn-admin-publish-effect store record authorization)
    (case outcome
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
reconfiguration.  The caller is inside an owner section
(fnn-owner-live-reconfigure's quanta 2 and 3 are quanta of the caller's
section, the one envelope): a failed observation after the publication leaves this body as
the condition it is, the section's boundary classifies it by its concrete
class (books/failure-scope.lisp fn-fs-classify) and stops the service before
the owner mutex is released, so this writer never continues with its old
group-code table.  The record is durable and the next open replays it:
nothing here is uncertain, and no arm of this function says otherwise (lane
ACTORS, item AC01: a parent-class `error' arm recast every failure here, a
fault included, as an uncertain outcome)."
  (let* ((store (fnn-owner-service-store service))
         (generation (fnn-owner-core 'fn-owner-config-generation))
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
    :refreshed))

;; lane prepare-served: ACL2's un-stage of a configuration record whose
;; publication was refused before anything was written (host/owner-host.lisp
;; fn-owner-reconfigure-unstage: books/owner-prepare-served.lisp
;; fn-psrv-unstage).  The caller holds the owner mutex.
(defun fnn-owner-reconfigure-unstage ()
  (let ((word (fnn-owner-action 'fn-owner-reconfigure-unstage)))
    (unless (member word '(:unstaged :none))
      (fnn-fault "owner returned a malformed un-stage word ~a" word))
    word))

;;; ---------------------------------------------------------------------------
;;; The live reconfiguration as ACL2-ordered quanta (ruling 19, item
;;; LOCK-R2-LIVE-RECONFIGURE-IO; books/owner-reconfig-phased.lisp).
;;;
;;; The host holds a RUN: ACL2's PHASE (fn-orp-step), the effects of the last
;;; step not yet executed, and the captured values the windows need.  It feeds
;;; fn-orp-step the observation of the effect it last executed and executes
;;; the effects answered, each where its label says: (:owner . E) inside a
;;; quantum of the caller's section, (:off . E) with the owner mutex O and the
;;; extent mutex E both released.  It decides nothing: every branch below is a
;;; step of fn-orp-step (keystone fn-orp-step-runs-the-phased-run: the host's
;;; loop over the step runs exactly fn-orp-run) or an ACL2 word it passes on.

(defstruct (fnn-reconfig (:conc-name fnn-rc-))
  (service nil)
  (reserve nil)        ; fn-orp-step's RESERVE: only `store limit' reserves
  (phase :start)       ; ACL2's phase
  (event :go)          ; the observation the next step is fed
  (pending nil)        ; the labelled effects of the last step not yet executed
  (startedp nil)
  (record nil)         ; the staged record's octets
  (reason nil)         ; ACL2's reason for a refusal
  (word nil)           ; :accepted or :refused, for the caller's continuation
  (next nil)           ; the next generation's name (fn-owner-cfg-next-name)
  (clear nil)          ; ACL2's authorization with that name unoccupied
  (occupied nil)       ; ... and occupied (the lstat selects, ACL2 decided both)
  (authorization nil)  ; the one the observation selected
  (generation nil)     ; the published record's generation and name
  (name nil)
  (step nil)           ; *fnn-section-step* at the end of the last window
  (condition nil)      ; the condition a window met, re-signalled under O
  (fence-store nil)    ; an uncertain publication: the store is fenced under O
  (missing nil)        ; peers whose journals window B has yet to scan
  (prefix-size nil)    ; ACL2's journal prefix size, read under O
  (scanned nil)        ; (PEER JOURNAL ENTRIES OFFSET) per scanned journal, newest first
  (installedp nil)
  (holdp nil)          ; the gate's hold (fn-otm-hold-begin) is up
  (answer nil)         ; the caller's continuation's values
  (windowp nil))       ; true while an off-owner window is next

(defun fnn-rc-advance (run)
  "Feed the pending EVENT to ACL2's step: its effects and next phase."
  (destructuring-bind (effects phase)
      (fnn-call 'fn-orp-step (fnn-rc-phase run) (and (fnn-rc-reserve run) t)
                (fnn-rc-event run))
    (unless (and (listp effects)
                 (every (lambda (e) (and (consp e) (member (car e) '(:owner :off))))
                        effects))
      (fnn-fault "owner returned a malformed reconfiguration step ~s" effects))
    (setf (fnn-rc-pending run) effects
          (fnn-rc-phase run) phase)))

(defun fnn-rc-next-feed-event (run)
  "Window B's event after a journal returned: (:feed PEER) for the next newly
configured peer, else :feeds-done."
  (let ((peer (pop (fnn-rc-missing run))))
    (if peer (list :feed peer) :feeds-done)))

(defun fnn-rc-prime (run)
  "Ask ACL2 for the next effects while none are pending and the run lasts."
  (loop while (and (null (fnn-rc-pending run))
                   (not (eq (fnn-rc-phase run) :done)))
        do (when (and (consp (fnn-rc-phase run)) (eq (car (fnn-rc-phase run)) :feeding))
             (setf (fnn-rc-event run) (fnn-rc-next-feed-event run)))
           (fnn-rc-advance run)))

(defun fnn-rc-resignal (run default)
  "Under the owner: the condition a window met, else DEFAULT, re-signalled
with the publication step the window left, so the section's one boundary
classifies it as it did when the window ran inside the section."
  (setq *fnn-section-step* (fnn-rc-step run))
  (error (or (fnn-rc-condition run) default)))

(defun fnn-rc-do-stage (run stage)
  "Effect :stage, under O: ACL2's staging entry, STAGE (lambda (CID)) -- the
caller's (fnn-owner-result 'fn-ores-config-result-p 'ENTRY CID ...) -- over a
private logical connection (its pin is the current generation
fn-ocfg-reconfig-refusal checks).  `fn-owner-open' answers the new
connection's integer id, or NIL when the model refused the open (it is not an
action keyword).  A staged record's octets are the one configuration record to
publish; a refusal keeps ACL2's reason (:busy while another record is staged)."
  (let* ((cid (let ((opened (fnn-owner-core 'fn-owner-open)))
                (unless (or (null opened) (and (integerp opened) (>= opened 0)))
                  (fnn-fault "owner returned a malformed connection id"))
                opened))
         (result (and (integerp cid) (funcall stage cid)))
         (staged (and result (fnn-core 'fn-ores-config-word result))))
    (when (integerp cid) (fnn-owner-action 'fn-owner-close cid))
    (cond ((eq staged :staged)
           (setf (fnn-rc-record run)
                 (fnn-octets (fnn-core 'fn-ores-config-octets result)))
           :staged)
          (t (setf (fnn-rc-reason run)
                   (and (eq staged :refused) (fnn-core 'fn-ores-config-reason result)))
             (or staged :none)))))

(defun fnn-rc-do-authorize (run)
  "Effect :authorize, under O: ACL2's fn-oclc-live-authorizep (the staged
record applies to the carried node and configuration).  An authorized record
is also decided here for both observations the window can make of the next
generation's name, over the state the owner carries
(fn-owner-cfg-native-admin-authorize-carried: no record read, no history
replayed): window A lstats that name and takes the decision its answer selects.
The staged record holds the configuration lock, so the carried state cannot move
between the two."
  (cond ((fnn-owner-core 'fn-owner-reconfigure-authorizedp)
         (let* ((store (fnn-owner-service-store (fnn-rc-service run)))
                (record (fnn-octet-list (fnn-rc-record run)))
                (lock (fnn-admin-lock-observation store))
                (profile (fnn-store-config store)))
           (setf (fnn-rc-next run) (fnn-owner-core 'fn-owner-cfg-next-name)
                 (fnn-rc-clear run)
                 (fnn-owner-core 'fn-owner-cfg-native-admin-authorize-carried
                                 record lock nil profile)
                 (fnn-rc-occupied run)
                 (fnn-owner-core 'fn-owner-cfg-native-admin-authorize-carried
                                 record lock t profile)))
         :authorized)
        (t :unauthorized)))

(defun fnn-rc-do-complete (run)
  "Effect :complete, under O: the owner installs the durably published record
(fn-owner-reconfigure-complete); ACL2's verdict is the event."
  (fnn-owner-action 'fn-owner-reconfigure-complete (fnn-rc-generation run)))

(defun fnn-rc-do-refresh (run)
  "Effect :refresh, under O: the store's configuration cache follows the
generation the owner installed, and ACL2's live configuration names the
journals window B provisions (newly configured peers only; fnn-owner-feed-
configured-missing).  ACL2's journal prefix size is read here for window B."
  (fnn-owner-refresh-config-cache (fnn-rc-service run) (fnn-rc-generation run))
  (setf (fnn-rc-prefix-size run)
        (fnn-nat (fnn-owner-core 'fn-owner-feed-journal-prefix-size))
        (fnn-rc-missing run)
        (fnn-owner-feed-configured-missing (fnn-rc-service run))))

(defun fnn-rc-do-replay (run peer)
  "Effect (:feed-replay . PEER), under O: the owner applies the entries
window B's scan of PEER's journal returned."
  (let ((scanned (find peer (fnn-rc-scanned run) :key #'first :test #'equal)))
    (unless scanned (fnn-fault "no scanned FNFD journal for peer ~a" peer))
    (fnn-owner-feed-replay peer (third scanned) (fourth scanned))))

(defun fnn-rc-do-install (run)
  "Effect :install, under O: the journals window B opened join the feeds."
  (fnn-owner-feed-install
   (fnn-rc-service run)
   (loop for entry in (reverse (fnn-rc-scanned run))
         collect (cons (first entry) (second entry))))
  (setf (fnn-rc-installedp run) t))

(defun fnn-rc-owner-effect (run effect)
  "Execute one owner effect under O.  Answers :reserve, :convert, :release or
:continue for the caller's own work (the macro runs it in the quantum), else
NIL.  The event the effect observed is left for the next step."
  (let ((what (if (consp effect) (car effect) effect)))
    (case what
      ((:stage :reserve :convert :release :continue)
       (when (eq what :continue)
         (setf (fnn-rc-word run)
               (if (equal (cdr (first (fnn-rc-pending run))) :accept) :accepted :refused)))
       what)
      (:authorize (setf (fnn-rc-event run) (fnn-rc-do-authorize run)) nil)
      (:complete (setf (fnn-rc-event run) (fnn-rc-do-complete run)) nil)
      (:refresh (fnn-rc-do-refresh run) nil)
      (:feed-replay (fnn-rc-do-replay run (cdr effect)) nil)
      (:install (fnn-rc-do-install run) nil)
      (:unstage (fnn-owner-reconfigure-unstage) nil)
      ((:accept :refuse) nil)
      (:fence
       (when (fnn-rc-fence-store run)
         (setf (fnn-store-fenced (fnn-owner-service-store (fnn-rc-service run))) t))
       (fnn-rc-resignal run (make-condition 'fnn-store-indeterminate
                                            :message "owner rejected a durably published configuration")))
      (:fault
       (fnn-rc-resignal run (make-condition 'fnn-store-fault
                                            :message "the configuration change faulted")))
      (t (fnn-fault "owner named the reconfiguration effect ~s" effect)))))

(defun fnn-rc-hold (run entry)
  "Under O: the gate's hold, ACL2's fn-otm-hold-begin (ENTRY :begin) in the
quantum that leaves the owner for its first window, fn-otm-hold-end (:end) in
the quantum whose step answered :done.  A second reconfiguration is refused :busy at its staging
(fn-ocfg-reconfig-refusal) before it gets here; the hold's :busy here, or an
end that finds no hold, is a fault."
  (let ((word (fnn-owner-reconfig-hold (fnn-rc-service run) entry)))
    (unless (eq word (if (eq entry :begin) :held :released))
      (fnn-fault "owner answered the reconfiguration hold ~(~a~) with ~a" entry word))
    (setf (fnn-rc-holdp run) (eq entry :begin))))

(defun fnn-rc-leave (run)
  "Under O, last in every quantum of the section (its unwind-protect cleanup,
outside the caller's E): a run that leaves for its first window takes the
gate's hold (fn-otm-hold-begin) before it releases the owner; a run that does
not wait for a window, because its step answered :done (accept, refuse) or
the quantum is being left by the fence or fault it re-signalled, releases it
(fn-otm-hold-end)."
  (cond ((and (fnn-rc-windowp run) (not (fnn-rc-holdp run)))
         (fnn-rc-hold run :begin))
        ((and (not (fnn-rc-windowp run)) (fnn-rc-holdp run))
         (fnn-rc-hold run :end))))

(defun fnn-rc-owner-quantum (run)
  "Under O, in a quantum of the caller's section: execute the owner effects
ACL2 names, in order, until one is the caller's own (answered, for the macro
to run) or the next is off the owner (the run waits for its window) or the run is done (the hold is released; NIL)."
  (loop
    (fnn-rc-prime run)
    (let ((head (first (fnn-rc-pending run))))
      (cond ((null head)
             (setf (fnn-rc-windowp run) nil)
             (return nil))
            ((eq (car head) :off)
             (setf (fnn-rc-windowp run) t)
             (return nil))
            (t (pop (fnn-rc-pending run))
               (let ((stop (fnn-rc-owner-effect run (cdr head))))
                 (when stop (return stop))))))))

(defun fnn-rc-classify (run condition)
  "A window met CONDITION.  It is kept to be re-signalled under O; the word
is the one ACL2's step takes: :uncertain for an indeterminate outcome,
:refused for a plain refusal (nothing was written), else :fault."
  (setf (fnn-rc-condition run) condition)
  (cond ((typep condition 'fnn-store-indeterminate) :uncertain)
        ((eq (type-of condition) 'fnn-store-error)
         (setf (fnn-rc-condition run) nil)
         :refused)
        (t :fault)))

(defun fnn-rc-do-observe (run)
  "Effect (:off . :observe): lstat of the next generation's name (the only
I/O of the authorization), selecting the decision ACL2 made for that
observation.  :ok when ACL2's decision accepts the publication, :refused when
it refuses (its reason kept)."
  (let* ((store (fnn-owner-service-store (fnn-rc-service run)))
         (next (fnn-rc-next run))
         (occupied (and (stringp next)
                        (fnn-lstat (fnn-join (fnn-config-dir store) next))
                        t))
         (result (if occupied (fnn-rc-occupied run) (fnn-rc-clear run))))
    (setf (fnn-rc-authorization run) result)
    (cond ((eq (fnn-core 'fn-native-admin-host-publication-status result) :accepted)
           :ok)
          (t (setf (fnn-rc-reason run)
                   (fnn-core 'fn-native-admin-host-publication-reason result))
             :refused))))

(defun fnn-rc-do-publish (run)
  "Effect (:off . :publish): ACL2's publication plan executed, off O and E.
The outcome is the publication's own word; an uncertain one fences the store
and the service when quantum 2 re-signals it."
  (unwind-protect
       (multiple-value-bind (outcome generation name)
           (fnn-admin-publish-effect (fnn-owner-service-store (fnn-rc-service run))
                                     (fnn-rc-record run) (fnn-rc-authorization run))
         (setf (fnn-rc-generation run) generation
               (fnn-rc-name run) name)
         (when (eq outcome :uncertain)
           (setf (fnn-rc-fence-store run) t
                 (fnn-rc-condition run)
                 (make-condition 'fnn-store-indeterminate
                                 :message "configuration record publication is uncertain")))
         outcome)
    ;; The queued stage cleanup (the unlink and its directory fsync) runs
    ;; here, with no lock held.
    (fnn-immutable-drain-cleanups)))

(defun fnn-rc-do-feed-io (run peer)
  "Effect (:off . (:feed-io . PEER)): open, read and repair PEER's journal
(fnn-owner-feed-open).  A journal that did not return closes every journal
this window opened."
  (multiple-value-bind (journal entries offset)
      (fnn-owner-feed-open (fnn-owner-service-store (fnn-rc-service run))
                           peer (fnn-rc-prefix-size run))
    (push (list peer journal entries offset) (fnn-rc-scanned run))
    :ok))

(defun fnn-rc-close-scanned (run)
  "Close the journals scanned and not installed; the first failure is lost to
the condition already carried."
  (unless (fnn-rc-installedp run)
    (fnn-owner-feed-close-entries
     (loop for entry in (fnn-rc-scanned run) collect (cons (first entry) (second entry))))
    (setf (fnn-rc-scanned run) nil)))

(defun fnn-rc-window (run)
  "Off O and E: execute the effects ACL2 labels :off, in order, until the
next is an owner effect or the run is done.  *fnn-section-step* is this
window's own binding; the value it ends at travels to quantum 2."
  (let ((*fnn-section-step* nil))
    (unwind-protect
         (loop
           (fnn-rc-prime run)
           (let ((head (first (fnn-rc-pending run))))
             (unless (and head (eq (car head) :off))
               (return))
             (pop (fnn-rc-pending run))
             (let ((effect (cdr head)))
               ;; A condition a window meets is its RESULT: classified into
               ;; the word ACL2's step takes, kept, and re-signalled under O
               ;; by the :fence or :fault effect (fnn-rc-resignal), where the
               ;; section's one boundary classifies it.
               (setf (fnn-rc-event run)
                     (handler-case
                         (cond ((eq effect :observe) (fnn-rc-do-observe run))
                               ((eq effect :publish) (fnn-rc-do-publish run))
                               ((and (consp effect) (eq (car effect) :feed-io))
                                (fnn-rc-do-feed-io run (cdr effect)))
                               (t (fnn-fault "owner named the reconfiguration window effect ~s"
                                             effect)))
                       (serious-condition (condition)
                         (fnn-rc-close-scanned run)
                         (fnn-rc-classify run condition)))))))
      (setf (fnn-rc-step run) *fnn-section-step*))
    (setf (fnn-rc-windowp run) nil)))

(defun fnn-rc-begin (run reserve)
  "Register the request: RESERVE for the store-limit caller.  Nothing runs
until the caller's drive."
  (setf (fnn-rc-reserve run) reserve
        (fnn-rc-startedp run) t)
  nil)

(defmacro fnn-owner-live-reconfigure
    ((run drive section service cid &rest class) (word reason)
     &key before stage reserve convert release continue)
  "Stage, publish and complete one ACL2-constructed configuration record as
quanta of the caller's SECTION, the durable I/O off the owner (ruling 19; ACL2:
books/owner-reconfig-phased.lisp fn-orp-step, keystone
fn-orp-step-runs-the-phased-run).  The caller's section call is this form's
(SECTION SERVICE CID CLASS...), as fnn-owner-held-commit's is; BEFORE is its
quantum-1 body, which ends by registering the request,
(fnn-rc-begin RUN RESERVE), and calling (DRIVE) in tail position.  STAGE is
ACL2's staging entry as (lambda (CID) (fnn-owner-result 'fn-ores-config-result-p
'ENTRY CID ARG...)).  Answers the values of the last quantum's CONTINUE.

STATEMENT.  QUANTUM 1 (the entry, under O): BEFORE, then :stage, :authorize
and, for `store limit' (RESERVE true), :reserve under E; a refusal there
unstages and answers.  WINDOW A (no O, no E): :observe, the lstat of the next
generation's name, then :publish, the immutable publication (open, write,
fsync, link, directory fsync, unlink, close).  QUANTUM 2 (SECTION again, as
class :commit under the hold): by the outcome :complete and :refresh (the store's configuration cache
and the newly configured peers); a refused publication releases, unstages and
answers; an uncertain one fences and a fault faults, the window's condition
re-signalled under O.  WINDOW B (no O): (:feed-io . PEER), each newly
configured journal's open, read and repair.  QUANTUM 3 (SECTION again, :commit):
(:feed-replay . PEER) for each, :install, then :convert under E when reserved;
with no new peer quantum 3 is quantum 2's tail.  CONTINUE is the caller's work
after the answer, run in the quantum that decides it, with WORD (:accepted or
:refused) and REASON (ACL2's).  RESERVE, CONVERT and RELEASE are the
store-limit pool reservation: taken in quantum 1 inside the caller's E, CONVERT
and RELEASE take E themselves; nobody holds E across a window.

HELD BETWEEN QUANTA.  The staged record: ACL2 refuses a second reconfiguration
while it stands (fn-ocfg-reconfig-refusal :busy, the stage entry's reason, so a
second caller's CONTINUE sees (:refused :busy)) and :begin and :take
(fn-ocfg-step).  The gate's hold (books/owner-time-reconfig.lisp): taken by
fn-otm-hold-begin in the quantum that leaves for window A, released by
fn-otm-hold-end in the quantum whose step answered :done.  Under it the gate
admits only :inspect, :reader and :commit (this form's re-entry: fn-otm-hold-
next), and the committer may not START (fn-otm-committer-may-start).

WHAT A WINDOW OBSERVES.  Window A: the filesystem, and the values quantum 1
captured (the record, ACL2's two authorizations); no owner state.  Window B:
the feed directory and the journals of peers no installed feed serves, which
nothing writes before :install; no owner state.  A concurrent quantum sees the
owner either as before :complete (the old configuration, the record staged) or
as after it.

NO HALF-INSTALLED CONFIGURATION.  ACL2 installs the new configuration in the
one quantum that runs :complete (fn-owner-reconfigure-complete) and the
store's cache follows in that quantum; the feed table changes only at :install.
No concurrent caller can see the store's cache, the owner's configuration and
the feeds disagree except between quantum 2 and quantum 3, in which the staged
record is gone and no journal exists for a new peer: the hold, which stands
until the step is done, admits no quantum that could use the difference."
  (let ((stop (gensym "STOP")) (results (gensym "RESULTS")))
    `(let* ((,run (make-fnn-reconfig :service ,service))
            (,results nil))
       (unwind-protect
            (flet ((,drive ()
                     (loop
                       (let ((,stop (fnn-rc-owner-quantum ,run)))
                         (case ,stop
                           (:stage (setf (fnn-rc-event ,run) (fnn-rc-do-stage ,run ,stage)))
                           (:reserve (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
                                       ,reserve))
                           (:convert (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
                                       ,convert))
                           (:release (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
                                       ,release))
                           (:continue
                            (setf (fnn-rc-answer ,run)
                                  (multiple-value-list
                                   (let ((,word (fnn-rc-word ,run))
                                         (,reason (fnn-rc-reason ,run)))
                                     (declare (ignorable ,word ,reason))
                                     ,continue))))
                           (t (return)))))
                     (values-list (fnn-rc-answer ,run))))
              (setq ,results
                    (multiple-value-list
                     (,section ,service ,cid
                              (lambda () (unwind-protect ,before (fnn-rc-leave ,run)))
                              ,@class)))
              (loop while (fnn-rc-windowp ,run)
                    do (fnn-rc-window ,run)
                       (setq ,results
                             (multiple-value-list
                              (,section ,service ,cid
                               (lambda () (unwind-protect (,drive) (fnn-rc-leave ,run)))
                               :commit))))
              (values-list ,results))
         (fnn-rc-close-scanned ,run)))))

;;; PKT-221: the credential file's login bindings, published into the owner's
;;; configuration, one record per delta list ACL2's fn-lb-sync-plan names.
;;; This runs outside any quantum: a plan quantum, then each record through
;;; fnn-owner-live-reconfigure.  At the start (fnn-native-auth-install, an
;;; owner startup hook) it runs after the gate exists and the committer and mux
;;; are started but before any listener is bound
;;; (host/native/owner.lisp fnn-owner-run: fnn-owner-run-startup-hooks precedes
;;; fnn-listen), so no client quantum can interleave and no hold is needed; on a
;;; running owner the credential reload (host/native/login-bindings.lisp) takes
;;; the gate's hold per record, and ACL2 refuses a record staged on a plan a
;;; concurrent change outdated.
(defun fnn-native-auth-publish-bindings (service octets presentp max-credentials)
  "Publish the credential file's login bindings into the owner's configuration.
PKT-221: ACL2's fn-lb-sync-plan names the delta lists; each is staged and made
durable through fnn-owner-live-reconfigure, the one live path.  Answers
:accepted, or :refused before any record whose publication was refused
(records published before it stand)."
  (let ((plan (fnn-quantum-control
               service nil
               (lambda ()
                 (fnn-admin-test-fault "login-bindings")
                 (fnn-owner-core 'fn-owner-login-bindings-plan
                                 (fnn-core 'fn-native-auth-host-load-bindings
                                           octets presentp max-credentials))))))
    (unless (and (consp plan) (eq (first plan) :ok) (listp (second plan)))
      (fnn-err "login bindings refused: ~a" (and (consp plan) (second plan)))
      (return-from fnn-native-auth-publish-bindings :refused))
    (dolist (deltas (second plan) :accepted)
      (unless (eq (fnn-owner-live-reconfigure (run drive fnn-quantum-control service nil)
                      (word reason)
                    :stage (lambda (pcid) (fnn-owner-result 'fn-ores-config-result-p 'fn-owner-reconfigure-deltas pcid deltas))
                    :before (progn
                              (fnn-admin-test-fault "login-bindings-record")
                              (fnn-rc-begin run nil)
                              (drive))
                    :continue word)
                  :accepted)
        (return-from fnn-native-auth-publish-bindings :refused)))))

;;; PRF-164 (PKT-439): the owner's side of XREDEEM.  The connection CID
;;; holds (books/nntp-auth.lisp fn-auth-redeem-waitp) after its read; the
;;; caller, host/native/owner.lisp fnn-owner-redeem-quantum, holds the owner
;;; mutex in a quantum of its own, of ACL2's publication class (never while a
;;; batch is in flight; PKT-828 open item 2).  The NNTP session
;;; reaches the publication in-process, the way peer accept does
;;; (host/native/peer-invite.lisp), not over the control socket: no control
;;; request kind is used.
(defun fnn-owner-account-redeem (service cid class)
  "Plan, publish, then answer: 281 only after the redeem record is durable.
Runs as the quanta of fnn-owner-serialized (CLASS, ACL2's publication class)
for the connection CID, which must still wait for the owner's word; the reply
is the continuation's, so it leaves only after the durable publication
(fnn-owner-live-reconfigure).

Returns the ACL2-rendered reply octets for CID, or NIL when the connection no
longer waits."
  (let ((salt nil) (bound nil))
  (fnn-owner-live-reconfigure (run drive fnn-owner-serialized service cid class)
      (published reason)
    :stage (lambda (pcid) (fnn-owner-result 'fn-ores-config-result-p 'fn-acct-host-owner-redeem-stage pcid cid salt bound))
    :before
    (and (fnn-owner-core 'fn-acct-host-owner-redeem-waitingp cid)
         (progn
           (setq salt (fnn-csprng-octets (fnn-core 'fn-acct-host-salt-octets)
                                         "credential salt")
                 bound (fnn-profile-nat 'fn-store-profile-max-credentials
                                        (fnn-owner-service-store service)))
           (fnn-rc-begin run nil)
           (drive)))
    :continue
    (progn
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
        ;; The connection may have left while the record was published
        ;; (the windows hold no owner): it is then answered nothing, as a
        ;; connection that no longer waits is.
        (and (fnn-owner-core 'fn-acct-host-owner-redeem-waitingp cid)
             (progn
               (unless (eq (fnn-owner-action 'fn-owner-account-outcome cid word) :ok)
                 (fnn-fault "owner rejected the redeem outcome"))
               (fnn-octet-list (fnn-owner-octets-global 'fn-owner-output)))))))))

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
         (word (fnn-quantum-control
                service nil
                (lambda ()
                  (fnn-admin-test-fault "compaction")
                  (fnn-owner-core 'fn-owner-sco-request
                                  (fnn-checkpoint-budget-test-override nil) free
                                  (fnn-owner-monotonic-ms))))))
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
         (found (fnn-quantum-control
                 service nil
                 (lambda ()
                   (fnn-admin-test-fault "inspect")
                   (and (fnn-bridge-lookup-found-p octets) t))))
         (word (fnn-core 'fn-omr-inspect-word found)))
    (list :reason (fnn-core 'fn-omr-inspect-status word) word)))
(defun fnn-owner-export-request (service dir)
  "Row S3b: `store export DIR' on the running owner.  DIR's existence is
observed off the mutex (lstat is I/O); under the owner mutex ACL2 answers
the word from the two observations (books/owner-export-request.lisp
fn-oex-request-word: an export in flight, DIR present, else :requested),
and a :requested one captures the history, pins the arena and starts the
export thread before the mutex is released (host/native/owner.lisp
fnn-owner-export-start), so the captured list and the pinned generation
agree.  The reply carries the word and ACL2's sentence (kind 23,
fn-oex-request-line)."
  (let* ((existsp (and (fnn-lstat dir) t))
         (word (fnn-quantum-control
                service nil
                (lambda ()
                  (fnn-admin-test-fault "export")
                  (let* ((inflightp (first (fnn-owner-export-observation service)))
                         (word (fnn-core 'fn-oex-request-word inflightp existsp)))
                    (when (eq word :requested)
                      (let ((captured (fnn-owner-core 'fn-owner-oex-capture)))
                        (unless (and (true-listp captured) (= (length captured) 4))
                          (fnn-fault "owner returned a malformed export capture"))
                        (fnn-owner-export-start service captured dir)))
                    word)))))
    (unless (member word '(:requested :export-in-flight :archive-exists))
      (fnn-fault "owner returned a malformed export answer ~a" word))
    (fnn-err "EXPORT request archive=~a answer=~(~a~)" dir word)
    (list :reason (fnn-core 'fn-oex-request-status word) word
          (fnn-core 'fn-oex-request-line word dir))))

(defun fnn-owner-export-status (service)
  "Row S3b: `store export --status' on the running owner: ACL2's word over
the exporter slot (fn-oex-status-word: in flight, done, failed, idle) and
its sentence (fn-oex-outcome-line), no owner state read."
  (destructuring-bind (inflightp outcome dir) (fnn-owner-export-observation service)
    (let ((word (fnn-core 'fn-oex-status-word inflightp outcome)))
      (list :reason (fnn-core 'fn-oex-status-status word) word
            (fnn-core 'fn-oex-outcome-line word (if (stringp dir) dir ""))))))

(defun fnn-owner-reclaim-request (service mode)
  "Q16: `store reclaim' on the running owner (books/owner-reclaim.lisp).  ACL2
answers it under the owner mutex (host/owner-host.lisp fn-owner-orc-request):
a dry run the owner runs now, off its mutex, on this control thread
(host/native/owner.lisp fnn-owner-reclaim-dry-run: the capture by pointer,
then the fold over the rows, the classes and the decision), its report in the
owner's log as `store reclaim --dry-run' prints it offline; a pass in flight
answers :in-flight; `--recorded' runs the pass that installs
(fnn-owner-reclaim-pass: :installed, :none, or deferred by name);
`store reclaim' without it records the instant live, then runs that pass.
The reply names the word."
  (let* ((free (fnn-disk-free-octets (fnn-owner-service-store service)))
         (word (fnn-quantum-control
                service nil
                (lambda ()
                  (fnn-admin-test-fault "reclaim")
                  (fnn-owner-core 'fn-owner-orc-request mode
                                  (fnn-checkpoint-budget-test-override nil) free
                                  (fnn-owner-monotonic-ms))))))
    (unless (member word '(:requested :in-flight :queued :blocked :no-recorded-instant
                           :offline-only))
      (fnn-fault "owner returned a malformed reclaim answer ~a" word))
    (fnn-err "RECLAIM request mode=~(~a~) answer=~(~a~)" mode word)
    (when (and (eq word :requested) (eq mode :reclaim))
      ;; `store reclaim': the instant at the clock recorded first, through
      ;; the live reconfiguration (fn-owner-orc-instant-stage), durable
      ;; before the pass reads it; a refusal is before anything was written.
      (let ((clock (fnn-store-prepare-observation)))
        (destructuring-bind (recorded &optional reason &rest ignored)
            (fnn-owner-live-reconfigure (run drive fnn-quantum-control service nil)
                (word why)
              :stage (lambda (pcid) (fnn-owner-result 'fn-ores-config-result-p 'fn-owner-orc-instant-stage pcid clock))
              :before
              (progn
                (fnn-admin-test-fault "reclaim-instant")
                (fnn-rc-begin run nil)
                (drive))
              :continue (list word why))
          (declare (ignore ignored))
          (unless (eq recorded :accepted)
            (fnn-err "RECLAIM instant refused: ~(~a~)" reason)
            (return-from fnn-owner-reclaim-request
              (list :reason :refused (or reason :reclaim-instant)))))))
    (when (eq word :requested)
      (setq word (if (eq mode :dry-run)
                     (fnn-owner-reclaim-dry-run service free)
                   ;; Q16 (a): `--recorded' installs (fnn-owner-reclaim-pass),
                   ;; and `store reclaim' over the instant it just recorded
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

(defun fnn-lim-decision (store plan values use run-mb core observations history)
  "ACL2's limit decision.  HISTORY is the heap history observation
(fnn-heap-history-observation over VALUES), taken by the caller: the live
one off the owner and extent mutexes (sweep S033), the offline one directly.
This reads no directory, so it is safe in the deciding quantum."
  (declare (ignore store))
  (fnn-core 'fn-lim-decide (fnn-lim-plan-field plan) (fnn-lim-plan-n plan)
            values use run-mb core +fnn-gc-nursery-octets+ observations history))

(defun fnn-lim-reason (decision)
  (fnn-core 'fn-lim-decision-reason decision))

(defun fnn-lim-line (plan decision store values funded)
  "ACL2's reply: the decision's sentence and the field's three values after
it (books/limits-live.lisp fn-lim-reply-line: requested over VALUES, funded
from FUNDED, the profile the running owner serves, NIL offline, and the
representation ceiling)."
  (fnn-core 'fn-lim-reply-line (fnn-lim-plan-field plan) (fnn-lim-plan-n plan)
            decision (fnn-store-open-ms store) values funded))

(defun fnn-owner-limit-serialized (service plan)
  "The live owner's limit change: decided under the owner mutex (the
configuration history does not move under it), published through the
ordinary live reconfiguration, and on :applied served at once."
  (let* ((store (fnn-owner-service-store service))
         ;; The machine and image observations, off the mutex.
         (core (fnn-heap-image-observation))
         (observations (fnn-heap-observations))
         (run-mb (floor (sb-ext:dynamic-space-size) 1048576))
         ;; Sweep S033: the history observation walks the journal directory,
         ;; so it is taken off the mutex too, over the profile the owner
         ;; carries (read in a quantum of its own); the deciding quantum
         ;; uses it only while that carry is unchanged, and observes again
         ;; when a concurrent limit change moved it.
         (seen nil) (history nil))
    (loop
     (loop
      (let ((carry (fnn-quantum-control
                    service nil
                    (lambda ()
                      (fnn-admin-test-fault "limit-carry")
                      (fnn-owner-core 'fn-owner-limit-carried)))))
        (when (and seen (equal (car carry) seen)) (return))
        (setq seen (car carry)
              history (and seen (fnn-heap-history-observation
                                 (fnn-store-root store) seen)))))
     (let ((answer
            (let ((growth nil) (d nil) (line nil) (funded nil) (token nil))
              ;; The decision, with the pool preview, is quantum 1's, under O
              ;; and then E; its reservation (:reserve) is the preview it
              ;; stands on.  The budget reduction is :convert's, under E, in
              ;; the quantum that installs.
              (fnn-owner-live-reconfigure (run drive fnn-quantum-control service nil)
                  (word reason)
                :stage (lambda (pcid) (fnn-owner-result 'fn-ores-config-result-p 'fn-native-admin-host-owner-reconfigure pcid plan))
                :before
                (progn
                  (fnn-admin-test-fault "limit")
                  ;; A concurrent limit change moved the carry after the
                  ;; observation above: the history is observed again off the
                  ;; mutexes, never here.  The carry moves only in a quantum
                  ;; of the owner, so this read holds until the quantum ends.
                  (if (not (equal (car (fnn-owner-core 'fn-owner-limit-carried)) seen))
                      :carry-moved
                    ;; The store's use reads only the owner's carried state, and
                    ;; its carried-debt fallback can load history pages through
                    ;; the extent mutex (fn-pgs-fill-frame takes it
                    ;; non-recursively): read it here, under the owner mutex and
                    ;; before the extent mutex.
                    (let* ((use (fnn-owner-core 'fn-owner-limit-use))
                           ;; The extent mutex owns pool draws independently of
                           ;; the owner mutex: held for the preview and the
                           ;; decision, released before the staging, and taken
                           ;; again by the reservation, ACL2's own admission
                           ;; (:reserve) of the same growth.
                           (decided
                       (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
                        (let* ((carry (fnn-owner-core 'fn-owner-limit-carried))
                               ;; The history's requested profile and what this
                               ;; process serves and admits under before D, both
                               ;; carried by the owner from its open
                               ;; (host/owner-host.lisp fn-owner-limit-carry;
                               ;; fn-lim-carry-after-is-the-history): no walk of
                               ;; the configuration history per request.
                               (values (car carry))
                               (initial (progn
                                          (setq funded (cdr carry))
                                          (unless (and (consp carry) values funded)
                                            (fnn-fault "owner carries no limit profile"))
                                          (fnn-lim-decision store plan values use run-mb core
                                                            observations history))))
                          (setq growth (fnn-core 'fn-lim-protected-growth
                                                 (fnn-core 'fn-lim-apply-row values
                                                           (fnn-lim-plan-field plan)
                                                           (fnn-lim-plan-n plan))
                                                 funded core (fnn-gc-nursery-octets)))
                          (let ((preview (first (fnn-core-page-read-pool
                                                 'fn-owner-page-read-protected-growth-preview
                                                 growth))))
                            (setq d (fnn-core 'fn-lim-article-decision
                                              (fnn-core 'fn-lim-pool-decision initial preview)
                                              (fnn-core 'fn-lim-apply-row values
                                                        (fnn-lim-plan-field plan)
                                                        (fnn-lim-plan-n plan))
                                              funded)
                                  line (fnn-lim-line plan d store values funded)))
                          (fnn-err "LIMIT ~a" line)
                          (if (not (eq (fnn-core 'fn-lim-decision-status d) :accepted))
                              (list :reason :refused (fnn-lim-reason d) line)
                            :go)))))
                      (if (eq decided :go)
                          (progn
                            (fnn-rc-begin run t)
                            (drive))
                        decided))))
                ;; The growth is reserved in quantum 1 under E, taken by the
                ;; reservation itself (fn-prl-reserve-growth,
                ;; host/page-read-host.lisp), converted
                ;; into the budget reduction in quantum 3 and evicted when the
                ;; change is refused; nobody holds E across a window.  A
                ;; reservation ACL2 refuses after the record was staged drops
                ;; the stage and refuses by ACL2's word (the decision above
                ;; admitted the same amount a moment before).
                :reserve
                (let* ((reserved (fnn-core-page-read-pool
                                  'fn-owner-page-read-growth-reserve growth))
                       (word (first reserved)))
                  (cond ((eq word :admitted) (setq token (second reserved)))
                        (t (fnn-owner-reconfigure-unstage)
                           (fnn-refuse "owner refused the limit's growth reservation: ~(~a~)"
                                       word))))
                :release
                (unless (eq (first (fnn-core-page-read-pool
                                    'fn-owner-page-read-growth-release token))
                            :evicted)
                  (fnn-fault "owner lost the growth reservation of a refused limit"))
                :convert
                ;; ACL2's served profile after D (fn-lim-funded-after,
                ;; fn-lim-funded-after-decide): the requested candidate on
                ;; :applied -- the profile every later open computes from the
                ;; history this record ended (fn-lim-effective-of-append-
                ;; record) -- else the one already served: a recorded change
                ;; does not fund, and releases its reservation.  The carry
                ;; moves to fn-lim-carry-after (the record is published); its
                ;; funded half is the answer.  A conversion ACL2 refuses is a
                ;; broken invariant (PRL-ROW-SUM-INVARIANT), a fault after the
                ;; release.
                (let ((served (fnn-owner-core 'fn-owner-limit-decided
                                              (fnn-lim-plan-field plan)
                                              (fnn-lim-plan-n plan) d)))
                  (if (equal served funded)
                      (unless (eq (first (fnn-core-page-read-pool
                                          'fn-owner-page-read-growth-release token))
                                  :evicted)
                        (fnn-fault "owner lost the growth reservation of a recorded limit"))
                    (progn
                      (unless (eq (first (fnn-core-page-read-pool
                                          'fn-owner-page-read-growth-convert token growth))
                                  :protected-growth-admitted)
                        (fnn-core-page-read-pool 'fn-owner-page-read-growth-release token)
                        (fnn-fault "owner lost the protected space of a durably recorded limit"))
                      (unless (eq (fnn-owner-core 'fn-owner-apply-limit-profile served)
                                  :installed)
                        (fnn-indeterminate
                         "owner refused a durably recorded limit's profile"))
                      (setf (fnn-store-config store) served))))
                :continue
                (if (eq word :refused)
                    (list :reason :refused reason)
                  (list :reason :accepted (fnn-lim-reason d) line))))))
       (unless (eq answer :carry-moved) (return answer))))))

(defun fnn-admin-execute-limit (store plan)
  "The offline limit change: no process holds a reservation (run-mb 0), so an
accepted change is recorded for the next start.  Prints ACL2's line."
  (let* ((values (fnn-lim-recorded-profile store))
         (use (fnn-core-state 'fn-store-lim-use))
         (d (fnn-lim-decision store plan values use 0
                              (fnn-heap-image-observation) (fnn-heap-observations)
                              (fnn-heap-history-observation (fnn-store-root store) values)))
         (line (fnn-lim-line plan d store values nil)))
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
-reclaim-mode; row S1: a store limit, fnn-owner-limit-serialized)."
  ;; Row S9: the retire request, before any administrative plan.
  (let ((retire (fnn-core 'fn-nret-request argv)))
    (when retire
      (return-from fnn-owner-live-admin-serialized
        (fnn-owner-retire-begin service (second retire)))))
  (let ((plan (fnn-core 'fn-native-admin-host-plan argv)))
    (when (fnn-core 'fn-native-admin-host-owner-requestp plan)
      (let ((mode (fnn-core 'fn-native-admin-host-reclaim-mode plan))
            (msgid (fnn-core 'fn-native-admin-result-inspect-msgid plan))
            (export-dir (fnn-core 'fn-native-admin-result-export-dir plan))
            (export-statusp (fnn-core 'fn-native-admin-result-export-statusp plan)))
        (return-from fnn-owner-live-admin-serialized
          (cond (mode (fnn-owner-reclaim-request service mode))
                (msgid (fnn-owner-inspect-request service msgid))
                ;; Row S3b: the export request and its status poll.
                ((stringp export-dir) (fnn-owner-export-request service export-dir))
                (export-statusp (fnn-owner-export-status service))
                (t (fnn-owner-compaction-request service)))))))
  (let ((plan (fnn-core 'fn-native-admin-host-plan argv)))
    (when (fnn-lim-plan-p plan)
      (return-from fnn-owner-live-admin-serialized
        (fnn-owner-limit-serialized service plan))))
  (let ((plan (fnn-core 'fn-native-admin-host-plan argv)))
    (fnn-owner-live-reconfigure (run drive fnn-quantum-control service nil)
        (word reason)
      :stage (lambda (pcid) (fnn-owner-result 'fn-ores-config-result-p 'fn-native-admin-host-owner-reconfigure pcid plan))
      :before
      (progn
        (fnn-admin-test-fault "admin")
        ;; PKT-453 (a): a refusal answers (:reason :refused REASON), the
        ;; plan's reason or the staging step's, both ACL2's.  The quantum's
        ;; value is the answer: no early return crosses its boundary (lane
        ;; failure-scope: an unwind no condition explains is a fault).
        (if (not (fnn-admin-plan-acceptedp plan))
            (list :reason :refused (fnn-admin-plan-reason plan))
          (progn
            (fnn-rc-begin run nil)
            (drive))))
      :continue (if (eq word :refused) (list :reason :refused reason) word))))

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
    (fnn-unwind-cleanups
        ((multiple-value-bind (generation name) (fnn-admin-publish store record authorization)
           (values generation name
                   (fnn-admin-verify-under-lock store record authorization))))
      (fnn-immutable-drain-cleanups))))

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
    (fnn-unwind-cleanups
        ((let ((report (fnn-core-state 'fn-native-admin-host-query-report plan)))
           (unless (fnn-octet-list-p report)
             (fnn-fault "ACL2 returned a malformed configuration listing"))
           (when report
             (write-sequence (fnn-octets report) *fnn-stdout*)
             (finish-output *fnn-stdout*))
           +fnn-exit-ok+))
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
      (fnn-unwind-cleanups
          ((multiple-value-bind (opened count) (fnn-open-live-store root t)
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
                 +fnn-exit-ok+))))
        (when store (fnn-store-close store)))))
