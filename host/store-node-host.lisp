; Experimental store bridge: physical observations drive the proved fn-sn core.
; These program-mode wrappers are inside the adapter trust boundary. Callee
; guard verification is conditional on valid inputs/state; it does not prove
; that this wrapper establishes each precondition. Keep actual host/model
; correspondence and growing-history execution cost explicit when changing
; these entries. Do not add whole-store recognition per served operation.
(in-package "ACL2")
(include-book "../books/store-observed")
(include-book "../books/history-columns-relation")
; D25: the duplicate-versus-conflict decision keys on the poster's bytes.
(include-book "../books/poster-bytes")
(include-book "../books/native-config-observation")
(include-book "../books/store-sweep")
(include-book "../books/store-node-resolution")
(include-book "../books/store-prepare-correspondence")
(include-book "../books/store-budget")
(include-book "../books/store-budget-article")
(include-book "../books/store-maintenance-reserve")
(include-book "../books/store-capacity-vector")
(include-book "../books/store-carried-folds")
; PKT-220: the retention figures `operator CONFIG obligations' opens with.
(include-book "../books/retention-figures")
(include-book "../books/store-capacity-config")
; PKT-510 (1): the offline request authorizes from the open's carried fold.
(include-book "../books/config-carried-open")
(include-book "../books/node-config")
(include-book "../books/native-admin")
; D27, PRF-102: the operator's namespace counts.
(include-book "../books/store-profile-namespace")
; P3: open from an exact-state checkpoint.
(include-book "../books/store-checkpoint-open")
(include-book "../books/store-checkpoint-tables-reader")
; The state checkpoint under the records flip (lane checkpoint-arena): the
; arena run A before the four tables; its load (fn-scka-open-run, the
; host's fn-scka-seal-n calls, fn-scka-finish) and its writer
; (fn-scka-write-setup, fn-scka-write-step, fn-scka-canon-rows).
(include-book "../books/store-checkpoint-arena-load")
(include-book "../books/store-checkpoint-arena-writer")
(include-book "../books/owner-checkpoint-pipeline")
; PKT-444 (1): the open names a pre-C1 control record instead of faulting.
(include-book "../books/store-open-pre-c1")
(include-book "../books/store-open-replay-refusal")
; PRF-242: the open's replay answers its identity questions from tries it
; builds as it advances, and the history recognizer dispatches once per record.
(include-book "../books/replay-identity-index")
; fn-store-sn-prepare and fn-store-sn-finish call the owner's carried twins
; (fn-pcar-spc-prepare, fn-ccar-sn-finish): neither walks the history.
(include-book "../books/owner-commit-carried")
(include-book "../books/owner-prepare-carried")
; fn-store-sn-prepare stages the interned row through the carried prepare
; (fn-store-prepare-interned-carried-is-prepare-interned under fn-snt-relation).
(include-book "../books/store-prepare-carried")
;; fn-store-sn-prepare calls fn-psrv-store-prepare-next (lane prepare-served).
(include-book "../books/store-prepare-served")
(include-book "../books/store-checkpoint-codec")
; fn-bs-scp-program: the checkpoint file name is its rename target.
(include-book "../books/byte-store-state-checkpoint-program")
; fn-rcl-same-articlep: the duplicate-versus-tombstone comparison
; fn-store-existing-action (books/store-intern.lisp) makes, which
; fn-store-sn-prepare and the retention prepare call.
(include-book "../books/store-reclaim")
(include-book "../books/acceptance-payload-ref")
;
; Loaded here, not left to a bridge's `ld' order: this file uses names
; host/store-host.lisp defines, so a session that loads this file alone
; must get them too.  A second `ld' of a file already in the session
; re-admits identical definitions, which ACL2 accepts as redundant.
(ld "store-host.lisp" :ld-error-action :error)

(include-book "../books/peer-config")
(include-book "../books/provenance-codec")
;; host-decisions-2 packet C: the inspect lookup (fn-provi-of-msgid).
(include-book "../books/provenance-inspect")
;; lane proto-determinism: fn-store-sn-replay-digest-report (the end of this file).
(include-book "../books/state-digest")

; This wrapper reuses the established decimal-octet boundary helpers from the
; store host. Python supplies only ordered filesystem observations.
;; The history stobj fn-hist (books/history-columns.lisp) the event-index
;; readers read in place of the store node's retired field 13.  Before each
;; read the host refreshes it against the Store it reads
;; (books/history-columns-relation.lisp fn-hist-refresh-is-the-history: the
;; result IS the history, so R holds at the read): a whole load after an open
;; or reset of the store node (`fn-store-sn-hist-reload', set below wherever
;; the store is replaced by an open), else the sync of the rows committed
;; since the last read.  One process serves one Store (owner mode, or the
;; store node's), so one stobj.
(defun fn-host-hist-sync (store fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (let ((reload (and (boundp-global 'fn-store-sn-hist-reload state)
                     (f-get-global 'fn-store-sn-hist-reload state))))
    (let ((fn-hist (fn-hist-refresh (fn-sn-files store) reload fn-hist)))
      (let ((state (f-put-global 'fn-store-sn-hist-reload nil state)))
        (mv fn-hist state)))))

(defun fn-store-sn-reset (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-store-sn-record-octets nil state))
         (state (f-put-global 'fn-store-sn-record-debt nil state))
         (state (f-put-global 'fn-store-sn-hist-reload t state))
         (state (f-put-global 'fn-store-sn
                             ; No compiled group table and no compiled
                             ; capacity: the domain is empty and the capacity
                             ; is zero until the configuration history is
                             ; replayed.  That is the fail-closed floor of
                             ; specs/reconfiguration.md section 1.6 -- a store
                             ; that has not been configured accepts nothing,
                             ; rather than accepting into a compiled-in
                             ; default.  The checkpoint host reads the live
                             ; node's capacity (`fn-store-sn-capacity').
                             (fn-sn-initial nil 0) state))
        (state (f-put-global 'fn-store-sco-open nil state))
        (state (f-put-global 'fn-store-cfg-open-configs nil state)))
    (value :ready)))

(defun fn-store-sn-state (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-store-sn state)))

; The committed record octets and the completion debt of the standalone
; Store, carried as (K . VALUE) and advanced over the records committed since
; through the Store's derived event index, as the owner carries them
; (host/owner-host.lisp fn-owner-record-octets, fn-owner-record-debt): one
; index lookup and one fold step per record committed since the last verdict,
; never a walk of the history (lane post-alloc: the walk recognised every
; retained row, 346 MB per standalone POST at N = 10,000).  Equal to the
; history folds under fn-ceis-indexedp with a valid cache
; (books/store-budget.lisp fn-sbud-bytes-carried-is-the-fold,
; books/store-carried-folds.lisp fn-scf-debt-carried-is-the-record-debt).
; The relation holds at every open (fn-sn-open-observed-is-indexed-by-
; recomputation) and every Store transition keeps it
; (books/consumer-event-index-store-invariants.lisp); a cache stays valid
; while committed records only grow (fn-sbud-octets-cache-valid-after-commit)
; and is dropped whenever a store is installed (fn-store-sn-reset,
; fn-store-sn-open-extended), so the first verdict after an open folds once.
(defun fn-store-sn-record-octets (s state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((cache (if (boundp-global 'fn-store-sn-record-octets state)
                    (f-get-global 'fn-store-sn-record-octets state)
                  nil))
         (bytes (fn-sbud-bytes-carried cache s))
         (state (f-put-global 'fn-store-sn-record-octets
                              (cons (fn-sbud-count s) bytes) state)))
    (mv bytes state)))

(defun fn-store-sn-record-debt (s state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((cache (if (boundp-global 'fn-store-sn-record-debt state)
                    (f-get-global 'fn-store-sn-record-debt state)
                  nil))
         (debt (fn-scf-debt-carried cache s))
         (state (f-put-global 'fn-store-sn-record-debt
                              (cons (fn-sbud-count s) debt) state)))
    (mv debt state)))

; The operator's headroom for the replayed Store: (used budget
; reserved-charge charge-capacity), from PROFILE (the values ACL2 decoded
; from the store's metadata file at open) and the Store state this session
; carries.  `fn-sbud-used' is the committed record count
; (fn-sbud-used-names-the-transaction-namespace); the host counts nothing.
(defun fn-store-sn-publication-verdict (profile kind state)
  (declare (xargs :stobjs state :mode :program))
  ; PRF-138: the capacity vector (`fn-cvec-verdict-at'), at the replayed
  ; history's completion debt.
  (let ((s (f-get-global 'fn-store-sn state)))
    (mv-let (bytes state) (fn-store-sn-record-octets s state)
      (mv-let (debt state) (fn-store-sn-record-debt s state)
        ; PRF-180: the count read from the index (fn-sbud-count-is-used-by-definition).
        (value (fn-cvec-verdict-at profile kind (fn-sbud-count s) bytes debt))))))

; An article's verdict (packet 1): the count gate and the history gate at the
; article's own figure, `fn-sbud-article-verdict-at' of the committed count
; and octets (books/store-budget-article.lisp,
; `fn-sbud-article-verdict-keeps-history').
(defun fn-store-sn-article-verdict (profile payload-length group-count state)
  (declare (xargs :stobjs state :mode :program
                  :guard (natp payload-length)))
  (let ((s (f-get-global 'fn-store-sn state)))
    (mv-let (bytes state) (fn-store-sn-record-octets s state)
      (mv-let (debt state) (fn-store-sn-record-debt s state)
        ; PRF-138: and the capacity vector still holds after it
        ; (`fn-cvec-article-verdict-keeps-the-vector').  PRF-180: the count
        ; read from the index (fn-sbud-count-is-used-by-definition).
        (value (fn-cvec-article-verdict-at profile (fn-sbud-count s) bytes
                                           payload-length group-count
                                           debt))))))

; The developer `store post''s word for the same verdict
; (`fn-cvec-article-verdict-word'): :admissible, :memberships (the membership
; charge alone refused it) or :unaffordable.
(defun fn-store-sn-article-verdict-word (profile payload-length group-count state)
  (declare (xargs :stobjs state :mode :program))
  (let ((s (f-get-global 'fn-store-sn state)))
    (mv-let (bytes state) (fn-store-sn-record-octets s state)
      (mv-let (debt state) (fn-store-sn-record-debt s state)
        (value (fn-cvec-article-verdict-word profile (fn-sbud-count s) bytes
                                             payload-length group-count
                                             debt))))))

(defun fn-store-sn-headroom (profile state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sbud-headroom profile (f-get-global 'fn-store-sn state))))

; The bounded observed-image entry validates the decoded record list and
; frontier, constructs its own replaying kernel image, and invokes actual
; fn-sn-recover.  This wrapper installs only its tagged successful result.
(defun fn-store-config-observation-limit (profile)
  ; The bounded physical scan uses the same ACL2-owned limit as its plan: the
  ; operator's `max-config-generations' of the profile the store runs under.
  (declare (xargs :mode :program))
  (fn-bs-profile-max-config-generations profile))

(defun fn-store-config-observation-entries (entries)
  "Convert only octet representation; decoding/name policy stays in fn-nco-observe."
  (declare (xargs :mode :program))
  (if (consp entries)
      (let ((entry (car entries)))
        (if (and (true-listp entry) (equal (len entry) 2)
                 (fn-cbor-octet-listp (car entry))
                 (fn-cbor-octet-listp (cadr entry)))
            (let ((rest (fn-store-config-observation-entries (cdr entries))))
              (if (equal rest :bad)
                  :bad
                 (cons (list (fn-store-octets->string (car entry))
                             (car (cdr entry)))
                       rest)))
          :bad))
    (if (null entries) nil :bad)))

(defun fn-store-config-observation (entries max-generations)
  "The recovery subject for one bounded physical config directory observation."
  (declare (xargs :mode :program))
  (let ((converted (fn-store-config-observation-entries entries)))
    (if (equal converted :bad)
        (fn-nco-result :fault :input nil)
      (fn-nco-observe converted max-generations))))

(defun fn-store-config-initial-observation (entries max-generations)
  "Initialization-only observation; an empty directory may receive genesis."
  (declare (xargs :mode :program))
  (let ((converted (fn-store-config-observation-entries entries)))
    (if (equal converted :bad)
        (fn-nco-result :fault :input nil)
      (fn-nco-observe-initial converted max-generations))))

; A loop (PKT-877, lane serve-depth): the recursion took one control-stack
; frame per configuration record, and the configuration history grows with
; every reconfiguration.  The same answer: :bad at the first record that does
; not decode (or an improper tail), else the values in order.
(defun fn-store-cfg-decode-records-loop (octet-records acc)
  (declare (xargs :mode :program))
  (if (consp octet-records)
      (let ((parsed (fn-cfg-decode-exact (car octet-records))))
        (if (not (fn-record-parse-okp parsed))
            :bad
          (fn-store-cfg-decode-records-loop (cdr octet-records)
                                            (cons (fn-record-parse-value parsed) acc))))
    (if (null octet-records) (revappend acc nil) :bad)))

(defun fn-store-cfg-decode-records (octet-records)
  ; Each durable configuration record decodes exactly, or the list is :bad.
  (declare (xargs :mode :program))
  (fn-store-cfg-decode-records-loop octet-records nil))

(defun fn-store-cfg-candidate-openp (octet-records frontier config-octet-records)
  "Decode at the existing byte boundary, then ask the logical native-admin
candidate predicate whether this exact next durable image reopens.  This is
not a second recovery algorithm: `fn-native-admin-candidate-openp' invokes
the same configuration replay and observed-node open definitions startup uses."
  (declare (xargs :mode :program))
  (let ((records (fn-store-decode-records octet-records))
        (config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (equal records :bad) (equal config-records :bad)
            (null config-records))
        nil
      ; The replay's domain is the retained rows: the candidate interns the
      ; decoded history into a LOCAL arena, as the open does into the live one.
      (let ((rows (fn-store-intern-records-local records)))
        (and (not (equal rows :bad))
             (if (fn-native-admin-candidate-openp rows frontier config-records) t nil))))))

(defun fn-store-cfg-native-admin-authorize
    (octet-records frontier config-octet-records record-octets lock-owned observed-name-octets
                   profile)
  "The existing exact byte decoders feed one logical publication authorization.
The result binds the core's record generation, the ACL2 filename, candidate
reopen predicate, writer-lock observation and observed final namespace."
  (declare (xargs :mode :program
                  :guard (and (fn-cbor-octet-listp record-octets)
                              (fn-octet-list-listp octet-records)
                              (fn-octet-list-listp config-octet-records)
                              (fn-octet-list-listp observed-name-octets))))
  (let ((records (fn-store-decode-records octet-records))
        (config-records (fn-store-cfg-decode-records config-octet-records))
        (parsed (fn-cfg-decode-exact record-octets))
        (names (fn-store-octet-lists->strings observed-name-octets)))
    (if (or (equal records :bad) (equal config-records :bad) (null config-records)
            (equal names :bad) (not (fn-record-parse-okp parsed)))
        (fn-native-admin-publication-result :refused :decode nil nil nil)
      ; D27: the operator's bounds, read from the profile the store runs
      ; under (the host passes the decoded config.json, opaque): field 7
      ; for a created group's name (PRF-171,
      ; `fn-cvec-native-admin-authorize-refuses-exactly-past-the-group-name-bound'),
      ; then max-config-generations, one fewer for every record but the
      ; retention rule (PRF-102, PRF-138,
      ; `fn-cvec-config-publication-keeps-the-release-generation').
      (let ((rows (fn-store-intern-records-local records)))
        (if (equal rows :bad)
            (fn-native-admin-publication-result :refused :decode nil nil nil)
          (fn-cvec-native-admin-authorize
           rows frontier config-records (fn-record-parse-value parsed)
           lock-owned names profile))))))

;; PKT-510 (1): the offline request's authorization from the open's carried
;; fold (books/config-carried-open.lisp
;; fn-cfgc-cvec-native-admin-authorize-is-the-replayed-authorization: EQUAL to
;; fn-cvec-native-admin-authorize whenever the carried fold is the replay of
;; the same histories).  The records are the extended capture's (the history
;; the open replayed, fn-sco-records of E); the fold and the open's result are
;; E's (fn-sco-store-open-of-extended-capture); the configuration history and
;; the frontier must be the ones the open used, compared here.  The candidate
;; open is not recomputed (PKT-601 (1),
;; fn-cfgc-candidate-open-carried-is-the-replayed-candidate).  NIL when there is no carried open
;; or the configuration history is not the open's: the caller then runs
;; fn-store-cfg-native-admin-authorize over the history it read.  The live
;; owner never calls this: its Store advanced past its open.
(defun fn-store-cfg-native-admin-authorize-carried
    (frontier config-octet-records record-octets lock-owned observed-name-octets
              profile state)
  (declare (xargs :stobjs state :mode :program
                  :guard (and (fn-cbor-octet-listp record-octets)
                              (fn-octet-list-listp config-octet-records)
                              (fn-octet-list-listp observed-name-octets))))
  (let* ((carried (and (boundp-global 'fn-store-sco-open state)
                       (f-get-global 'fn-store-sco-open state)))
         (opened-configs (and (boundp-global 'fn-store-cfg-open-configs state)
                              (f-get-global 'fn-store-cfg-open-configs state)))
         (config-records (fn-store-cfg-decode-records config-octet-records))
         (parsed (fn-cfg-decode-exact record-octets))
         (names (fn-store-octet-lists->strings observed-name-octets)))
    (cond ((or (not (consp carried)) (null opened-configs)
               (equal config-records :bad)
               (not (equal config-records opened-configs))
               ; PKT-601 (1): the candidate open is decided from the open's
               ; result, which names the frontier it opened at.
               (not (equal frontier
                           (fn-sf-frontier
                            (fn-sn-files (fn-sn-open-state (caddr carried)))))))
           (value nil))
          ((or (null config-records) (equal names :bad)
               (not (fn-record-parse-okp parsed)))
           (value (fn-native-admin-publication-result :refused :decode nil nil nil)))
          (t (value (fn-cfgc-cvec-native-admin-authorize
                     (fn-sco-records (car carried)) frontier config-records
                     (fn-record-parse-value parsed) lock-owned names profile
                     (cadr carried) (caddr carried)))))))

; The same authorization flattened for a caller that reads one form:
; (status reason generation name).  The generation and the filename are
; ACL2's (`fn-native-admin-publication-authorize'); the caller allocates
; neither.
(defun fn-store-cfg-publication
    (octet-records frontier config-octet-records record-octets lock-owned observed-name-octets
                   profile)
  (declare (xargs :mode :program))
  (let ((result (fn-store-cfg-native-admin-authorize
                 octet-records frontier config-octet-records record-octets
                 lock-owned observed-name-octets profile)))
    (list (fn-native-admin-publication-status result)
          (fn-native-admin-publication-reason result)
          (fn-native-admin-publication-generation result)
          (let ((name (fn-native-admin-publication-name result)))
            (if (stringp name) (fn-record-string-octets name) nil)))))

; The Store open from an extended checkpoint E, on both paths
; (checkpoint-cost): the configuration fold's result and the opened Store are
; computed once by fn-sco-store-open, and E with the pair stays in the
; global `fn-store-sco-open' for the owner, which installs from it without
; replaying again (fn-owner-recover-from-store-open, host/owner-host.lisp).
; The :ok test is the open's kind: fn-sco-finalize-okp-is-kind-ok says it is
; fn-sn-open-okp, without running the whole-state recognizer again.
; No barrier is fabricated here: Python must report each of five real fsync
; observations via fn-store-sn-io before this state is :ready.
; The open is `fn-sopc-classified-open' (books/store-open-pre-c1.lisp): a
; history whose identity fold stopped at a control record a pre-C1 image
; filed under its Newsgroups is refused by name (:refused, the refusal kept
; in the global `fn-store-open-refusal' for fn-store-open-refusal-text);
; every other history is `fn-sco-store-open' of E, as before
; (fn-sopc-classified-open-is-the-open-without-a-pre-c1-record).  The call is
; its twin `fn-rii-classified-open' (books/replay-identity-index.lisp, PRF-242:
; the history recognizer reads each record's kind once), EQUAL with no
; hypothesis (fn-rii-classified-open-is-classified-open).
;
; fn-store-sn-open-classified is that open over E and its CLASSIFIED open,
; computed by the caller: the
; recover entries below call the fused fn-rii-sco-extend-open
; (books/replay-identity-index.lisp section 7b, KEYSTONE
; fn-rii-sco-extend-open-is-extend-then-open: it is the extension and
; fn-rii-classified-open of it), whose drain does not check the resumed node
; again.
(defun fn-store-sn-open-classified (e classified config-records state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((refused (equal (car classified) :refused))
         (state (f-put-global 'fn-store-open-refusal
                              (if refused classified nil) state))
         (pair (if refused (list nil nil) classified))
         (replayed (car pair))
         (opened (cadr pair)))
    (if refused
        (let ((state (f-put-global 'fn-store-sco-open nil state)))
          (value :refused))
    (if (and (equal (fn-replay-result-kind replayed) :ok)
             (equal (fn-sn-open-kind opened) :ok)
             (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                    :recovering))
        (let* ((state (f-put-global 'fn-store-sn (fn-sn-open-state opened) state))
               (state (f-put-global 'fn-store-sn-hist-reload t state))
               (state (f-put-global 'fn-store-sn-record-octets nil state))
               (state (f-put-global 'fn-store-sn-record-debt nil state))
               (state (f-put-global 'fn-store-cfg
                                    (fn-cnode-config (fn-replay-result-node replayed))
                                    state))
               (state (f-put-global 'fn-store-sco-open (list e replayed opened) state))
               ; The configuration history this open folded: the offline
               ; request's authorization is carried only over the same one
               ; (fn-store-cfg-native-admin-authorize-carried).
               (state (f-put-global 'fn-store-cfg-open-configs config-records state)))
          (value :recovering))
      ;; A replay that stopped at an article its capacity cannot hold
      ;; refuses the open by name (books/store-open-replay-refusal.lisp
      ;; fn-sorr-refusal); any other stop stays a fault, its position and
      ;; reason kept for the fault's line (fn-sorr-stop-text).
      (let* ((records (fn-sco-records e))
             (refusal (fn-sorr-refusal replayed records config-records))
             (state (f-put-global 'fn-store-sco-open nil state))
             (state (f-put-global 'fn-store-open-refusal refusal state))
             (state (f-put-global 'fn-store-open-stop
                                  (and (not refusal)
                                       (fn-sorr-stop-text replayed records config-records))
                                  state)))
        (value (if refusal :refused :fault)))))))

(defun fn-store-sn-open-extended (e config-records frontier state)
  (declare (xargs :stobjs state :mode :program))
  (fn-store-sn-open-classified e (fn-rii-classified-open e config-records frontier)
                               config-records state))

; The operator's line for the refusal the last open recorded, or nil.
(defun fn-store-open-refusal-text (state)
  (declare (xargs :stobjs state :mode :program))
  (value (if (boundp-global 'fn-store-open-refusal state)
             (let ((refusal (f-get-global 'fn-store-open-refusal state)))
               (or (fn-sopc-refusal-text refusal) (fn-sorr-refusal-text refusal)))
           nil)))

; Where the last open's replay stopped, for the fault's line, or nil.
(defun fn-store-open-stop-text (state)
  (declare (xargs :stobjs state :mode :program))
  (value (if (boundp-global 'fn-store-open-stop state)
             (f-get-global 'fn-store-open-stop state)
           nil)))

; The repair verb's answer while its semantics wait on ember (PKT-444).
(defun fn-store-repair-control-text ()
  (declare (xargs :mode :program))
  *fn-sopc-repair-undecided-text*)

; The physical configuration and Store histories share transaction IDs, but
; have independent sequence spaces. ACL2 interleaves them at recovery, with
; configuration before a tied Store event, and carries that history in the
; opened Store. The final configuration remains available for administration.
;
; THE INTERN AT THE OPEN (records-flip; books/store-intern.lisp): the arena is
; emptied, then the decoded wire events become the store's rows, every
; article's payload sealed once (fn-intern-events under keyring nil and
; generation 0, the open's; KEYSTONES fn-intern-events-materializes,
; -are-store-events, -keep-coordinates, -contexts-okp).  The open runs over the
; rows; alpha of the opened history is the decoded journal
; (fn-intern-events-materializes), which is what the byte-store relation
; compares (books/byte-store-k0-recovery: fn-bs-recovered-rowsp).  The
; open's answer (fn-store-sn-recover-rows) is (mv nil KEYWORD state).
; tools/run_store.py recover makes three calls: fn-store-sn-recover-records
; decodes; the host clears the arena and calls the guard-verified
; fn-intern-events itself (records nil 0: the open's keyring and generation);
; fn-store-sn-recover-rows opens over the rows.  The native host
; (host/native/io.lisp fnn-bridge-recover) sends the history in CHUNKS
; (PKT-823; books/store-recover-stream.lisp): it clears the arena, then per
; chunk calls fn-store-decode-records (fn-srs-decode) and the guard-verified
; fn-srs-intern-step (the rows accumulated newest first), then fn-srs-rows and
; fn-store-sn-recover-rows.  KEYSTONE fn-srs-steps-are-one-step-of-the-
; concatenation: any chunking gives the rows and arena of one step over the
; whole history, which fn-srs-one-step-is-the-intern-of-the-decode says is
; the intern of the decoded history.  Neither :program entry calls an arena updater: one that
; did would carry ACL2's invariant-risk, run through its *1* body (every
; guard-verified callee re-checking its guard) and print a warning on
; standard output (flip-L6-2 LANEDUMP).
(defun fn-store-sn-recover-records (octet-records config-octet-records)
  (declare (xargs :mode :program
                  :guard (and (fn-octet-list-listp octet-records)
                              (fn-octet-list-listp config-octet-records))))
  (let ((records (fn-store-decode-records octet-records))
        (config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (equal records :bad) (equal config-records :bad)
            (null config-records))
        :bad
      records)))

(defun fn-store-sn-recover-rows (rows frontier config-octet-records state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-octet-list-listp config-octet-records)))
  (let ((config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (equal config-records :bad) (null config-records))
        (value :fault)
      ; The full open is the empty capture extended over the whole
      ; history, opened once (fn-store-sn-open-extended below).  It is
      ; the full open fn-cpo-open-observed and the full replay
      ; fn-cpr-replay by fn-sco-store-open-of-extended-capture
      ; (books/owner-checkpoint-open.lisp) with PREFIX = NIL.
      (let ((pair (fn-rii-sco-extend-open (fn-sco-capture config-records nil)
                                          config-records rows frontier)))
        (fn-store-sn-open-classified (car pair) (cadr pair) config-records state)))))

;; ---------------------------------------------------------------------------
;; P3: the state checkpoint (books/store-checkpoint-open.lisp,
;; books/store-checkpoint-codec.lisp).  The decoded checkpoint stays in the
;; ACL2 global `fn-store-sco-checkpoint' from its decode to the open and the
;; next publication; the host holds only its octets and the sequence S.

(defun fn-store-sco-current (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-store-sco-checkpoint state)
      (f-get-global 'fn-store-sco-checkpoint state)
    nil))

(defun fn-store-sco-clear (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-store-sco-checkpoint nil state))
         (state (f-put-global 'fn-store-sco-load nil state))
         (state (f-put-global 'fn-store-sco-open nil state)))
    (value :cleared)))

; PLAN: one frame (HEADER A B TRAILER) per segment in file order, as the
; host's range reads placed them (fnn-state-checkpoint-plan,
; host/native/io.lisp): the header and the trailer as octet lists, the
; chunk as the buffer's cells A..B, the chunks contiguous.  The schema-3
; reader (books/store-checkpoint-tables-reader.lisp fn-sct-load) reads the
; four table runs by index over the buffer, resolving every payload
; reference against the P table; no list of the file is built.  The answer
; is (:ok S) or (:refused REASON), REASON :layout, :header, :sequence,
; :segment, :truncated, :f-row, :close, :ref, :tree or :trailing.

; Whether ROWS hold an arena handle: host/checkpoint-host.lisp refuses a
; protected-prefix capture that does (:arena; the generation frames do not
; carry the arena).  The state checkpoint below carries it.
(defun fn-store-rows-hold-handles-p (rows)
  (declare (xargs :mode :program))
  (and (consp rows)
       (or (fn-held-p (car rows)) (fn-hstxa-p (car rows))
           (fn-store-rows-hold-handles-p (cdr rows)))))

; THE STATE CHECKPOINT UNDER THE RECORDS FLIP (lane checkpoint-arena,
; books/store-checkpoint-arena*.lisp): the file opens with the ARENA run A
; (the tag, the payload count, then the canonical payloads in batches),
; then the four tables of the capture of the CANONICAL rows (each row's
; payload position is its handle in that arena).  A file without the run
; (a tables-only file written before the flip) is refused by name (:arena)
; and the journal replays in full, which is authoritative.
;
; The load is three calls from host/native/io.lisp fnn-state-checkpoint-load,
; so that no :program entry updates the arena (an entry that did would carry
; ACL2's invariant-risk: run through its *1* body, every callee re-checking
; its guard, and a warning on standard output; flip-L6-2):
;   `fn-store-sco-decode' opens and verifies the A run (fn-scka-open-run:
;     the chain from the genesis, the tag, the count; the buffer is only
;     read) and answers (:arena START END COUNT), keeping the rest of the
;     plan and S in the global `fn-store-sco-load';
;   the host empties the arena and calls the guard-verified fn-scka-seal-n
;     over [START, END) a bounded number of payloads per call, each sealed
;     straight from its buffer range (fn-scka-seal-n-compose: the calls are
;     one loop);
;   `fn-store-sco-decode-finish' reads the four tables after the run
;     (fn-scka-finish: the run ended exactly at END, fn-sct-load, the F
;     row's S is the run's) and answers (:ok S) or (:refused REASON).
; The three calls are `fn-scka-load' (books/store-checkpoint-arena-load.lisp),
; whose KEYSTONE fn-scka-load-of-written-file says the file the writer
; produced loads to its tables with the arena exactly the canonical payloads.
(defun fn-store-sco-decode (plan fn-octets state)
  (declare (xargs :stobjs (fn-octets state) :mode :program))
  (let* ((o (fn-scka-open-run plan fn-octets))
         (state (f-put-global 'fn-store-sco-checkpoint nil state)))
    (if (and (consp o) (eq (car o) :ok))
        (let ((state (f-put-global 'fn-store-sco-load (list (nth 4 o) (nth 5 o)) state)))
          (mv nil (list :arena (nth 1 o) (nth 2 o) (nth 3 o)) state fn-octets))
      (let ((state (f-put-global 'fn-store-sco-load nil state)))
        (mv nil
            (list :refused (if (and (consp o) (consp (cdr o))) (cadr o) :malformed))
            state fn-octets)))))

(defun fn-store-sco-decode-finish (i end fn-octets state)
  (declare (xargs :stobjs (fn-octets state) :mode :program))
  (let* ((load (and (boundp-global 'fn-store-sco-load state)
                    (f-get-global 'fn-store-sco-load state)))
         (state (f-put-global 'fn-store-sco-load nil state))
         (loaded (if (and (consp load) (consp (cdr load)))
                     (fn-scka-finish (car load) (cadr load) i end fn-octets)
                   (list :refused :arena))))
    (if (and (consp loaded) (eq (car loaded) :ok) (consp (cdr loaded)))
        ; The tables mean the capture (fn-sct-capture-of-tables-of-capture):
        ; the 7-tuple the open extends, its event index rebuilt from E.
        (let* ((checkpoint (fn-sct-capture-of-tables (cadr loaded)))
               (state (f-put-global 'fn-store-sco-checkpoint checkpoint state))
               ; The F row's log position and frontier (a format-9 store's
               ; open starts its scan there: books/store-log-segments.lisp).
               (state (f-put-global 'fn-store-sco-log-position
                                    (list (fn-sct-tables-log (cadr loaded))
                                          (fn-sco-at 2 (fn-sct-tables-f (cadr loaded))))
                                    state)))
          (mv nil (list :ok (fn-sco-sequence checkpoint)) state fn-octets))
      (let* ((state (f-put-global 'fn-store-sco-checkpoint nil state))
             (state (f-put-global 'fn-store-sco-log-position nil state)))
        (mv nil
            (list :refused (if (and (consp loaded) (consp (cdr loaded)))
                               (cadr loaded)
                             :malformed))
            state fn-octets)))))

; The loaded checkpoint's F row: (LOG FRONTIER), LOG its log position
; (fn-sct-log-positionp: NIL or (K GENESIS)) and FRONTIER the txid frontier at
; its S; NIL when no checkpoint is loaded.
(defun fn-store-sco-log-position (state)
  (declare (xargs :stobjs state :mode :program))
  (value (and (boundp-global 'fn-store-sco-log-position state)
              (f-get-global 'fn-store-sco-log-position state))))

; The checkpoint's file name: the rename target of the byte program
; fn-bs-scp-program (step 6, (:rename :staging STAGE :root NAME)).
(defun fn-store-sco-file-name ()
  (declare (xargs :mode :program))
  (nth 4 (nth 6 (fn-bs-scp-program ".stage-checkpoint" '(0)))))

(defun fn-store-sco-segment-header-octets ()
  (declare (xargs :mode :program))
  *fn-scc-segment-header-octets*)

; The most octets one range read of the checkpoint takes: one whole segment
; written with segment size R, the profile's max-record-octets.
(defun fn-store-sco-segment-read-bound (profile)
  (declare (xargs :mode :program))
  (fn-scc-segment-max-octets (fn-bs-profile-max-record-octets profile)))

(defun fn-store-sco-trailer-octets ()
  (declare (xargs :mode :program))
  *fn-frame-trailer-octets*)

; The most octets of checkpoint file the reader holds in the buffer, from
; the profile (books/store-checkpoint-reader.lisp fn-sccr-file-read-bound:
; three times the history bound plus one segment's framing).
(defun fn-store-sco-file-read-bound (profile)
  (declare (xargs :mode :program))
  (fn-sccr-file-read-bound (fn-bs-profile-max-history-octets profile)
                           (fn-bs-profile-max-record-octets profile)))

; Whether the segment whose HEADER the host holds is read, given the
; octets read so far: (:ok EXTENT CHUNK-OCTETS), (:refused :header) or
; (:refused :exceeds-bound).  The host reads exactly EXTENT - 37 more
; octets on :ok and nothing on a refusal (fnn-state-checkpoint-plan).
(defun fn-store-sco-segment-admit (header total profile)
  (declare (xargs :mode :program))
  (fn-sccr-admit-segment header total
                         (fn-store-sco-segment-read-bound profile)
                         (fn-store-sco-file-read-bound profile)))

; The committed record count the open observed: the selected pack's
; coverage LOWER, or one past the last ACL2-bound transaction sequence.
(defun fn-store-sco-observed-count (sequences lower)
  (declare (xargs :mode :program))
  (let ((last-sequence (car (last sequences))))
    (if (and (consp sequences) (natp last-sequence) (natp lower))
        (max lower (+ 1 last-sequence))
      (nfix lower))))

; The open's choice (fn-sco-select) under the profile's K.
; A file without the arena run is refused by name (:arena ->
; reason=checkpoint-arena: books/store-checkpoint-arena-load.lisp
; fn-scka-select-named), never reported as corrupt.
(defun fn-store-sco-select (status sequence count profile)
  (declare (xargs :mode :program))
  (fn-scka-select-named status sequence count (fn-bs-profile-max-open-suffix profile)))

; The open from the loaded checkpoint and the suffix's ROWS.  It mirrors the
; full recover (fn-store-sn-recover-records, the intern,
; fn-store-sn-recover-rows): the host decodes the suffix with
; fn-store-sn-recover-records, interns it ON TOP of the arena the load left
; (fn-intern-events records nil 0: the canonical handles continue from the
; checkpoint's payload count; the arena is not emptied) and calls this entry
; over the rows (host/native/io.lisp fnn-recover-from-state-checkpoint).  The
; entry reads no arena.  The three calls are books/store-checkpoint-arena.lisp
; `fn-scka-recover-rows' over the host's extension (fn-rii-sco-extend, EQUAL
; to fn-sco-extend: fn-rii-sco-extend-is-sco-extend), whose KEYSTONE
; fn-scka-recover-from-checkpoint-is-full-recover says they are the full
; recover's extension and arena; the keystone
; fn-sn-recover-from-checkpoint-equals-full-recover is about the fn-sco-open
; of that extension.  The answer is (mv nil KEYWORD state).
(defun fn-store-sn-recover-from-checkpoint (rows frontier config-octet-records state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-octet-list-listp config-octet-records)))
  (let ((checkpoint (fn-store-sco-current state))
        (config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (null checkpoint) (equal rows :bad) (equal config-records :bad)
            (null config-records))
        (value :fault)
      ; The suffix is replayed once: E is fn-sco-open's extension, and the
      ; open and the configuration are read off it (fn-sco-open is
      ; fn-sco-finalize of E; fn-sco-replay-result is E's fold finished).
      (let ((pair (fn-rii-sco-extend-open checkpoint config-records rows frontier)))
        (fn-store-sn-open-classified (car pair) (cadr pair) config-records state)))))

; Each ROW's wire event (alpha, books/store-intern.lisp fn-row-wire-of: the
; payload read through the arena), encoded.
; A loop (PKT-877, lane serve-depth): the recursion took one control-stack
; frame per record.  :program, so no twin: the accumulator reversed once.
(defun fn-store-sco-encode-records-loop (records fn-arena acc)
  (declare (xargs :mode :program :stobjs fn-arena))
  (if (consp records)
      (fn-store-sco-encode-records-loop
       (cdr records) fn-arena
       (cons (fn-rcon-store-event-encode (fn-row-wire-of (car records) fn-arena)) acc))
    (revappend acc nil)))

(defun fn-store-sco-encode-records (records fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (fn-store-sco-encode-records-loop records fn-arena nil))

; The covered prefix's record octets, for the callers of the host's open
; that take the whole record list (pack publication, compaction, the
; owner).  Each is the canonical encoding of a record the checkpoint holds
; (fn-rcon-store-event-encode-is-store-event-encode, books/records-concrete).
(defun fn-store-sco-prefix-octets (fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-store-sco-encode-records (fn-sco-records (fn-store-sco-current state))
                                      fn-arena)))

; The covered prefix's records START .. START+COUNT-1, encoded as
; fn-store-sco-prefix-octets encodes them all: a streamed reader of the prefix
; (host/native/checkpoint.lisp fnn-log-reclaim-steps) takes a chunk at a time.
(defun fn-store-sco-prefix-octets-range (start count fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-store-sco-encode-records
          (take (nfix count) (nthcdr (nfix start) (fn-sco-records (fn-store-sco-current state))))
          fn-arena)))

; The covered prefix's LAST record's octets, or NIL: the owner reads its
; pending key statement off the history's last record, which after a log
; checkpoint open with an empty suffix is the prefix's (host/native/io.lisp
; fnn-history-last-record).
(defun fn-store-sco-last-record-octets (fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let ((records (fn-sco-records (fn-store-sco-current state))))
    (value (and (consp records)
                (fn-rcon-store-event-encode (fn-row-wire-of (car (last records)) fn-arena))))))

;; The verb's walk of the live rows (lane checkpoint-arena-3): each sealing
;; row's canonical payload length and SOURCE (its handle in the live arena,
;; or the octet list a composite carries), N rows per call, the state kept
;; in the global `fn-store-sco-pass' (ROWS' LACC SACC) between the calls
;; (books/store-checkpoint-arena-writer.lisp fn-scka-srcs-n;
;; fn-scka-srcs-n-compose: the calls are one walk; fn-scka-srcs-n-complete:
;; the walk is fn-scka-canon-lens and fn-scka-canon-srcs).  The walk READS
;; the arena.  `fn-store-sco-pass-begin' answers the row count,
;; `fn-store-sco-pass-step' whether the walk is done.
(defun fn-store-sco-pass-begin (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((records (fn-sf-records (fn-sn-files (f-get-global 'fn-store-sn state))))
         (state (f-put-global 'fn-store-sco-pass (list records nil nil) state)))
    (value (len records))))

(defun fn-store-sco-pass-step (n fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let* ((pass (and (boundp-global 'fn-store-sco-pass state)
                    (f-get-global 'fn-store-sco-pass state)))
         (next (if (and (consp pass) (natp n))
                   (fn-scka-srcs-n (nth 0 pass) n (nth 1 pass) (nth 2 pass) fn-arena)
                 (list nil nil nil)))
         (state (f-put-global 'fn-store-sco-pass next state)))
    (value (atom (nth 0 next)))))

; The verb's pipeline setup from the recovered Store, after the walk above.
; Under the records flip the file is the arena run of the live rows'
; CANONICAL payloads and the tables of the capture of their CANONICAL rows.
; NEXT: the open left E (fn-store-sn-open-extended), the capture of the
; canonical rows of the rows it opened (the open interns at the canonical
; handles: fn-scka-recover-from-checkpoint-is-full-recover), with H0 their
; canonical payload count, the walk's length count when E covers every row;
; NEXT is E extended over the canonical rows after it
; (books/store-checkpoint-arena-writer.lisp fn-scka-next-checkpoint, KEYSTONE
; fn-scka-next-checkpoint-is-capture), as the owner's publication takes it:
; the history is not canonicalized again (before checkpoint-arena-3 the
; verb canonicalized every row, alpha and the intern, to compare with E).
; Without E, the capture of fn-scka-canon-rows.  Then the arena run's
; setup from the walk's lengths (fn-scka-lens-setup) and
; `fn-scka-publication-setup' (books/store-checkpoint-arena-writer.lisp: the
; table pipeline's fn-ockp-setup with the decision by name over the whole
; file's octets, the arena run's included) before anything is allocated.
; The entry READS the arena only.  The answer is (SETUP S ARUN): SETUP's
; first element is :unencodable, (:deferred REASON ESTIMATE BOUND) or
; (:plan ESTIMATE); ARUN is (N COUNT STATE0), the arena run's payload count,
; segment count and first step state (fn-scka-initial-state over the walk's
; SOURCES and the batches); host/native/io.lisp fnn-command-state-checkpoint
; then loops on fn-scka-write-step (the arena run, first: each payload
; copied from its source, never through alpha) and fn-ockp-step (the four
; tables) into the same staged file.  KEYSTONES:
; fn-scka-write-run-is-run-segments (the run's octets) and the pipeline's
; fn-ockp-run-writes-the-file (the tables').  LOG: the record log's
; position at S (a format-9 store rotated at this capture; NIL otherwise),
; the F row's (fn-sct-log-positionp).
(defun fn-store-sco-publish-setup (segment-octets budget free revision log fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let* ((st (f-get-global 'fn-store-sn state))
         (records (fn-sf-records (fn-sn-files st)))
         (configs (fn-sn-config-history st))
         (pass (and (boundp-global 'fn-store-sco-pass state)
                    (f-get-global 'fn-store-sco-pass state)))
         (state (f-put-global 'fn-store-sco-pass nil state))
         (opened (and (boundp-global 'fn-store-sco-open state)
                      (f-get-global 'fn-store-sco-open state)))
         (e (car opened)))
    (if (not (and (consp pass) (atom (nth 0 pass))))
        (value (list (list :unencodable nil nil nil nil 0 0) 0 nil))
      (let* ((lens (reverse (nth 1 pass)))
             (srcs (reverse (nth 2 pass)))
             (next0 (and opened (equal (len (fn-sco-records e)) (len records))
                         (fn-scka-next-checkpoint e (len lens) configs records fn-arena)))
             (next (if (or (null next0) (equal next0 :bad))
                       (let ((canon (fn-scka-canon-rows records fn-arena 0)))
                         (if (equal canon :bad) :bad (fn-sco-capture configs canon)))
                     next0)))
        (if (equal next :bad)
            (value (list (list :unencodable nil nil nil nil 0 0) 0 nil))
          (let* ((ws (fn-scka-lens-setup lens segment-octets))
                 (setup (fn-scka-publication-setup next (fn-sf-frontier (fn-sn-files st))
                                                   revision log segment-octets budget free
                                                   (nth 3 ws))))
            (value (list setup (fn-sco-sequence next)
                         (list (nth 0 ws) (nth 2 ws)
                               (fn-scka-initial-state srcs (nth 1 ws) 0))))))))))

(defun fn-store-sn-domain (state)
  ; The allocation domain the live node carries: every name ever created.
  (declare (xargs :stobjs state :mode :program))
  (fn-state-groups (fn-node-acceptance (fn-sn-node (f-get-global 'fn-store-sn state)))))

(defun fn-store-sn-capacity (state)
  ; The retention charge capacity the live node carries: the replayed
  ; configuration's (`operator capacity'), 0 before any configuration is
  ; replayed.  The checkpoint host captures, decodes and restores under this
  ; value, the same node `fn-store-sn-domain' reads, so a checkpoint binds
  ; the capacity the store actually runs under.
  (declare (xargs :stobjs state :mode :program))
  (fn-retain-capacity (fn-node-retention (fn-sn-node (f-get-global 'fn-store-sn state)))))

(defun fn-store-cfg-generation (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cfg-generation (f-get-global 'fn-store-cfg state))))

(defun fn-store-cfg-join-names (names)
  ; Names as one octet list separated by LF, which no group name contains.
  (declare (xargs :mode :program))
  (if (consp names)
      (append (fn-record-string-octets (car names))
              (if (consp (cdr names)) (cons 10 (fn-store-cfg-join-names (cdr names))) nil))
    nil))

(defun fn-store-cfg-served (state)
  ; The served table at the live generation.
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-cnode-served-of (f-get-global 'fn-store-cfg state)))))

(defun fn-store-cfg-domain (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names (fn-store-sn-domain state))))

; One operator reconfiguration: a single create or retire, stamped with the
; host's clock observation, admitted by exactly the predicate replay applies
; (`fn-cnode-record-acceptablep' against the live node's reservation total,
; the RFC 3977 section 3.1 ceiling and an idle node).  The answer is :ok with
; the record octets left in `fn-store-cfg-last-octets', or :refused with the
; reason in `fn-store-cfg-last-reason'.  Nothing here mutates the store: the
; record becomes durable in Python and is replayed at the next open.
(defun fn-store-cfg-reconfigure (kind name-octets n monotonic wall state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (f-get-global 'fn-store-sn state))
         (cfg (f-get-global 'fn-store-cfg state))
         (node (fn-sn-node s))
         (cn (fn-cnode-make node cfg))
         (state (f-put-global 'fn-store-cfg-last-octets nil state)))
    (if (not (equal (fn-sf-phase (fn-sn-files s)) :ready))
        (let ((state (f-put-global 'fn-store-cfg-last-reason :not-ready state)))
          (value :refused))
      (if (not (fn-cbor-octet-listp name-octets))
          (let ((state (f-put-global 'fn-store-cfg-last-reason :group-name state)))
            (value :refused))
        (let* ((name (fn-store-octets->string name-octets))
               (generation (+ 1 (fn-cfg-generation cfg)))
               (deltas (cond ((equal kind :create-group)
                              (list (fn-cfg-create-group name *fn-cfg-default-policy-id*)))
                             ((equal kind :remove-group)
                              (list (fn-cfg-remove-group name)))
                             ; R6.  The capacity delta.  Admissibility is
                             ; `books/config''s own rule, checked here against
                             ; the LIVE node's reservation total by the same
                             ; `fn-cnode-record-acceptablep' replay applies --
                             ; no second owner of the bound.
                             ((equal kind :set-capacity)
                              (list (fn-cfg-set-capacity (nfix n))))
                             (t nil)))
               (stamp (fn-clock-observation (nfix monotonic) (nfix wall) 0 t))
               (record (fn-cfg-record-make (fn-cfg-generation cfg)
                                           (fn-state-next-txid (fn-node-acceptance node))
                                           generation deltas stamp)))
          (if (null deltas)
              (let ((state (f-put-global 'fn-store-cfg-last-reason :delta-kind state)))
                (value :refused))
            (if (fn-cnode-record-acceptablep cn record (fn-cnode-line-ceiling))
                (let* ((state (f-put-global 'fn-store-cfg-last-octets
                                            (fn-cfg-encode record) state))
                       (state (f-put-global 'fn-store-cfg-last-reason nil state)))
                  (value :ok))
              (let ((state (f-put-global
                            'fn-store-cfg-last-reason
                            (or (fn-cfg-admissible-reason
                                 (fn-cfg-value cfg) generation stamp
                                 (fn-retain-reserved (fn-node-retention node))
                                 (fn-cnode-line-ceiling) deltas)
                                (if (consp (fn-node-stage node)) :group-staged :record))
                            state)))
                (value :refused)))))))))

; -----------------------------------------------------------------------------
; Peer records (specs/peering.md section 1.2; `fn peer add|remove|list').
;
; The CLI hands over the operator's words and nothing else: the record shape,
; its well-formedness, the delta, the admissibility test and the record octets
; are all decided here, by `books/peer-config' and the same
; `fn-cnode-record-acceptablep' that `group create' uses and that replay will
; apply to the stored record.  A malformed record is `:refused' with a named
; reason before any generation is spent.

(defun fn-store-cfg-peer-record (name-octets path-octets host-octets port
                                 in-groups-octets in-max-octets in-inflight
                                 out-groups-octets out-streaming out-max-queue
                                 out-backoff auth-kind auth-octets)
  ; The typed record the operator's words denote, or nil.  `port' 0 selects a
  ; BP transport whose eid is `host-octets'; an empty inbound or outbound
  ; group pattern selects the absent half; an inbound bound of 0 selects
  ; *fn-record-max-payload*, the largest article this store can hold.
  (declare (xargs :mode :program))
  (let ((name (fn-store-octets->string name-octets))
        (path (fn-store-octets->string path-octets))
        (endpoint (fn-store-octets->string host-octets))
        (ingroups (fn-store-octets->string in-groups-octets))
        (outgroups (fn-store-octets->string out-groups-octets))
        (auth (fn-store-octets->string auth-octets)))
    (if (or (equal name :bad) (equal path :bad) (equal endpoint :bad)
            (equal ingroups :bad) (equal outgroups :bad) (equal auth :bad))
        nil
      (let ((p (fn-cfg-peer-make
                name path
                (if (posp port)
                    (list :nntp endpoint port)
                  (list :bp endpoint))
                (if (equal ingroups "")
                    nil
                  ; An unsaid inbound bound (0) is the record layer's own
                  ; ceiling.  `fn-cfg-peer-inboundp' refuses anything above
                  ; *fn-record-max-payload*, so a default typed into the CLI
                  ; would be a second owner of that number -- and the one
                  ; that was there (1048576, 32 times the ceiling) refused
                  ; every `peer add' made with the defaults.
                  (list ingroups
                        (if (posp in-max-octets)
                            in-max-octets
                          *fn-record-max-payload*)
                        (nfix in-inflight)))
                (if (equal outgroups "")
                    nil
                  (list outgroups (and out-streaming t) (nfix out-max-queue)
                        (nfix out-backoff)))
                (list (if (equal auth-kind :principal) :principal :source-address)
                      auth))))
        (if (fn-cfg-peerp p) p nil)))))

(defun fn-store-cfg-peer-delta-record (deltas monotonic wall state)
  ; The configuration record carrying one peer delta, admitted by the
  ; predicate replay applies.  :ok leaves the octets in
  ; `fn-store-cfg-last-octets'; :refused leaves the reason in
  ; `fn-store-cfg-last-reason'.
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (f-get-global 'fn-store-sn state))
         (cfg (f-get-global 'fn-store-cfg state))
         (node (fn-sn-node s))
         (cn (fn-cnode-make node cfg))
         (state (f-put-global 'fn-store-cfg-last-octets nil state))
         (generation (+ 1 (fn-cfg-generation cfg)))
         (stamp (fn-clock-observation (nfix monotonic) (nfix wall) 0 t))
         (record (fn-cfg-record-make (fn-cfg-generation cfg)
                                     (fn-state-next-txid (fn-node-acceptance node))
                                     generation deltas stamp)))
    (if (not (equal (fn-sf-phase (fn-sn-files s)) :ready))
        (let ((state (f-put-global 'fn-store-cfg-last-reason :not-ready state)))
          (value :refused))
      (if (fn-cnode-record-acceptablep cn record (fn-cnode-line-ceiling))
          (let* ((state (f-put-global 'fn-store-cfg-last-octets
                                      (fn-cfg-encode record) state))
                 (state (f-put-global 'fn-store-cfg-last-reason nil state)))
            (value :ok))
        (let ((state (f-put-global
                      'fn-store-cfg-last-reason
                      (or (fn-cfg-admissible-reason
                           (fn-cfg-value cfg) generation stamp
                           (fn-retain-reserved (fn-node-retention node))
                           (fn-cnode-line-ceiling) deltas)
                          :record)
                      state)))
          (value :refused))))))

; D23: the boundary's carried-source list (books/peer-authored-accept.lisp
; *fn-pa-carries-slot*), one row per principal after the record's rows.  A
; principal is the 64 lowercase hexadecimal characters HDR :fn-verified and
; `auth-principal' use; anything else refuses the delta as :carries.
(defun fn-store-cfg-carries-rows (name carries)
  (declare (xargs :mode :program))
  (if (consp carries)
      (let ((hex (fn-store-octets->string (car carries)))
            (rest (fn-store-cfg-carries-rows name (cdr carries))))
        (if (or (equal hex :bad) (equal rest :bad)
                (not (equal (length hex) 64))
                (not (subsetp (coerce hex 'list)
                              (coerce "0123456789abcdef" 'list))))
            :bad
          (cons (fn-cfg-row-make name "carries-principal" hex 0) rest)))
    nil))

(defun fn-store-cfg-set-peer (name-octets path-octets host-octets port
                              in-groups-octets in-max-octets in-inflight
                              out-groups-octets out-streaming out-max-queue
                              out-backoff auth-kind auth-octets carries
                              monotonic wall state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((p (fn-store-cfg-peer-record
             name-octets path-octets host-octets port in-groups-octets
             in-max-octets in-inflight out-groups-octets out-streaming
             out-max-queue out-backoff auth-kind auth-octets))
         (extra (and p (fn-store-cfg-carries-rows (fn-cfg-peer-name p)
                                                  carries))))
    (cond ((null p)
           (let ((state (f-put-global 'fn-store-cfg-last-reason :peer-record state)))
             (value :refused)))
          ((equal extra :bad)
           (let ((state (f-put-global 'fn-store-cfg-last-reason :carries state)))
             (value :refused)))
          (t
           (fn-store-cfg-peer-delta-record
            (list (fn-cfg-set-peer (fn-cfg-peer-name p)
                                   (append (fn-cfg-peer-rows p) extra)))
            monotonic wall state)))))

; The node's own policy slots (`fn policy set|get`).  The one peering needs
; is "path-identity": `fn-peer-local-identity` (books/peer-inbound.lisp)
; reads exactly this slot, and RFC 5537 section 3.5 loop suppression is
; INERT while it is unset -- an unset slot reads as the empty string, and
; `fn-path-names-p` never matches the empty identity, so a node cannot
; recognise its own name in a Path.  Measured on the two-node gate,
; 2026-09-20: both nodes accepted an article whose Path named them, because
; nothing on this tree could ever write the slot.  `fn-store-prov-post`
; reads the same slot and substituted "local" for it.
;
; The delta, its admissibility and the record octets are `books/config`'s,
; through the same `fn-cnode-record-acceptablep` `peer add` and
; `group create` use.
(defun fn-store-cfg-set-policy (slot-octets id-octets monotonic wall state)
  (declare (xargs :stobjs state :mode :program))
  (let ((slot (fn-store-octets->string slot-octets))
        (id (fn-store-octets->string id-octets)))
    (if (or (equal slot :bad) (equal id :bad) (equal slot ""))
        (let ((state (f-put-global 'fn-store-cfg-last-reason :policy-slot state)))
          (value :refused))
      (fn-store-cfg-peer-delta-record (list (fn-cfg-set-policy slot id))
                                      monotonic wall state))))

(defun fn-store-cfg-policy (slot-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((slot (fn-store-octets->string slot-octets)))
    (if (equal slot :bad)
        (value nil)
      (value (fn-record-string-octets
              (fn-cfg-policy (fn-cfg-value (f-get-global 'fn-store-cfg state))
                             slot))))))

(defun fn-store-cfg-remove-peer (name-octets monotonic wall state)
  (declare (xargs :stobjs state :mode :program))
  (let ((name (fn-store-octets->string name-octets)))
    (if (equal name :bad)
        (let ((state (f-put-global 'fn-store-cfg-last-reason :peer-name state)))
          (value :refused))
      (if (null (fn-cfg-peer-find name (fn-cfg-peers
                                        (fn-cfg-value (f-get-global 'fn-store-cfg state)))))
          (let ((state (f-put-global 'fn-store-cfg-last-reason :no-such-peer state)))
            (value :refused))
        (fn-store-cfg-peer-delta-record (list (fn-cfg-remove-peer-delta name))
                                        monotonic wall state)))))

; The listing.  Names first, then one slot at a time in the codec's own
; vocabulary (books/peer-config, `fn-cfg-peer-rows'): nothing about a peer is
; rendered by Python from a shape it guessed.  The enumeration was a
; :program-mode copy of the same fold and is now books/peer-config's
; `fn-cfg-peer-names', so the peer table has one way of being listed.
(defun fn-store-cfg-peer-names (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-cfg-peer-names
           (fn-cfg-peers (fn-cfg-value (f-get-global 'fn-store-cfg state)))))))

(defun fn-store-txn-pairs-octets (pairs)
  (declare (xargs :mode :program))
  (if (consp pairs)
      (cons (list (car (car pairs)) (fn-record-string-octets (nth 1 (car pairs))))
            (fn-store-txn-pairs-octets (cdr pairs)))
    nil))

; The operator's `peer list' report, rendered by books/native-admin-peer's
; `fn-native-admin-peer-report' over the replayed configuration: the one the
; native `peer list' prints (host/native-admin-host.lisp).  Python writes the
; octets out and renders no field.
(defun fn-store-cfg-peer-report (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-native-admin-peer-report
          (fn-cfg-peers (fn-cfg-value (f-get-global 'fn-store-cfg state))))))

; The fixed-width configuration record filename (`fn-native-admin-config-name',
; books/native-admin-shape.lisp), nil beyond its width.
(defun fn-store-cfg-record-name (generation)
  (declare (xargs :mode :program))
  (let ((name (fn-native-admin-config-name generation)))
    (if (stringp name) (fn-record-string-octets name) nil)))

; One bounded observation of the final transaction namespace, as the native
; host asks it (`fn-store-txn-observation-selected', lower bound 0): :invalid,
; or each (sequence name-octets) pair in order.  The grammar, the bound and
; the gap policy are `fn-profile-txn-observation''s.
(defun fn-store-txn-observation-octets (observed maximum)
  (declare (xargs :mode :program))
  (let ((value (fn-store-txn-observation-selected observed maximum 0)))
    (if (and (consp value) (equal (car value) :ok))
        (fn-store-txn-pairs-octets (nth 2 value))
      :invalid)))

(defun fn-store-cfg-last-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-store-cfg-last-octets state)))

(defun fn-store-cfg-last-reason (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-store-cfg-last-reason state)))

(defun fn-store-sn-io (operation result state)
  (declare (xargs :stobjs state :mode :program))
  ; fn-rcon-sn-io-is-sn-io (books/records-concrete): fn-sn-io with the
  ; concrete record dispatchers.
  ; :log-reserve and :log-order are the record log's two composite steps
  ; (books/store-log-route.lisp fn-olr-sn-reserve / fn-olr-sn-order: the file
  ; route's success sequences, by definition), called on a format-9 store.
  (let* ((s (f-get-global 'fn-store-sn state))
         (next (case operation
                 (:log-reserve (fn-olr-sn-reserve s))
                 (:log-order (fn-olr-sn-order s))
                 (t (fn-rcon-sn-io s operation result)))))
    (let ((state (f-put-global 'fn-store-sn next state)))
      (value (fn-sf-phase (fn-sn-files next))))))

;
; THE POST ENTRY (records-flip): the duplicate test reads the stored article's
; bytes through the arena (books/store-intern.lisp fn-store-existing-action,
; KEYSTONE fn-store-existing-action-is-the-verdict-over-alpha: D25's verdict
; over alpha of the acceptance articles), and the prepare is
; fn-store-prepare-carried-next then the host's seal, which is
; fn-store-prepare-interned-carried, which on a related store is
; fn-store-prepare-interned (KEYSTONES -is-intern-then-prepare,
; -refusal-keeps-the-arena, -acceptance-seals-one-payload): the row is
; interned at the arena's count and the payload sealed only when the store
; staged it, so a refused POST retains no bytes.  The answer is
; (mv nil KEYWORD fn-arena state).
(defun fn-store-sn-prepare (msgid-octets payload group-codes id-octets
                             subject-octets evidence-octets charge observation
                             fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program
                  :guard (and (fn-cbor-octet-listp msgid-octets)
                              (fn-cbor-octet-listp payload)
                              (fn-cbor-octet-listp id-octets)
                              (fn-cbor-octet-listp subject-octets)
                              (fn-cbor-octet-listp evidence-octets))))
  (let* ((s (f-get-global 'fn-store-sn state))
         (groups (fn-store-groups-from-codes group-codes (fn-store-sn-domain state))))
    ; The fields' checks are ACL2's (books/post-fields.lisp
    ; fn-pfld-article-inputsp): the Message-ID grammar, the codec's payload
    ; ceiling, the resolved groups, the record's metadata domain, the charge.
    (if (or (not (fn-octet-listp payload))
            (not (fn-pfld-article-inputsp msgid-octets (len payload) groups
                                          id-octets subject-octets
                                          evidence-octets charge)))
        (mv nil :invalid fn-arena state)
      ; A name in the domain but not served at the live generation (a retired
      ; group) is refused by the prepare itself (fn-psrv-store-prepare-next,
      ; lane prepare-served): the host makes no served test of its own.
      (let* ((msgid (fn-store-octets->string msgid-octets))
             (existing (fn-store-existing-action msgid payload groups s fn-arena)))
        (if existing
            (mv nil existing fn-arena state)
          (let* ((record (fn-sn-article-record
                          s observation msgid payload groups
                          (fn-store-octets->string id-octets)
                          (fn-store-octets->string subject-octets)
                          (fn-store-octets->string evidence-octets)
                          charge)))
            ; The carried prepare (books/store-prepare-carried.lisp): the
            ; row interned at the arena's count, staged by fn-pcar-spc-prepare;
            ; no replay of the history.  The entry READS the arena only, so it
            ; carries no invariant-risk and runs compiled; the answer
            ; (:seal OCTETS) names the payload the host then seals with one
            ; call of fn-arena-seal-list (host/native/io.lisp
            ; fnn-bridge-prepare, tools/run_store.py prepare).  KEYSTONES
            ; fn-store-prepare-interned-carried-is-next-then-seal (the two
            ; calls are the carried entry) and
            ; fn-store-prepare-interned-carried-is-prepare-interned (under
            ; fn-snt-relation, books/store-intern.lisp's entry).
            (if (equal record :clock-unusable)
                (mv nil :clock-unusable fn-arena state)
              (let ((next (fn-psrv-store-prepare-next
                           (f-get-global 'fn-store-cfg state)
                           s record (fn-arena-count fn-arena))))
                (if (equal next s)
                    (mv nil :refused fn-arena state)
                  (let ((state (f-put-global 'fn-store-sn next state)))
                    (mv nil (list :seal (fn-record-payload record))
                        fn-arena state)))))))))))

; A semantic refusal consumes the already durable allocator reservation using
; the proved composition transition, which advances the same live node to the
; durable frontier.  It is never a host-side frontier rewind.
(defun fn-store-sn-refuse-reservation (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (f-get-global 'fn-store-sn state))
         (files (fn-sn-files s))
         (next (fn-sn-refuse-reservation s (1- (fn-sf-frontier files)))))
    (if (and (equal (fn-sf-phase files) :reserved)
             (not (equal next s))
             (equal (fn-sf-phase (fn-sn-files next)) :ready))
        (let ((state (f-put-global 'fn-store-sn next state))) (value :refused))
      (value :fault))))

; Prepare a retention delta in the canonical Store transaction namespace.
; KIND is selected by ACL2 vocabulary; the native host supplies only bounded
; fields already authored by the workflow decision.
(defun fn-store-sn-prepare-retention
  (kind id-octets subject-octets evidence-octets charge state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (f-get-global 'fn-store-sn state))
         (node (fn-sn-node s)))
    ; books/post-fields.lisp fn-pfld-retention-inputsp.
    (if (not (fn-pfld-retention-inputsp kind id-octets subject-octets
                                        evidence-octets charge))
        (value :invalid)
      (let* ((txid (fn-state-next-txid (fn-node-acceptance node)))
             (event (fn-store-retention-event-make
                     kind (fn-sn-identity-next s) txid txid
                     (fn-store-octets->string id-octets)
                     (fn-store-octets->string subject-octets)
                     (fn-store-octets->string evidence-octets) charge))
             (next (fn-sn-prepare-retention s event)))
        (if (equal next s)
            (value :refused)
          (let ((state (f-put-global 'fn-store-sn next state)))
            (value :prepared)))))))

; This is enabled only before the host has attempted final-name publication.  The proved composition transition resolves the exact
; candidate through the file kernel and actual node abort transition.
; Link/directory uncertainty remains fenced for observed replay instead.
(defun fn-store-sn-known-abort (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (f-get-global 'fn-store-sn state))
         (files (fn-sn-files s))
         (next (fn-sn-known-abort s)))
    (if (and (member-equal (fn-sf-phase files)
                           '(:record-staged :record-data-durable))
             (not (equal next s))
             (equal (fn-sf-phase (fn-sn-files next)) :ready))
        (let ((state (f-put-global 'fn-store-sn next state)))
          (value :aborted))
      (value :fault))))

(defun fn-store-sn-pending-octets (fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let ((record (fn-sf-record-candidate
                 (fn-sn-files (f-get-global 'fn-store-sn state)))))
    ; The staged ROW's wire event (alpha: fn-row-wire-of, the payload read
    ; through the arena), encoded: fn-rcon-store-event-encode-is-store-event-
    ; encode (books/records-concrete).  The frame is the journal's bytes for
    ; the wire record the POST carried (fn-intern-events-materializes).
    (value (if record
               (fn-rcon-store-event-encode (fn-row-wire-of record fn-arena))
             nil))))

; The staged record's sequence: the developer `store post' names its
; transaction file from it (books/store-budget-naming.lisp).
(defun fn-store-sn-pending-sequence (state)
  (declare (xargs :stobjs state :mode :program))
  ; fn-rcon-sbud-pending-sequence-is-sbud-pending-sequence (books/records-concrete).
  (value (fn-rcon-sbud-pending-sequence (f-get-global 'fn-store-sn state))))

(defun fn-store-sn-finish (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (f-get-global 'fn-store-sn state))
         (before-files (fn-sn-files before))
         ; fn-ccar-sn-finish-is-sn-finish (books/owner-commit-carried.lisp):
         ; equal to fn-sn-finish on every input.  fn-sn-finish finds the
         ; completion record by fn-sn-find-record, which runs the event
         ; recognizer over every record of the history, so N commits cost
         ; N^2 recognitions (bounds-p5 2026-09-25: 5.2, 19.2 and 77.4 s of
         ; commit CPU for N = 250, 500 and 1000); the carried finish steps
         ; to the record's sequence position and reads it by shape.
         (next (fn-ccar-sn-finish before))
         (after-files (fn-sn-files next)))
    ; fn-sn-finish is deliberately a no-op away from :completing.  The host
    ; reports success only for the transition that consumes this exact pending
    ; completion and appends one acknowledgement, never for a stale ready
    ; state or repeated call.
    (if (and (equal (fn-sf-phase before-files) :completing)
             (equal (fn-sf-phase after-files) :ready)
             (equal (len (fn-sf-successes after-files))
                    (1+ (len (fn-sf-successes before-files)))))
        (let ((state (f-put-global 'fn-store-sn next state))) (value :durable))
      (value :fault))))

(defun fn-store-sn-article-count (state)
  (declare (xargs :stobjs state :mode :program))
  (value (len (fn-state-articles
               (fn-node-acceptance
                (fn-sn-node (f-get-global 'fn-store-sn state)))))))

(defun fn-store-sn-next-txid (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-state-next-txid
          (fn-node-acceptance
           (fn-sn-node (f-get-global 'fn-store-sn state))))))

(defun fn-store-sn-existing-action (msgid-octets payload group-codes fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program
                  :guard (and (fn-cbor-octet-listp msgid-octets)
                              (fn-cbor-octet-listp payload))))
  (let ((groups (fn-store-groups-from-codes group-codes (fn-store-sn-domain state))))
    (if (or (not (fn-pfld-lookup-inputsp msgid-octets groups))
            (not (fn-octet-listp payload)))
        (value :absent)
      ; books/store-intern.lisp fn-store-existing-action-is-the-verdict-over-alpha.
      (let ((action (fn-store-existing-action
                     (fn-store-octets->string msgid-octets) payload groups
                     (f-get-global 'fn-store-sn state) fn-arena)))
        (value (if action action :absent))))))

(defun fn-store-sn-group-next (code state)
  (declare (xargs :stobjs state :mode :program))
  (let ((group (if (natp code) (fn-store-group-name code (fn-store-sn-domain state)) nil)))
    (value (if group
               (fn-next-number group
                               (fn-state-nexts
                                (fn-node-acceptance
                                 (fn-sn-node (f-get-global 'fn-store-sn state)))))
             0))))

(defun fn-store-sn-pin-count (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-rtf-pin-count (f-get-global 'fn-store-sn state))))

(defun fn-store-sn-reserved (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-rtf-reserved (f-get-global 'fn-store-sn state))))

(defun fn-store-sn-lookup (msgid-octets fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program
                  :guard (fn-cbor-octet-listp msgid-octets)))
  (if (not (fn-af-message-idp msgid-octets))
      (mv nil nil fn-hist state)
    ; The row's HANDLE through the history stobj's Message-ID answer, not the
    ; acceptance state's article (fn-apr-payload-of-is-the-article-payload,
    ; books/acceptance-payload-ref.lisp: equal at rest under R), and its
    ; bytes read through the arena (books/store-intern.lisp fn-handle-bytes:
    ; no bytes for a handle outside it).
    (let ((store (f-get-global 'fn-store-sn state)))
      (mv-let (fn-hist state) (fn-host-hist-sync store fn-hist state)
        (mv nil (fn-handle-bytes (fn-apr-payload-of (fn-store-octets->string msgid-octets)
                                                    store fn-hist)
                                 fn-arena)
            fn-hist state)))))

(defun fn-store-sn-lookup-foundp (msgid-octets fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program
                  :guard (fn-cbor-octet-listp msgid-octets)))
  (if (not (fn-af-message-idp msgid-octets))
      (mv nil nil fn-hist state)
    ; fn-apr-foundp-is-article-found (books/acceptance-payload-ref.lisp), under R.
    (let ((store (f-get-global 'fn-store-sn state)))
      (mv-let (fn-hist state) (fn-host-hist-sync store fn-hist state)
        (mv nil (fn-apr-foundp (fn-store-octets->string msgid-octets) store fn-hist)
            fn-hist state)))))

; -----------------------------------------------------------------------------
; The served statement query (decision D21)
;
; THE HOST LINE THE ASSURANCE RULE ASKS FOR.  fn-store-sn-statement below
; calls fn-sn-statement-lookup (books/store-node.lisp) on the value of the
; 'fn-store-sn global, and that function reads the carried index and nothing
; else: it does not walk the store, does not re-parse an article and does not
; verify a signature.  What licenses reading the index instead of the lace
; projection is fn-store-statement-lookup-is-the-lace-lookup
; (books/store-intern.lisp; since the records flip, the lace of the indexed
; rows' bytes read through the arena, under fn-rows-contexts-okp of those
; rows).  Its hypothesis fn-sn-indexedp holds
; of this global because fn-sn-initial-is-indexed establishes it at
; fn-store-sn-reset and every transition this file applies to the global --
; fn-sn-io, fn-sn-prepare, fn-sn-finish, fn-sn-refuse-reservation,
; fn-sn-known-abort, fn-sn-recover and fn-sn-set-keyring -- is proved to
; preserve it.

; The verification context.  A node that holds no key verifies no statement,
; so an unconfigured store answers every statement query with "absent" rather
; than with a guess: that is the fail-closed floor of specs/reconfiguration.md
; section 1.6, at the statement layer.  Installing a keyring recomputes the
; index over the whole store, which is correct -- a new keyring gives a new
; set of verified statements -- and is a reconfiguration event, not a served
; path.  The validity decision is ACL2's fn-prin-keyringp, called here; this
; file does not re-decide it.
(defun fn-store-sn-keyring-of-pairs (pairs)
  (declare (xargs :mode :program))
  (if (consp pairs)
      (let ((entry (car pairs)))
        (if (and (true-listp entry) (equal (len entry) 2))
            (let ((rest (fn-store-sn-keyring-of-pairs (cdr pairs))))
              (if (equal rest :bad)
                  :bad
                (cons (cons (car entry) (car (cdr entry))) rest)))
          :bad))
    (if (null pairs) nil :bad)))

; The entry is books/store-intern.lisp fn-store-set-keyring: every row's
; context recomputed from its bytes, read through the arena, under the new
; keyring and generation (the one reconfiguration that re-reads bytes); the
; arena is read, not changed.
(defun fn-store-sn-set-keyring (pairs fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let ((keyring (fn-store-sn-keyring-of-pairs pairs)))
    (if (or (equal keyring :bad) (not (fn-prin-keyringp keyring)))
        (value :invalid)
      (let ((state (f-put-global
                    'fn-store-sn
                    (fn-store-set-keyring (f-get-global 'fn-store-sn state)
                                          keyring fn-arena)
                    state)))
        (value :configured)))))

(defun fn-store-sn-keyring-size (state)
  (declare (xargs :stobjs state :mode :program))
  (value (len (fn-sn-keyring (f-get-global 'fn-store-sn state)))))

(defun fn-store-sn-keyring-generation (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sn-keyring-generation (f-get-global 'fn-store-sn state))))

; Acceptance evidence carried by the ACL2 state.  Kind-4 results are durable
; historical evidence.  A legacy fn-r result is only a current-process
; observation and disappears on recovery because fn-r has no verdict bytes.
; This wrapper performs only Message-ID conversion and a carried-index lookup;
; it neither parses article bytes nor verifies a signature.  Present results
; are the reader-safe :fn-verified item octets.
(defun fn-store-sn-verdict (msgid-octets state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-af-message-idp msgid-octets))
      (value nil)
    (let ((verdict
           (fn-sn-verdict-lookup
            (f-get-global 'fn-store-sn state)
            (fn-store-octets->string msgid-octets))))
      (value (if verdict (fn-stx-verified-item verdict) nil)))))

; The query.  Absent is nil; present is the statement's canonical octets.
(defun fn-store-sn-statement (id-octets state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-octet-listp id-octets))
      (value nil)
    (let ((statement (fn-sn-statement-lookup
                      (f-get-global 'fn-store-sn state) id-octets)))
      (value (if statement (fn-stmt-encode statement) nil)))))

; The equivocation question, answered from the index's third list.  It is a
; DISCOVERY AID with a proved agreement to the lace
; (fn-store-equivocatorp-is-the-lace-equivocator, books/store-intern.lisp),
; never an independent
; authority.
(defun fn-store-sn-equivocator (creator-octets incarnation state)
  (declare (xargs :stobjs state :mode :program))
  (if (or (not (fn-octet-listp creator-octets)) (not (natp incarnation)))
      (value :invalid)
    (value (if (fn-sn-equivocatorp (f-get-global 'fn-store-sn state)
                                   creator-octets incarnation)
               :equivocator
             :single))))

; The number of bindings the index holds.  This is the served-path cost
; witness: fn-stx-index-lookup-cost-is-index-bounded bounds a lookup by this
; number, which grows by at most one per accepted article
; (fn-stx-index-grows-by-at-most-one-binding), where the lace projection it
; replaces is linear in the whole store.
(defun fn-store-sn-index-size (state)
  (declare (xargs :stobjs state :mode :program))
  (value (len (fn-stx-index-bindings
               (fn-sn-index (f-get-global 'fn-store-sn state))))))

; The staging sweep (books/store-sweep.lisp).  Python enumerates the staging
; directory and names what the live process still holds; which of those names
; may be unlinked is the book's decision, never Python's.  The answer is the
; removal names joined by LF, as fn-store-cfg-join-names joins group names.
; The names here are already octet lists (a staging file name is not a group
; name, so fn-store-cfg-join-names, which encodes strings, does not apply).
(defun fn-store-sn-join-octet-names (names)
  (declare (xargs :mode :program))
  (if (consp names)
      (append (car names)
              (if (consp (cdr names))
                  (cons 10 (fn-store-sn-join-octet-names (cdr names)))
                nil))
    nil))

(defun fn-store-sn-sweep-staging (observed held state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-sn-join-octet-names
          (car (fn-sn-sweep-staging (f-get-global 'fn-store-sn state)
                                    observed held)))))

; Native recovery consumes the structured result directly.  Unlike the older
; LF-joined adapter for Python, it cannot confuse an observed filename that
; contains LF with two distinct names.  The subject is fn-sn-sweep-round:
; one bounded observation, whether the directory held more, and the answer
; (:done|:again|:refused removals) that decides the host's next round
; (host/native/io.lisp, fnn-sweep-staging).
(defun fn-store-sn-sweep-round (observed overp held state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sn-sweep-round (f-get-global 'fn-store-sn state)
                            observed overp held)))

(defun fn-store-sn-staging-observation-limit (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sn-staging-observation-limit)))

; -----------------------------------------------------------------------------
; Provenance (books/provenance, books/provenance-codec)
;
; ACL2 decides the provenance of a locally posted article.  Before this lane
; `tools/run_store.py's `metadata' typed the constant b"unsigned-legacy-v0"
; here, which is a decision Python owned and the model only compared
; (AGENTS.md, one owner per decision).  These three wrappers hold no
; provenance logic: they read the live configuration, call `fn-prov-*' and
; marshal octets.

(defun fn-store-prov-post (state)
  ; The provenance of an article this node injected, decided by ACL2
  ; (books/post-fields.lisp fn-pfld-post-evidence: the principal, "local"
  ; when no <path-identity> is configured, and the form the store gets; KEYSTONE
  ; fn-pfld-post-evidence-is-admitted: the POST's field check admits it).  The
  ; host reads the live configuration's policy slot and generation.
  (declare (xargs :stobjs state :mode :program))
  (let ((cfg (f-get-global 'fn-store-cfg state)))
    (value (fn-pfld-post-evidence
            (fn-cfg-policy (fn-cfg-value cfg) "path-identity")
            (fn-cfg-generation cfg)))))

(defun fn-store-prov-describe (evidence-octets state)
  ; The lossless line the CLI prints for one stored evidence value.  A value
  ; written before this lane decodes as the `:legacy' kind and prints as
  ; itself; a wire form prints its fields.
  (declare (xargs :stobjs state :mode :program))
  (value (fn-record-string-octets
          (fn-prov-describe
           (fn-prov-of-wire (fn-record-octets-string evidence-octets))))))

(defun fn-store-prov-for-msgid (msgid-octets state)
  ; The provenance of the article with this Message-ID, from the LIVE node:
  ; the binding gives the obligation id, the retention pin gives the evidence
  ; the acceptance recorded.  NIL when the node holds no such binding or the
  ; pin has been released.  The lookup and the wire/legacy dispatch are ACL2's
  ; (books/provenance-inspect.lisp fn-provi-of-msgid); the host decodes the
  ; octets and relays.
  (declare (xargs :stobjs state :mode :program))
  (value (fn-provi-of-msgid (fn-sn-node (f-get-global 'fn-store-sn state))
                            (fn-store-octets->string msgid-octets))))

;; ---------------------------------------------------------------------------
;; Replay determinism (lane proto-determinism, 2026-09-27): the digest of the
;; state an open folded, `store ROOT digest' (host/native/io.lisp
;; fnn-command-store-digest).  Every digest is books/state-digest.lisp's over
;; the LOGICAL value (fn-sdg-canon: an object's value, never its layout):
;;   history    the history's rows as wire events, in log order
;;              (fn-sdg-rows-history): the log, independent of handles;
;;   pool       the payload arena's logical value (fn-sdg-arena-pool);
;;   field NAME each field of the Store node `fn-store-sn' (books/store-node.lisp
;;              fn-sn-make-v6's order), the derived indexes included;
;;   config     the replayed configuration `fn-store-cfg';
;;   canonical  history and the node's config-history: the log's content,
;;              what a peer holding the log recomputes;
;;   state      every line above: the whole folded state.
;; A difference between two opens of the same log names the field.

(defconst *fn-store-sn-digest-fields*
  '("groups" "capacity" "files" "node" "keyring" "index" "keyring-generation"
    "verdicts" "snapshots" "identity-next" "config-history" "consumer" "topic"
    "event-index"))

(defun fn-store-sn-digest-line (words digest)
  (declare (xargs :mode :program))
  (append (fn-record-string-octets (concatenate 'string "digest " words " "))
          (fn-sdg-hex digest) (list 10)))

(defun fn-store-sn-digest-fields (s names i)
  (declare (xargs :mode :program))
  (if (atom s)
      nil
    (append (fn-store-sn-digest-line
             (concatenate 'string "field "
                          (if (consp names) (car names)
                            (concatenate 'string "field-" (coerce (explode-atom i 10) 'string))))
             (fn-sdg-digest (car s)))
            (fn-store-sn-digest-fields (cdr s) (if (consp names) (cdr names) nil) (1+ i)))))

(defun fn-store-sn-replay-digest-report (fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let* ((s (and (boundp-global 'fn-store-sn state) (f-get-global 'fn-store-sn state)))
         (cfg (and (boundp-global 'fn-store-cfg state) (f-get-global 'fn-store-cfg state)))
         (rows (fn-sf-records (fn-sn-files s)))
         (history (fn-sdg-rows-history rows fn-arena))
         (config-history (fn-sdg-digest (nth 10 s)))
         (count (fn-arena-count fn-arena))
         (body (append
                (fn-store-sn-digest-line
                 (concatenate 'string "history records=" (coerce (explode-atom (len rows) 10) 'string))
                 history)
                (fn-store-sn-digest-line
                 (concatenate 'string "pool payloads=" (coerce (explode-atom count 10) 'string))
                 (fn-sdg-arena-pool fn-arena))
                (fn-store-sn-digest-fields s *fn-store-sn-digest-fields* 0)
                (fn-store-sn-digest-line "config" (fn-sdg-digest cfg))
                (fn-store-sn-digest-line "canonical"
                                         (fn-digest (append history config-history))))))
    ; Format 10: the genesis record the open read (books/store-genesis.lisp),
    ; printed AFTER the state line and outside it: no folded field reads a
    ; genesis field (the history salt keys only the owner's derived index),
    ; so two stores holding the same records under different genesis
    ; records print every line above equal and this one different
    ; (tests/test_native_replay_determinism.py).
    (value (append body (fn-store-sn-digest-line "state" (fn-digest body))
                   (fn-store-sn-digest-line
                    "genesis"
                    (fn-sdg-digest (and (boundp-global 'fn-store-genesis state)
                                        (f-get-global 'fn-store-genesis state))))))))
