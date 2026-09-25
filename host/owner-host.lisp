; Experimental owner bridge: :program wrappers over the proved fn-own machine.
;
; tools/run_owner.py drives one owner per store through these entry points.
; Every wrapper is one proved owner transition: fn-own-step, fn-opc-prepare,
; or fn-own-read (the served port: one
; socket read is one fn-served-step over the connection's pinned archive,
; fn-own-read-is-served-step-on-pinned-prefix) or one fn-own-open, over the
; global `fn-owner`; the host never rebuilds owner, store, wire or session
; state itself.  The wire framing state lives inside the owner's connection
; record, so there is no per-connection host state at all.  Marshaling
; reuses host/store-host.lisp (decimal octets in, symbols and naturals out);
; the reply stream and the close verdict are the book's two projections of an
; effect list (fn-served-reply-octets, fn-served-closingp), installed in the
; globals `fn-owner-output` and `fn-owner-closep`.
; The served POST path: a read that injected an article leaves its
; submission queued inside the owner (fn-own-read); fn-owner-take is the
; writer step (fn-own-take-submission) and exposes the submission in flight
; (its connection, Message-ID, octets and groups, all produced by
; books/injection.lisp); the host carries it through the same store events
; tools/run_store.py `post' reports and feeds the word it observed to
; fn-owner-outcome (fn-own-outcome), which renders the 240 or 441 for that
; connection alone.  The submission flag is the third projection of an
; effect list, `fn-owner-submittedp' (fn-served-submission).  The host never
; writes a reply octet.
(in-package "ACL2")
; books/owner-fault includes books/owner and adds the host-fault transition
; `fn-own-fault'.  The host needs it: `fn-owner-fault' below is the only way
; tools/run_owner.py can abandon ONE connection, and before it existed an
; exception in the serve loop ended the process for every connection.
(include-book "../books/owner-config")
; P3 owner open and publication (fn-ock-).
(include-book "../books/owner-checkpoint-open")
; D25: the duplicate-versus-conflict decision keys on the poster's bytes.
(include-book "../books/poster-bytes")
(include-book "../books/config-owner-live")
(include-book "../books/config-owner-publish")
(include-book "../books/owner-tls-prefix")
(include-book "../books/owner-config-observe")
(include-book "../books/owner-served-carried")
(include-book "../books/owner-commit-carried")
(include-book "../books/owner-prepare-carried")
(include-book "../books/owner-advance-carried")
(include-book "../books/owner-intent-carried")
(include-book "../books/owner-commit-ocl")
(include-book "../books/owner-served-invariants")
(include-book "../books/owner-feed-port")
(include-book "../books/owner-prepare-correspondence")
; The transaction budget: `fn-owner-prepare' installs `fn-sbud-prepare'.
(include-book "../books/owner-store-budget")
(include-book "../books/checkpoint-auxiliary")
(include-book "../books/feed-wire-input")
(include-book "../books/feed-connection")
(include-book "../books/feed-connection-invariants")
; The injecting agent (the path-identity policy, fn-oag-post-config) and the
; service log lines (fn-olog-*): both ACL2's, read here and nowhere computed.
(include-book "../books/owner-agent")
(include-book "../books/owner-log")
; The served article bound installed with the profile (PKT-103).
(include-book "../books/owner-served-bound")
(include-book "../books/topic-history-local-proposals")
; The FNFD feed trailer.  `tools/run_owner.py' used to run its own
; `hashlib.sha256' over the protected prefix of every feed frame; the owner's
; ACL2 session does not load `host/store-host.lisp', so the one owner has to
; be a book both sessions include.  See books/frame-trailer.lisp.
(include-book "../books/feed-journal")
(include-book "../books/peer-pull")
(include-book "../books/consumer-owner-local")
(include-book "../books/hybrid-lifecycle")
(include-book "../books/peer-authored-accept")
(include-book "../books/key-statements")
(include-book "../books/login-binding")
; PRF-099: the opaque-carriage budget and the refusal classes.
(include-book "../books/peer-carriage")
;
; Loaded here, not left to a bridge's `ld' order: this file uses names
; host/store-node-host.lisp (and host/store-host.lisp under it) defines, so a session that loads this file alone
; must get them too.  A second `ld' of a file already in the session
; re-admits identical definitions, which ACL2 accepts as redundant.
(ld "store-node-host.lisp" :ld-error-action :error)

; The posting configuration: the groups served at the live configuration
; generation, the node's own <path-identity> from the ONE slot that holds it
; (the configuration policy `path-identity', which `fn-peer-local-identity'
; and `fn-store-prov-post' also read), and the store's payload bound.  ACL2
; derives all of it (books/owner-agent.lisp fn-oag-post-config, whose agent
; is the path-identity by fn-oag-post-config-agent-is-the-path-identity);
; this wrapper only supplies the payload bound: the record codec's payload
; field (`*fn-record-max-payload*', books/records-shape), which bounds every
; profile's (`fn-sbud-payload-bound-within-record-codec').  The wire limit is
; fixed before the profile is handed over; the POST boundary applies the
; profile's own bound (`fn-owner-post-boundary').
(defun fn-owner-post-config (cfg)
  (declare (xargs :mode :program))
  (fn-oag-post-config cfg *fn-record-max-payload*))

(defun fn-owner-ocfg (state)
  ; Internal, single-valued accessor for host wrappers.
  (declare (xargs :stobjs state :mode :program))
  (f-get-global 'fn-owner state))

(defun fn-owner-ocfg-state (state)
  ; External ACL2 bridge accessor.  `value' is intentionally only at this
  ; boundary; host functions use fn-owner-ocfg above as a single value.
  (declare (xargs :stobjs state :mode :program))
  (value (fn-owner-ocfg state)))

; `fn-owner' has one canonical value: the configured owner.  These are the
; only host accessors for its raw owner component.  A wrapper that changes
; connection membership must use fn-owner-step's fn-ocfg transition; a core
; operation which preserves membership may use fn-owner-replace-core.
(defun fn-owner-core (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-ocfg-owner (f-get-global 'fn-owner state)))

(defun fn-owner-clock-observation (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-clock (fn-owner-core state))))

(defun fn-owner-stamp-status (state)
  ; The native submission boundary asks ACL2 whether this owner's current
  ; observation can become a schema-1 stamp.  An accepted observation may
  ; still have no wall or exceed the record's uint32 seconds bound.
  (declare (xargs :stobjs state :mode :program))
  (value (if (natp (fn-record-stamp-of-observation
                    (fn-own-clock (fn-owner-core state))))
             :usable :clock-unusable)))

(defun fn-owner-config (state)
  ; The one live configuration.  No host global shadows this value: every
  ; caller reads the generation replayed into and published by fn-ocfg.
  (declare (xargs :stobjs state :mode :program))
  (fn-ocfg-config (fn-owner-ocfg state)))

(defun fn-owner-live-post-config (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-owner-post-config (fn-owner-config state))))

(defun fn-owner-install-ocfg (oc state)
  (declare (xargs :stobjs state :mode :program))
  (f-put-global 'fn-owner oc state))

(defun fn-owner-replace-core (owner state)
  (declare (xargs :stobjs state :mode :program))
  (let ((oc (f-get-global 'fn-owner state)))
    (fn-owner-install-ocfg (fn-ocfg-with-owner oc owner) state)))

(defun fn-owner-state (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-owner-core state)))

(defun fn-owner-install-effects (effects state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-owner-effects effects state))
         (state (f-put-global 'fn-owner-output (fn-served-reply-octets effects) state))
         (state (f-put-global 'fn-owner-closep (fn-served-closingp effects) state))
         ; RFC 4642 section 2.2.2: the host owes a TLS handshake.  The book
         ; decided it (fn-auth-starttls, books/nntp-auth.lisp); this reads
         ; its answer off the effect list, exactly as the close is read.
         (state (f-put-global 'fn-owner-starttlsp
                              (if (fn-served-starttlsp effects) t nil) state))
         (state (f-put-global 'fn-owner-submittedp
                              (if (fn-served-submission effects) t nil) state)))
    state))

;; The process root (P3 owner open, books/owner-checkpoint-open.lisp).  Both
;; paths extend a checkpoint over the records after it (`fn-sco-extend') and
;; install from the extended value with `fn-ock-recover-extended'
;; (fn-owner-recover-extended below).  From a verified checkpoint
;; (fn-owner-recover-from-checkpoint) the records are the suffix after S; on
;; a full replay (fn-owner-recover) the checkpoint is the capture of the
;; empty prefix and the records are the whole history.  The keystone
;; fn-owner-recover-from-checkpoint-equals-full-recover says both install the
;; owner of the full open, the composition
;; fn-orec-recover-installs-ocl-relation is stated over, and
;; fn-ock-recover-installs-ocl-relation carries its two premises of the
;; carried served keystones to what is installed here.  The extended value is
;; the capture of the whole history; the owner keeps it as the base of its
;; next publication (`fn-owner-sco-base').
(defun fn-owner-install-extended (oc extended state)
  (declare (xargs :stobjs state :mode :program))
  (if (equal oc :fault)
        (value :fault)
      (let* ((state (fn-owner-install-ocfg oc state))
             ; Rebuilt exclusively by successful FNFD scans after
             ; authoritative store recovery.  It is a carried
             ; incremental fold, never a whole-journal rescan on a
             ; served event.
             (state (f-put-global 'fn-owner-feed-intents nil state))
             ; The persisted profile is handed back by
             ; fn-owner-install-profile after every recovery; until
             ; then the budget is 0 and every publication is
             ; :unaffordable (books/store-budget.lisp).
             (state (f-put-global 'fn-owner-store-profile nil state))
             ; Socket-only reply framers are recreated after
             ; authoritative recovery; their durable counterpart is
             ; the FNFD replay above, not this retained input.
             (state (f-put-global 'fn-owner-feed-inputs
                                  (fn-fc-table-initial-state) state))
             ; The owner's checkpoint state: the capture it extends at its
             ; next publication, the newest durable checkpoint's S (set by
             ; fn-owner-sco-note-durable), and the count of the last attempt.
             (state (f-put-global 'fn-owner-sco-base extended state))
             (state (f-put-global 'fn-owner-sco-durable nil state))
             (state (f-put-global 'fn-owner-sco-attempted nil state)))
        (value :recovering))))

(defun fn-owner-recover-extended (extended config-records frontier max-conns state)
  (declare (xargs :stobjs state :mode :program))
  (fn-owner-install-extended
   (fn-ock-recover-extended extended config-records frontier max-conns)
   extended state))

; The owner from the Store open this process just ran
; (fn-store-sn-open-extended, host/store-node-host.lisp): its extended
; checkpoint E and (fn-sco-store-open E ...) = (REPLAYED OPENED), kept in the
; global `fn-store-sco-open'.  fn-ock-install over that pair is
; fn-ock-recover-extended of E (fn-ock-install-of-store-open-by-definition),
; so the keystone fn-owner-recover-from-checkpoint-equals-full-recover and
; fn-ock-recover-installs-ocl-relation hold of what is installed here, on
; both paths, with no second extension or finalization.
(defun fn-owner-recover-from-store-open (max-conns state)
  (declare (xargs :stobjs state :mode :program))
  (let ((opened (and (boundp-global 'fn-store-sco-open state)
                     (f-get-global 'fn-store-sco-open state))))
    (if (not (and (consp opened) (consp (cdr opened)) (consp (cddr opened))))
        (value :fault)
      (let ((state (f-put-global 'fn-store-sco-open nil state)))
        (fn-owner-install-extended
         (fn-ock-install (cadr opened) (caddr opened) max-conns)
         (car opened) state)))))

(defun fn-owner-recover (octet-records frontier config-octet-records max-conns state)
  (declare (xargs :stobjs state :mode :program))
  (let ((records (fn-store-decode-records octet-records))
        (config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (equal records :bad) (equal config-records :bad))
        (value :fault)
      (fn-owner-recover-extended
       (fn-sco-extend (fn-sco-capture config-records nil) config-records records)
       config-records frontier max-conns state))))

; The open from the checkpoint the Store open decoded and verified
; (`fn-store-sco-checkpoint', host/store-node-host.lisp) and the octets of
; the records after it.
(defun fn-owner-recover-from-checkpoint (suffix-octet-records frontier config-octet-records
                                                              max-conns state)
  (declare (xargs :stobjs state :mode :program))
  (let ((checkpoint (fn-store-sco-current state))
        (records (fn-store-decode-records suffix-octet-records))
        (config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (null checkpoint) (equal records :bad) (equal config-records :bad))
        (value :fault)
      (fn-owner-recover-extended
       (fn-sco-extend checkpoint config-records records)
       config-records frontier max-conns state))))

(defun fn-owner-store (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-own-store (fn-owner-core state)))

; The Store's persisted profile, carried from open.  VALUES is what
; `fn-bs-config-decode' returned for the store's metadata file (the host
; decoded nothing: host/native/io.lisp `fnn-metadata-config-decode' asked
; ACL2); anything that is not one of the named profiles is refused and the
; budget stays 0.  The profile is never changed while the owner runs:
; books/store-budget.lisp says why it is fixed at init.
; The served article bound is installed here too, on every run path
; (books/owner-served-bound.lisp fn-osb-install-serves-the-profile-bound): the
; developer `owner run' never reaches fn-owner-posting-configure, and served
; its connections with the codec ceiling recovery installed.
(defun fn-owner-install-profile (values state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (verdict next)
    (fn-osb-install (fn-owner-core state) values)
    (if (equal verdict :installed)
        (let* ((state (fn-owner-replace-core next state))
               (state (f-put-global 'fn-owner-store-profile values state))
               (state (f-put-global 'fn-owner-record-octets nil state))
               ; PRF-099: the carried-usage cache restarts from the Store
               ; this open replayed (fn-pcb-usage-extend walks it once).
               (state (f-put-global 'fn-owner-carried-usage nil state)))
          (value :installed))
      (value :refused))))

(defun fn-owner-store-profile (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-store-profile state)
      (f-get-global 'fn-owner-store-profile state)
    nil))

; The carried profile's article bound A and group bound G, for the control
; socket's read bound (host/native/control.lisp `fnn-control-start').  Both
; are 0 before a profile is installed, and the read bound is then the
; command-frame bound: no article is accepted without a profile anyway.
(defun fn-owner-control-profile-bounds (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((profile (fn-owner-store-profile state)))
    (value (list (nfix (fn-sbud-payload-bound profile))
                 (nfix (fn-sbud-group-bound profile))))))

(defun fn-owner-served-post-bound (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((bound (fn-sbud-payload-bound (fn-owner-store-profile state))))
    (if (posp bound) bound *fn-record-max-payload*)))


;; The owner's publication (books/owner-checkpoint-open.lisp).  These read
;; the owner and write only the four fn-owner-sco-* globals: the served
;; owner `fn-owner' is never written here.

(defun fn-owner-sco-global (name state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global name state) (f-get-global name state) nil))

(defun fn-owner-sco-count (state)
  (declare (xargs :stobjs state :mode :program))
  (len (fn-sf-records (fn-sn-files (fn-own-store (fn-owner-core state))))))

; The newest durable checkpoint the Store open verified: its S, or NIL.
(defun fn-owner-sco-note-durable (sequence state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner-sco-durable (and (natp sequence) sequence)
                             state)))
    (value :noted)))

; :due or :idle, by fn-ock-publication-duep under the profile's K.
(defun fn-owner-sco-due (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((profile (fn-owner-store-profile state)))
    (value (if (and profile
                    (fn-ock-publication-duep
                     (fn-owner-sco-global 'fn-owner-sco-durable state)
                     (fn-owner-sco-count state)
                     (fn-bs-profile-max-open-suffix profile)
                     (fn-owner-sco-global 'fn-owner-sco-attempted state)))
               :due :idle))))

; The publication in three steps (checkpoint-cost): the capture under the
; owner mutex, the encoding outside it, the result back under it.
;
; fn-owner-sco-capture (under the mutex): the values the publication reads,
; (BASE CONFIGS RECORDS SEGMENT COUNT SUFFIX), and the attempt is recorded at
; COUNT.  They are ACL2 values; a later commit makes new ones and changes none
; of these.
(defun fn-owner-sco-capture (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((st (fn-own-store (fn-owner-core state)))
         (records (fn-sf-records (fn-sn-files st)))
         (count (len records))
         (durable (fn-owner-sco-global 'fn-owner-sco-durable state))
         (state (f-put-global 'fn-owner-sco-attempted count state)))
    (value (list (fn-owner-sco-global 'fn-owner-sco-base state)
                 (fn-sn-config-history st)
                 records
                 (fn-bs-profile-max-record-octets (fn-owner-store-profile state))
                 count
                 (- count (if (natp durable) durable 0))))))

; Outside the mutex, the host calls `fn-ock-publication' (a state-free ACL2
; function, books/owner-checkpoint-open.lisp) on the captured values:
; (NEXT OCTETS), NEXT the capture of the captured history
; (fn-ock-publication-is-the-capture-at-the-capture-point) and OCTETS its
; frozen file.  It reads no global and writes none.

; fn-owner-sco-publication-done (under the mutex): NEXT becomes the base,
; whether or not the write succeeded (it is the capture of a prefix of the
; owner's history either way), and on a durable write its S is the newest
; durable checkpoint.  Answers S, or :none.
(defun fn-owner-sco-publication-done (next durablep state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-owner-sco-base next state))
         (state (if durablep
                    (f-put-global 'fn-owner-sco-durable (fn-sco-sequence next) state)
                  state)))
    (value (if durablep (fn-sco-sequence next) :none))))

; The served POST bound (D27): the carried Store profile's payload bound
; (`fn-sbud-payload-bound', books/store-budget-naming, which never exceeds the
; record codec's payload ceiling: `fn-sbud-payload-bound-within-record-codec'),
; so the wire reads at most what the operator's profile admits.  Before a
; profile is installed (recovery, where nothing is served and the budget is 0)
; it is the codec ceiling `*fn-record-max-payload*'.
;
; Native operator startup supplies the one posting-policy bit after recovery
; and after `fn-owner-install-profile'.  Preserve the agent and served groups
; ACL2 already installed and set the served bound from the profile; this
; changes the same fn-own-config value read by served POST and control.
(defun fn-owner-posting-configure (allow state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (cfg (fn-own-config owner))
         (next (fn-inj-make-config (and allow t)
                                   (fn-inj-config-agent cfg)
                                   (fn-inj-config-groups cfg)
                                   (fn-owner-served-post-bound state))))
    (if (not (fn-inj-configp next))
        (value :refused)
      (let ((state (fn-owner-replace-core (fn-own-configure owner next) state)))
        (value :configured)))))

; The committed record octets of the carried Store, from the carried
; (K . SUM) of the first K records extended by the records committed since
; (books/store-budget.lisp `fn-sbud-bytes-extend'; equal to
; `fn-sbud-bytes-used' when the cache is valid,
; `fn-sbud-bytes-used-is-kernel-sum').  Committed records only grow while one
; owner runs, and the cache is reset when a profile is installed at open, so
; each record is encoded once per owner process, not once per POST.
(defun fn-owner-record-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((records (fn-sf-records (fn-sn-files (fn-owner-store state))))
         (cache (if (boundp-global 'fn-owner-record-octets state)
                    (f-get-global 'fn-owner-record-octets state)
                  nil))
         (bytes (fn-sbud-bytes-extend cache records))
         (state (f-put-global 'fn-owner-record-octets
                              (cons (len records) bytes) state)))
    (mv bytes state)))

; The owner's verdict on one more record of KIND: the carried profile's count
; and history gates against the Store it carries.
(defun fn-owner-publication-verdict (kind state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (bytes state) (fn-owner-record-octets state)
    (let ((s (fn-owner-store state)))
      (value (fn-sbud-verdict-at (fn-owner-store-profile state) kind
                                 (fn-sbud-used s) bytes)))))

; (used budget bytes-used history-bound reserved-charge charge-capacity), all
; read from the carried state; the host prints it and computes none of it.
(defun fn-owner-headroom (state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (bytes state) (fn-owner-record-octets state)
    (value (fn-sbud-headroom-at (fn-owner-store-profile state)
                                (fn-owner-store state) bytes))))

; The carried profile as the operator reads it (field names and values).
(defun fn-owner-profile-report (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bs-profile-report (fn-owner-store-profile state))))

(defun fn-owner-node (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-sn-node (fn-owner-store state)))

(defun fn-owner-step (event state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn-owner-install-ocfg
                (fn-ocfg-step (fn-owner-ocfg state) event) state)))
    state))

; The live control path is deliberately small for this packet: a configured
; client asks to create or retire one group.  ACL2 constructs the delta
; (`fn-ocl-request-deltas', books/config-owner-publish.lisp), checks the
; pinned generation and staged/clock/reservation conditions, and produces the
; exact record that the host persists.  Python carries only the kind/name
; request and the resulting octets.

(defun fn-owner-reconfigure-deltas (id deltas state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((oc (fn-owner-ocfg state))
         (reason (fn-ocfg-reconfig-refusal oc id deltas))
         (state (fn-owner-step (list :reconfigure id deltas) state))
         (staged (fn-ocfg-staged (fn-owner-ocfg state))))
    (if staged
        (let* ((state (f-put-global 'fn-owner-config-octets
                                    (fn-cfg-encode staged) state))
               (state (f-put-global 'fn-owner-config-reason nil state)))
          (value :staged))
      (let ((state (f-put-global 'fn-owner-config-reason reason state)))
        (value :refused)))))

(defun fn-owner-reconfigure (id kind name-octets state)
  ; :staged leaves exactly one encoded configuration record in the output
  ; slot.  :refused leaves the named ACL2 refusal reason there.  No state is
  ; published until fn-owner-reconfigure-complete follows a durable write.
  (declare (xargs :stobjs state :mode :program))
  (let ((name (if (fn-store-text-octetsp name-octets)
                  (fn-store-octets->string name-octets) :bad)))
    (if (equal name :bad)
        (let ((state (f-put-global 'fn-owner-config-reason :group-name state)))
          (value :refused))
      (let ((deltas (fn-ocl-request-deltas kind name)))
        (if (null deltas)
            (let ((state (f-put-global 'fn-owner-config-reason :delta-kind state)))
              (value :refused))
          (fn-owner-reconfigure-deltas id deltas state))))))

(defun fn-owner-reconfigure-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-config-octets state)))

(defun fn-owner-reconfigure-reason (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-config-reason state)))

(defun fn-owner-reconfigure-complete (generation state)
  ; This is called only after Store.write_config_record has named the record
  ; durable. An uncertain write has no call here and forces recovery.  The
  ; whole completion is ACL2's `fn-ocl-publish' (books/config-owner-publish):
  ; the refusal, the Store domain/capacity and carried physical history in one
  ; owner transition, the posting configuration of the published generation,
  ; and the verdict.  On :refused and :recovery-required its owner is the one
  ; installed now, so the host installs it unconditionally and decides nothing.
  (declare (xargs :stobjs state :mode :program))
  (mv-let (verdict next)
    (fn-ocl-publish (fn-owner-ocfg state) generation
                    (fn-owner-served-post-bound state))
    (let ((state (fn-owner-install-ocfg next state)))
      (value verdict))))

(defun fn-owner-config-generation (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cfg-generation (fn-owner-config state))))

(defun fn-owner-config-served (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-cnode-served-of (fn-owner-config state)))))

; -----------------------------------------------------------------------------
; The transaction path: the same observations run_store.py reports, each one
; a (:store ...) owner event.

;; The call is fn-rcon-ocfg-io (books/records-concrete-owner.lisp), equal to
;; fn-ocfg-step of (:store (:io operation result)) for every configured owner
;; (fn-rcon-ocfg-io-is-ocfg-step, no hypothesis): its :record-directory arm
;; pairs the staged record's sequence and transaction id through the
;; concrete record dispatchers instead of fn-record-p's octet lists.
(defun fn-owner-io (operation result state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn-owner-install-ocfg
                (fn-rcon-ocfg-io (fn-owner-ocfg state) operation result) state)))
    (value (fn-sf-phase (fn-sn-files (fn-owner-store state))))))

(defun fn-owner-prepare (msgid-octets payload group-codes id-octets
                          subject-octets evidence-octets charge state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (> (len payload) *fn-record-max-payload*)
            (equal groups :bad) (null groups)
            (not (fn-store-text-octetsp id-octets))
            (not (fn-store-text-octetsp subject-octets))
            (not (fn-store-text-octetsp evidence-octets)) (not (posp charge)))
        (value :invalid)
      ; A name in the domain but not served at the live generation (a retired
      ; group) is refused by the predicate fn-cnode-prepare applies.
      (if (not (fn-cnode-selection-servedp (fn-owner-config state) groups))
          (value :refused)
      (let* ((msgid (fn-store-octets->string msgid-octets))
             (existing (fn-pb-existing-action msgid payload groups s)))
        (if existing
            (value existing)
          (let* ((record (fn-sn-article-record
                          s (fn-own-clock (fn-owner-core state))
                          msgid payload groups
                          (fn-store-octets->string id-octets)
                          (fn-store-octets->string subject-octets)
                          (fn-store-octets->string evidence-octets)
                          charge))
                 ; fn-opc-prepare is equal to the former fn-ocfg-step event
                 ; under fn-own-relation, established by observed recovery
                 ; and preserved by every live owner transition.
                 ; The budget gate is part of the prepare: at or over the
                 ; carried profile's budget fn-sbud-prepare is the identity
                 ; (fn-sbud-prepare-refuses-at-budget) and the word is
                 ; :unaffordable; below it, it is fn-opc-prepare.
                 ; The call is fn-pcar-sbud-prepare
                 ; (books/owner-prepare-carried.lisp), equal to
                 ; fn-sbud-prepare with no hypothesis
                 ; (fn-pcar-sbud-prepare-is-sbud-prepare): its candidate
                 ; test reads the last record's txid instead of folding
                 ; every record's through fn-record-p.
                 (budget (fn-sbud-budget (fn-owner-store-profile state) :article))
                 (before (fn-owner-ocfg state))
                 (state (if (equal record :clock-unusable)
                            state
                          (fn-owner-install-ocfg
                           (fn-pcar-sbud-prepare before record budget)
                           state))))
            (if (equal record :clock-unusable)
                (value :clock-unusable)
              (if (equal (fn-owner-store state) s)
                (value (fn-sbud-refusal-kind before budget))
              (value :prepared))))))))))

(defun fn-owner-refuse-reservation (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (fn-owner-store state))
         (files (fn-sn-files before))
         (state (fn-owner-step
                 (list :store (list :refuse-reservation (1- (fn-sf-frontier files))))
                 state))
         (next (fn-owner-store state)))
    (if (and (equal (fn-sf-phase files) :reserved)
             (not (equal next before))
             (equal (fn-sf-phase (fn-sn-files next)) :ready))
        (value :refused)
      (value :fault))))

; fn-owner-prepare with the payload in the octet buffer (books/octets-stobj.lisp;
; host/native/owner.lisp fnn-owner-attempt).  Three things differ from the
; list entry above, each by a theorem of books/poster-bytes-buffer.lisp:
; the fn-octet-listp test is discharged by the buffer's recognizer
; (fn-pbb-buffer-is-octet-listp); the length is the fill count
; (fn-octets-len); the existing-article test reads the buffer by index
; (fn-pbb-existing-action-is-pb-existing-action).  The record's payload is
; the buffer's list (fn-octets-list), consed once here: it is the store
; record's own field, held for the record's life, until wave C gives the
; owner state a concrete representation.  Everything after the record is
; the same prepare (fn-pcar-sbud-prepare) on the same record.
(defun fn-owner-prepare-buffer (msgid-octets group-codes id-octets
                                 subject-octets evidence-octets charge
                                 fn-octets state)
  (declare (xargs :stobjs (fn-octets state) :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (> (fn-octets-len fn-octets) *fn-record-max-payload*)
            (equal groups :bad) (null groups)
            (not (fn-store-text-octetsp id-octets))
            (not (fn-store-text-octetsp subject-octets))
            (not (fn-store-text-octetsp evidence-octets)) (not (posp charge)))
        (value :invalid)
      (if (not (fn-cnode-selection-servedp (fn-owner-config state) groups))
          (value :refused)
      (let* ((msgid (fn-store-octets->string msgid-octets))
             (existing (fn-pbb-existing-action msgid fn-octets groups s)))
        (if existing
            (value existing)
          (let* ((record (fn-sn-article-record
                          s (fn-own-clock (fn-owner-core state))
                          msgid (fn-octets-list fn-octets) groups
                          (fn-store-octets->string id-octets)
                          (fn-store-octets->string subject-octets)
                          (fn-store-octets->string evidence-octets)
                          charge))
                 (budget (fn-sbud-budget (fn-owner-store-profile state) :article))
                 (before (fn-owner-ocfg state))
                 (state (if (equal record :clock-unusable)
                            state
                          (fn-owner-install-ocfg
                           (fn-pcar-sbud-prepare before record budget)
                           state))))
            (if (equal record :clock-unusable)
                (value :clock-unusable)
              (if (equal (fn-owner-store state) s)
                (value (fn-sbud-refusal-kind before budget))
              (value :prepared))))))))))

(defun fn-owner-prepare-retention
  (kind id-octets subject-octets evidence-octets charge state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (node (fn-sn-node s)))
    (if (or (not (member-equal kind '(:undertake :release)))
            (not (fn-store-text-octetsp id-octets))
            (not (fn-store-text-octetsp subject-octets))
            (not (fn-store-text-octetsp evidence-octets))
            (not (natp charge)))
        (value :invalid)
      (let* ((txid (fn-state-next-txid (fn-node-acceptance node)))
             (event (fn-store-retention-event-make
                     kind (fn-sn-identity-next s) txid txid
                     (fn-store-octets->string id-octets)
                     (fn-store-octets->string subject-octets)
                     (fn-store-octets->string evidence-octets) charge))
             (state (fn-owner-step (list :store (list :prepare-retention event)) state)))
        (value (if (equal (fn-owner-store state) s) :refused :prepared))))))

; The caller supplies an ACL2-constructed kind-3 or kind-4 event.  This
; boundary deliberately accepts no separate profile, key, article, or verdict
; fields that host code could recombine differently.
(defun fn-owner-prepare-identity (event state)
  (declare (xargs :stobjs state :mode :program))
  (let ((s (fn-owner-store state)))
    (if (not (or (fn-stxk-p event) (fn-stxa-p event)))
        (value :invalid)
;; fn-ccar-ocfg-prepare-identity (books/owner-commit-carried.lisp) is
      ;; fn-ocfg-step of this event for every configured owner, no hypothesis
      ;; (fn-ccar-ocfg-prepare-identity-is-ocfg-step), guard-verified under
      ;; fn-sn-statep of the store, which fn-ocl-relation carries.
      (let ((state (fn-owner-install-ocfg
                    (fn-ccar-ocfg-prepare-identity (fn-owner-ocfg state) event)
                    state)))
        (value (if (equal (fn-owner-store state) s) :refused :prepared))))))

; The consumer proposal is constructed by ACL2.  The host carries this exact
; bounded event into Store; it does not rebuild the scope, epoch or cursor.
(defun fn-owner-prepare-consumer (event state)
  (declare (xargs :stobjs state :mode :program))
  (let ((s (fn-owner-store state)))
    (if (not (fn-cpe-eventp event))
        (value :invalid)
      (let ((state (fn-owner-step
                    (list :store (list :prepare-consumer event)) state)))
        (value (if (equal (fn-owner-store state) s) :refused :prepared))))))

; ACL2 constructs the exact topic event before this host boundary. Store's
; carried historical projection decides whether it may be staged.
(defun fn-owner-prepare-topic (event state)
  (declare (xargs :stobjs state :mode :program))
  (let ((s (fn-owner-store state)))
    (if (not (fn-th-topic-eventp event))
        (value :invalid)
      (let ((state (fn-owner-step
                    (list :store (list :prepare-topic event)) state)))
        (value (if (equal (fn-owner-store state) s) :refused :prepared))))))

; This is the one owner-side proposal read. ACL2 selects an exact earlier T10
; event and snapshot from the carried topic projection; neither the control
; peer nor host may supply an external verified/source verdict.
(defun fn-owner-topic-propose (operation source-sequence observed-uid
                                         entropy-id quota state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (projection (fn-sn-topic s))
         (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (value
     (fn-th-local-propose operation projection txid source-sequence
                          observed-uid entropy-id quota))))

; The local-control socket binds its one OS owner to fn-col's fixed principal.
; These ACL2 calls alone choose the operation, current cursor scope and Store
; coordinates.  No request may provide qver, view, principal or event bytes.
(defun fn-owner-consumer-local-bootstrap (history incarnation state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-bootstrap (fn-owner-core state) history incarnation)))

(defun fn-owner-consumer-local-register (consumer group state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-register (fn-owner-core state) consumer group)))

(defun fn-owner-consumer-local-ack (cursor-octets state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-ack (fn-owner-core state) cursor-octets)))

(defun fn-owner-consumer-local-position (consumer state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-position (fn-owner-core state) consumer)))

(defun fn-owner-consumer-local-status (consumer state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-status (fn-owner-core state) consumer)))

(defun fn-owner-consumer-local-poll (consumer state)
  (declare (xargs :stobjs state :mode :program))
  (let ((decision (fn-col-poll (fn-owner-core state) consumer)))
    (value
     (if (eq (car decision) :poll)
         (list :poll (cadr decision)
               (if (caddr decision)
                   (if (fn-stxa-p (caddr decision))
                       (fn-stxa-encode (caddr decision))
                     ; fn-rcon-record-encode-impl-is-record-encode-impl
                     ; (books/records-codec-concrete, no hypothesis).
                     (fn-rcon-record-encode-impl (caddr decision)))
                 nil))
       decision))))

(defun fn-owner-consumer-local-unregister (consumer state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-col-unregister (fn-owner-core state) consumer)))

(defun fn-owner-checkpoint-clone-phase (marker-octets state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cpa-clone-phase-of-octets
          (fn-owner-store state) marker-octets)))

(defun fn-owner-known-abort (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (fn-owner-store state))
         (files (fn-sn-files before))
         (state (fn-owner-step (list :store (list :known-abort)) state))
         (next (fn-owner-store state)))
    (if (and (member-equal (fn-sf-phase files)
                           '(:record-staged :record-data-durable))
             (not (equal next before))
             (equal (fn-sf-phase (fn-sn-files next)) :ready))
        (value :aborted)
      (value :fault))))

(defun fn-owner-pending-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((record (fn-sf-record-candidate
                 (fn-sn-files (fn-owner-store state)))))
    ; fn-rcon-store-event-encode-is-store-event-encode: the encoder's
    ; dispatch, with the concrete record recognizer (books/records-concrete).
    (value (if record (fn-rcon-store-event-encode record) nil))))

; The staged record's sequence, the one the host names its transaction file
; from (host/native/owner.lisp fnn-owner-publish-prepared); the host holds no
; count of its own.  It is the committed count
; (books/store-budget-naming.lisp `fn-sbud-pending-sequence-is-used').
(defun fn-owner-pending-sequence (state)
  (declare (xargs :stobjs state :mode :program))
  ; fn-rcon-sbud-pending-sequence-is-sbud-pending-sequence (books/records-concrete).
  (value (fn-rcon-sbud-pending-sequence (fn-owner-store state))))

; The POST admission boundary over the profile the owner was handed at open
; (`fn-owner-install-profile'); without one the payload bound is 0.
(defun fn-owner-post-boundary (msgid-octets payload-length group-count charge
                                            state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sbud-post-boundary (fn-owner-store-profile state) msgid-octets
                                payload-length group-count charge)))

; Completion is the owner's (:complete) event: fn-sn-finish consumed once,
; its pair appended to the ledger once (fn-own-completion-consumed-once).
;; The call is fn-ccar-ocfg-complete (books/owner-commit-carried.lisp), equal
;; to fn-ocfg-step of (:complete) for every configured owner, no hypothesis
;; (fn-ccar-ocfg-complete-is-ocfg-step-complete).  It is guard-verified under
;; fn-sn-statep of the store, which fn-ocl-relation carries
;; (fn-ccar-ocl-relation-carries-sn-statep); the unverified fn-ocfg-step
;; evaluated that guard over the whole store on every completion, and its
;; fn-sn-finish searched the whole history and re-recognized the record for
;; every field it read.  The signed POST's composite, keyring snapshots,
;; retention, consumer and topic events complete here.
(defun fn-owner-finish (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (fn-owner-core state))
         (before-files (fn-sn-files (fn-own-store before)))
         (state (fn-owner-install-ocfg
                 (fn-ccar-ocfg-complete (fn-owner-ocfg state)) state))
         (after (fn-owner-core state))
         (after-files (fn-sn-files (fn-own-store after))))
    (if (and (equal (fn-sf-phase before-files) :completing)
             (equal (fn-sf-phase after-files) :ready)
             (equal (len (fn-own-ledger after))
                    (1+ (len (fn-own-ledger before)))))
        (value :durable)
      (value :fault))))

; The article completion of the submission in flight (served POST, control
; post): the word is fn-own-finish's (books/owner-served-invariants.lisp),
; :durable only when fn-sn-finish consumed an enabled completion whose record
; carries this submission's Message-ID and the octets fn-owner-take staged for
; it (fn-own-sub-stored-octets under the live configuration: for transit, the
; Path-updated fn-peer-relayed-octets), and the owner installed is its
; (fn-own-complete o).  That is the subject of
; fn-own-240-follows-consumed-completion, so the host no longer decides the
; word by comparing phases.  With no config record staged, fn-ocfg-step's
; (:complete) is exactly fn-ocfg-with-owner of fn-own-complete
; (books/owner-config.lisp fn-ocfg-complete); a staged record means this is
; not an article completion at all, and the answer is :fault with nothing
; changed.  Retention, identity and config completions still use
; fn-owner-finish above: they have no article submission to name.
;; The call is fn-ccar-own-finish (books/owner-commit-carried.lisp), equal
;; to fn-own-finish for every owner and configuration
;; (fn-ccar-own-finish-is-own-finish) under the same guard, fn-sn-statep of
;; the store, which the owner relation carries from open.  It finds the
;; completion record at its sequence position instead of searching the
;; whole history through fn-record-p, ten times per commit.  Since
;; books/records-concrete.lisp the record recognizer it executes is
;; fn-rcon-record-p (fn-rcon-record-p-is-record-p: equal to fn-record-p on
;; every input), which reads the record's strings in place instead of
;; building their octet lists.
(defun fn-owner-finish-submission (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((oc (fn-owner-ocfg state)))
    (if (fn-ocfg-staged oc)
        (value :fault)
      (let* ((result (fn-ccar-own-finish (fn-ocfg-owner oc) (fn-ocfg-config oc)))
             (state (fn-owner-replace-core (cdr result) state)))
        (value (car result))))))

(defun fn-owner-begin (id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (fn-owner-core state))
         (state (fn-owner-step (list :begin id) state)))
    (value (if (equal (fn-owner-core state) before) :refused :begun))))

; The writer step: fn-own-take-submission moves the oldest queued submission
; into the durable path when nothing is in flight, no transaction is pending
; and the store is :ready.  The submission in flight is exposed to the host
; through four globals read off the injection decision; the host passes them
; back through fn-owner-prepare exactly as the CLI passes its own.
(defun fn-owner-take (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (fn-owner-core state))
         (state (fn-owner-step (list :take) state))
         (after (fn-owner-core state))
         (sub (fn-own-inflight after)))
    (if (or (equal after before) (null sub))
        (value :idle)
      (let* ((decision (fn-own-sub-decision sub))
             (transitp (fn-own-transit-subp sub))
             (state (f-put-global 'fn-owner-submit-id (fn-own-sub-id sub) state))
             (state (f-put-global 'fn-owner-submit-transitp transitp state))
             (state (f-put-global 'fn-owner-submit-peer
                                  (if transitp (fn-peer-submission-peer decision) nil)
                                  state))
             (state (f-put-global 'fn-owner-submit-msgid
                                  (if transitp
                                      (fn-peer-submission-msgid decision)
                                    (fn-inj-decision-msgid decision))
                                  state))
             ; A transit article is stored, served and fed on as
             ; fn-peer-relayed-octets makes it: its Path updated with this
             ; node's identity and its Xref removed (RFC 5537 3.6/3.7,
             ; books/path-update.lisp).  These are the octets the host
             ; digests and stores; fn-owner-transit-decide stages the same
             ; function of the same octets (fn-peer-injection-arguments'
             ; payload) and leaves it in fn-owner-transit-payload, which the
             ; native drain compares with this before the store attempt.
             ; fn-own-sub-stored-octets is the one definition of these
             ; octets; fn-owner-finish-submission compares the completed
             ; record with the same function of the same configuration.
             (state (f-put-global 'fn-owner-submit-octets
                                  (fn-own-sub-stored-octets
                                   (fn-owner-config state) sub)
                                  state))
             ; A transit submission's memberships are not in the submission:
             ; they are fn-peer-scope-groups of the article's Newsgroups and
             ; the peer record, computed by fn-owner-transit-decide below
             ; over the live node, never here and never in Python.
             (state (f-put-global 'fn-owner-submit-groups
                                  (if transitp nil (fn-inj-decision-groups decision))
                                  state))
             ; The submission's intent identity, digested once here and
             ; carried to the intent and the resolution below
             ; (books/owner-intent-carried.lisp).  This is the only writer of
             ; the global, so its value always satisfies fn-icar-carryp
             ; (fn-icar-carryp-of-carry-of; nil before the first take).
             (state (f-put-global 'fn-owner-submit-intent
                                  (fn-icar-carry-of sub) state)))
        (value (cond (transitp :taken-transit)
                     ((fn-own-control-submissionp sub) :taken-control)
                     (t :taken)))))))

; The hybrid-signed author path and the BP application path submit an
; already-authored article object whose octets a signature or a journal
; binds.  This is one owner event, not a call around the owner to the store
; bridge: ACL2 checks the boundary, preserves the supplied octets exactly and
; queues the same submission record fn-own-take-submission consumes for
; served POST.
(defun fn-owner-control-submit (msgid-octets group-octets payload state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (result (fn-own-control-submit-result owner msgid-octets
                                                group-octets payload))
         (state (fn-owner-step (list :control-submit msgid-octets
                                     group-octets payload)
                               state)))
    (value result)))

(defun fn-owner-bp-transit-submit
    (peer msgid-octets payload id subject state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (cfg (fn-owner-config state))
         (result (fn-own-bp-transit-submit-result
                  owner cfg peer msgid-octets payload id subject))
         (state (fn-owner-step
                 (list :bp-transit-submit cfg peer msgid-octets payload
                       id subject) state)))
    (value result)))

(defun fn-owner-bp-transit-raw (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((sub (fn-own-inflight (fn-owner-core state))))
    (value (and (fn-own-bp-transit-submissionp sub)
                (fn-peer-submission-octets (fn-own-sub-decision sub))))))

; `fn operator CONFIG post': the operator is a posting agent and this node
; its injecting agent (RFC 5537 section 3.5).  books/owner.lisp
; fn-own-operator-submit injects the payload under the owner's posting
; configuration and the owner's current clock reading, refuses without one
; (D10-a), and resubmits the stored article when the same octets were
; already injected (fn-own-operator-retry-resubmits-the-stored-injection).
; The injected octets are what fn-owner-take then leaves in
; fn-owner-submit-octets; the host stores those, never the payload it read.
(defun fn-owner-operator-submit (msgid-octets group-octets payload state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (result (fn-own-operator-submit-result owner msgid-octets
                                                 group-octets payload))
         ; The refusal's service-log line, NIL unless RESULT is :refused
         ; (fn-olog-control-refusal-line-says-refused-iff-submit-refused).
         (state (f-put-global 'fn-owner-log-line
                              (fn-olog-control-refusal-line
                               owner msgid-octets group-octets payload)
                              state))
         (state (fn-owner-step (list :operator-submit msgid-octets
                                     group-octets payload)
                               state)))
    (value result)))

; Why the owner refused the operator's article: the injection decision's
; reason under the owner's current configuration and clock (the decision
; `fn-owner-operator-submit' just refused), NIL when that decision injects.
; The native control path maps it to the control word
; (`fn-native-control-refusal-status'), so an article past the profile's A
; reaches the operator as `article-exceeds-profile-bound', not a bare refusal.
(defun fn-owner-operator-refusal-reason (msgid-octets group-octets payload state)
  (declare (xargs :stobjs state :mode :program))
  (let ((decision (fn-own-operator-decision-of (fn-owner-core state)
                                               msgid-octets group-octets
                                               payload)))
    (value (if (fn-inj-injectedp decision)
               nil
             (fn-inj-decision-reason decision)))))

; -----------------------------------------------------------------------------
; The AUTHINFO policy (RFC 4643), set once at start-up and pinned per
; connection.
;
; It is defined HERE, above the transit port, because `fn-owner-open-peer'
; now reads it: a peer connection carries the operator's policy exactly as a
; reader connection does.
;
; The host reads the operator's credential file and passes the FIELDS; ACL2
; builds the record, the verifier and the configuration.  Nothing here
; derives a digest, compares a secret or decides a permission: the rows are
; transport (AGENTS.md's one-owner rule).  A row is
; (name-octets principal-octets salt-octets digest-octets postingp).

(defun fn-owner-auth-cred-of (row)
  (declare (xargs :mode :program))
  (fn-auth-make-cred (nth 0 row) (nth 1 row)
                     (fn-authsec-verifier (nth 2 row) (nth 3 row))
                     (and (nth 4 row) t)))

(defun fn-owner-auth-creds-of (rows)
  (declare (xargs :mode :program))
  (if (consp rows)
      (cons (fn-owner-auth-cred-of (car rows))
            (fn-owner-auth-creds-of (cdr rows)))
    nil))

(defun fn-owner-set-auth (requiredp protected-onlyp tls-availablep rows state)
  (declare (xargs :stobjs state :mode :program))
  (let ((acfg (fn-auth-make-config (and requiredp t) (and protected-onlyp t)
                                   (and tls-availablep t)
                                   (fn-owner-auth-creds-of rows))))
    (if (not (fn-auth-configp acfg))
        (value :rejected)
      (let ((state (f-put-global 'fn-owner-auth acfg state)))
        (value :ok)))))

(defun fn-owner-auth (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-auth state)
      (f-get-global 'fn-owner-auth state)
    (fn-auth-open-config)))

; Install a complete ACL2-built authentication configuration.  The native
; auth profile parser calls this after owner recovery and before the listener
; opens.  Raw Lisp cannot rebuild a credential row or change one policy bit.
(defun fn-owner-set-auth-config (acfg state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-auth-configp acfg))
      (value :rejected)
    (let ((state (f-put-global 'fn-owner-auth acfg state)))
      (value :ok))))

; -----------------------------------------------------------------------------
; The transit port (specs/peering.md 2.2).
;
; Accept: the host resolves the connecting address to a configured peer name
; with fn-owner-peer-for-address (the record's auth slot decides, not the
; client) and opens the connection with fn-own-open-peer, which pins the
; node, the live configuration AND the operator's AUTHINFO policy into the
; session.  A reader opens with fn-owner-open as before, on the same
; listener, under the same policy: `fn-served-peer-and-reader-open-under-
; the-same-policy' (books/served.lisp) is the statement of that.

(defun fn-owner-peer-name-for (rows address)
  ; The first configured peer whose auth slot is this source address.
  (declare (xargs :mode :program))
  (if (consp rows)
      (if (and (equal (fn-cfg-row-b (car rows)) "auth-source-address")
               (equal (fn-cfg-row-c (car rows)) address))
          (fn-cfg-row-a (car rows))
        (fn-owner-peer-name-for (cdr rows) address))
    nil))

(defun fn-owner-peer-for-address (address-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((address (fn-store-octets->string address-octets)))
    (if (equal address :bad)
        (value nil)
      (let ((name (fn-owner-peer-name-for
                   (fn-cfg-peers (fn-cfg-value (fn-owner-config state)))
                   address)))
        (value (if name (fn-record-string-octets name) nil))))))

; The native socket boundary supplies a family tag and the kernel's fixed-width
; address octets.  ACL2 owns their textual projection because the configured
; source-address is a semantic peer-identity decision, not a raw-host string
; formatting choice.  Numeric IPv4 is rendered canonically here; the current
; IPv6 profile admits only ::1, so every other IPv6 shape remains an explicit
; non-match until its textual policy is added in ACL2.
(defun fn-owner-ipv4-address-octets (address)
  (declare (xargs :mode :program))
  (if (consp address)
      (if (and (natp (car address)) (<= (car address) 255))
          (append (fn-nntp-decimal (car address))
                  (if (consp (cdr address)) '(46) nil)
                  (fn-owner-ipv4-address-octets (cdr address)))
        nil)
    nil))

(defun fn-owner-peer-for-socket-address (family address state)
  (declare (xargs :stobjs state :mode :program))
  (cond ((and (equal family :inet)
              (true-listp address) (equal (len address) 4)
              (fn-cbor-octet-listp address))
         (fn-owner-peer-for-address (fn-owner-ipv4-address-octets address) state))
        ((and (equal family :inet6)
              (equal address '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)))
         (fn-owner-peer-for-address (fn-record-string-octets "::1") state))
        (t (value nil))))

(defun fn-owner-open-peer (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (let* ((before (fn-owner-core state))
             (id (fn-own-next-id before))
             ; The owner's AUTHINFO policy, the same value fn-owner-open
             ; pins into a reader.  A peer connection was opened with no
             ; policy at all, and the owner resolves a connection to a peer
             ; by source address alone (fn-owner-peer-name-for below), so on
             ; a box where a configured peer is on loopback that was every
             ; client: the operator's credential reached nothing.
             (opened (fn-ocfg-open-peer (fn-owner-ocfg state) peer
                                        (fn-owner-auth state)))
             (state (fn-owner-install-ocfg (cdr opened) state))
             (state (fn-owner-install-effects (car opened) state))
             (state (f-put-global 'fn-owner-log-line
                                  (fn-olog-connection-line
                                   (fn-owner-core state) id peer-octets)
                                  state)))
        (if (fn-own-find-conn id (fn-own-conns (fn-owner-core state)))
            (value id)
          (value nil))))))

; The transfer decision for the transit submission in flight, over the LIVE
; node and the live configuration (RFC 4644 2.4.2: the offer was advisory).
; Every check of specs/peering.md 2.2 is in fn-peer-decide-transfer; this
; wrapper only reads its answer and the memberships fn-peer-injection-arguments
; derives, and leaves them where the bridge can read them.  The obligation id
; and the subject are the host's digests, as for POST (fn-frame-digest is
; constrained and unattached).
(defun fn-owner-transit-decide (id-octets subject-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (sub (fn-own-inflight owner)))
    (if (not (fn-own-transit-subp sub))
        (value :not-transit)
      (let* ((decision (fn-own-sub-decision sub))
             (node (fn-sn-node (fn-own-store owner)))
             (cfg (fn-owner-config state))
             (peer (fn-peer-submission-peer decision))
             (msgid (fn-peer-submission-msgid decision))
             (octets (fn-peer-submission-octets decision))
             (id (fn-store-octets->string id-octets))
             (subject (fn-store-octets->string subject-octets)))
        (if (or (equal id :bad) (equal subject :bad))
            (value :not-transit)
          (let* ((d (fn-peer-decide-transfer node cfg peer msgid octets
                                             (fn-own-clock owner) id subject))
                 (args (fn-peer-injection-arguments node cfg peer msgid octets
                                                    0 id subject
                                                    (fn-own-clock owner)))
                 (state (f-put-global 'fn-owner-transit-kind
                                      (fn-peer-decision-kind d) state))
                 (state (f-put-global 'fn-owner-transit-reason
                                      (fn-peer-decision-reason d) state))
                 ; (nth 3 args) is fn-peer-scope-groups' answer: the list
                 ; fn-peer-injection-arguments hands fn-node-prepare as the
                 ; memberships (generation, msgid, octets, GROUPS, id,
                 ; subject, evidence, charge).  The generation passed here is
                 ; 0 because no element read from this list depends on it.
                 ;
                 ; It answers with STRINGS ("Strings, as fn-node-prepare
                 ; takes", books/peer-inbound.lisp fn-peer-scope-groups, which
                 ; ends in `fn-record-octets-string') where the POST path's
                 ; `fn-inj-decision-groups' answers with OCTETS -- its
                 ; elements are `fn-cbor-octet-listp' by
                 ; `fn-inj-group-namesp' -- and the host reads ONE global for
                 ; both.  Reading a string as an octet list raised
                 ; `unexpected ACL2 octet-list result' inside `Owner.drain',
                 ; which did not catch, so the OWNER PROCESS DIED on the
                 ; first article a peer transferred: the second half of the
                 ; w10/v0-matrix board ASK, and the death that took 22
                 ; transit rows, the feed rows and the crash rows of the
                 ; matrix with it.  The conversion is ACL2's own and happens
                 ; here, where the global is written, so the two paths agree
                 ; on a representation without Python choosing one.
                 ;
                 ; `w11/twonode-feed' and `w11/owner-survival' diagnosed and
                 ; fixed this independently on the same evening, and the two
                 ; fixes differed only in which of two identical helpers they
                 ; called.  The duplicate is folded into ACL2:
                 ; `fn-oag-group-octets' (books/owner-agent.lisp) is the one.
                 (state (f-put-global 'fn-owner-submit-groups
                                      (if (equal (fn-peer-decision-kind d) :want)
                                          (fn-oag-group-octets (nth 3 args))
                                        nil)
                                      state))
                 (state (f-put-global 'fn-owner-transit-evidence
                                      (fn-record-string-octets
                                       (fn-peer-evidence peer cfg))
                                      state))
                 ; D23: the delivering boundary's carried-source list, the
                 ; one fn-owner-peer-carrier-plan hands fn-pa-current-plan
                 ; for this transit attempt (books/peer-authored-accept).
                 (state (f-put-global 'fn-owner-transit-carried
                                      (fn-pa-peer-carried-sources
                                       peer (fn-cfg-peers (fn-cfg-value cfg)))
                                      state))
                 ; PRF-099: the same boundary's opaque-carriage budget
                 ; (books/peer-carriage-rows.lisp fn-pcb-peer-budget), read
                 ; from the same configuration as its carried list.
                 (state (f-put-global 'fn-owner-transit-budget
                                      (fn-pcb-peer-budget
                                       peer (fn-cfg-peers (fn-cfg-value cfg)))
                                      state))
                 ; (nth 2 args) is the payload fn-node-prepare is given:
                 ; fn-peer-relayed-octets of the received octets
                 ; (fn-peer-injection-arguments-stages-the-relayed-octets).
                 ; fn-owner-take left the same function of the same octets in
                 ; fn-owner-submit-octets; the native drain compares the two.
                 (state (f-put-global 'fn-owner-transit-payload
                                      (if (equal (fn-peer-decision-kind d) :want)
                                          (nth 2 args)
                                        nil)
                                      state)))
            (value (fn-peer-decision-kind d))))))))

; The transit reply.  `kind' and `reason' are the decision this image just
; made; `word' is the store's observed outcome (:durable, :refused,
; :uncertain), ignored unless the decision was :want.
; The frames the host has to make durable, and the bytes they authorize.
; `fn-owner-feed-frames' is a list of encoded FNFD frames, each sealed with
; the constrained trailer (A-CRYPTO); the host writes them length-prefixed.
; `fn-feed-encode' takes the trailer as an argument, so these frames carry a
; ZERO trailer: tools/run_owner.py hashes the protected prefix and appends the
; real one (A-CRYPTO).  The header, the
; field encoding and every bound stay ACL2's; the host slices at a constant it
; did not choose.
(defconst *fn-owner-feed-zero-trailer*
  '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))

(defun fn-owner-feed-encode-records (records)
  (declare (xargs :mode :program))
  (if (consp records)
      (cons (fn-feed-encode (fn-feed-journal-kind (car records))
                            (fn-feed-journal-values (car records))
                            *fn-owner-feed-zero-trailer*)
            (fn-owner-feed-encode-records (cdr records)))
    nil))

; This is the outbound wire boundary.  The feed machine supplies its complete
; command/source octets; `fn-wire-render-feed-command' owns all interpretation
; of their CRLF structure, dot quoting and terminator.  The host receives only
; this already-rendered socket byte vector (or the separate refusal word).
(defun fn-owner-feed-render-command (command)
  (declare (xargs :mode :program))
  (fn-wire-render-feed-command command *fn-nntp-max-initial-line-octets*
                               *fn-record-max-payload*))

(defun fn-owner-feed-install-feed (records effects state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((command (fn-own-feed-effect-octets effects))
         (rendered (fn-owner-feed-render-command command))
         (state (f-put-global 'fn-owner-feed-records records state))
         (state (f-put-global 'fn-owner-feed-frames
                              (fn-owner-feed-encode-records records) state))
         (state (f-put-global 'fn-owner-feed-command
                              (fn-wire-outbound-octets rendered) state))
         (state (f-put-global 'fn-owner-feed-command-status
                              (if (fn-wire-outbound-okp rendered) :ok
                                (fn-wire-outbound-reason rendered)) state))
         (state (f-put-global 'fn-owner-feed-peer
                              (fn-own-feed-effect-peer effects) state)))
    state))

; The only host projection of a bounded feed step.  The ACL2 subject has
; already selected the next table, journal records and effects together.  A
; refusal is published as empty output and deliberately does not replace the
; owner's core, so queued delivery intent remains available for recovery.
(defun fn-owner-feed-install-port-result (owner result state)
  (declare (xargs :stobjs state :mode :program))
  (if (equal (fn-own-feed-port-status result) :accepted)
      (let* ((state (fn-owner-replace-core
                     (fn-own-with-feeds owner
                                        (fn-own-feed-port-table result)) state))
             (state (fn-owner-feed-install-feed
                     (fn-own-feed-port-records result)
                     (fn-own-feed-port-effects result) state)))
        (mv :accepted state))
    (let ((state (fn-owner-feed-install-feed nil nil state)))
      (mv :refused state))))

; Project the durable intent before the store is allowed to begin.  The host
; supplies values ACL2 itself produced (provenance, configuration generation
; and next transaction id); this function derives the exact object identity,
; acceptance-time targets and queue-capacity verdict from the in-flight owner
; submission.  No owner state moves until the frames have reached their
; per-peer journals.
;; The call is fn-icar-submission-intent (books/owner-intent-carried.lisp),
;; which returns (result . records) and equals
;; (cons fn-own-submission-intent-result fn-own-submission-intent-records)
;; under fn-icar-carryp of the carry fn-owner-take installed
;; (fn-icar-submission-intent-is-reference): the identity is the one digested
;; at take, not three new digests of the payload.
(defun fn-owner-intent-carry (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-submit-intent state)
      (f-get-global 'fn-owner-submit-intent state)
    nil))

(defun fn-owner-submission-intent (evidence generation txid state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (intent (fn-icar-submission-intent owner (fn-owner-intent-carry state)
                                            evidence generation txid))
         (result (car intent))
         (records (cdr intent))
         (state (f-put-global 'fn-owner-shared-resolution-id nil state))
         (state (fn-owner-feed-install-feed records nil state)))
    (value result)))

; Project commit/abort while the same submission is still in flight.  The
; caller durably appends these records before invoking fn-owner-outcome (or
; its control/transit counterpart), so the in-memory feed can never get ahead
; of the obligation journal.  Uncertain produces no resolution record.
;; The call is fn-icar-submission-resolution-records, equal to
;; fn-own-submission-resolution-records under the same carry
;; (fn-icar-submission-resolution-records-is-reference).
(defun fn-owner-submission-resolution (word evidence generation txid state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (records (fn-icar-submission-resolution-records
                   owner (fn-owner-intent-carry state)
                   word evidence generation txid))
         (sub (fn-own-inflight owner))
         (state (f-put-global 'fn-owner-shared-resolution-id
                              (and sub (fn-own-sub-id sub)) state))
         (state (fn-owner-feed-install-feed records nil state)))
    (value (cond ((consp records)
                  (fn-feed-journal-kind (car records)))
                 ((equal (fn-own-outcome-completion owner word) :uncertain)
                  :uncertain)
                 (t :none)))))

; Startup calls this only after the store's authoritative recovery completed.
; The scanner accumulated exact unresolved intent values in the global.  One
; call projects one commit/abort frame; replaying that frame removes the exact
; key.  A partial binding is :uncertain and must fence startup.
(defun fn-owner-feed-reconcile-next (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((values (car (f-get-global 'fn-owner-feed-intents state))))
    (if (null values)
        (value :done)
      (let* ((owner (fn-owner-core state))
             (record (fn-own-feed-intent-reconcile-record
                      (fn-sn-node (fn-own-store owner)) values)))
        (if (null record)
            (value :uncertain)
          (let ((state (fn-owner-feed-install-feed (list record) nil state)))
            (value (fn-feed-journal-kind record))))))))

(defun fn-owner-feed-reconcile-apply (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((record (car (f-get-global 'fn-owner-feed-records state))))
    (if (or (null record)
            (not (member-equal (fn-feed-journal-kind record)
                               '(:feed-commit :feed-abort))))
        (value :invalid)
      (let* ((peer (fn-record-octets-string
                    (fn-feed-record-peer (fn-feed-journal-values record))))
             (state (fn-owner-step (list :feed-replay peer (list record)) state))
             (state (f-put-global
                     'fn-owner-feed-intents
                     (fn-own-feed-intent-apply
                      (f-get-global 'fn-owner-feed-intents state)
                      (fn-feed-journal-kind record)
                      (fn-feed-journal-values record))
                     state)))
        (value :ok)))))

(defun fn-owner-feed-journal-peer-validp (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (value (if (fn-feed-namep peer-octets) t nil)))

(defun fn-owner-feed-journal-begin (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner-feed-safe-offset 0 state)))
    (value :ok)))

(defun fn-owner-feed-journal-prefix-size (state)
  (declare (xargs :stobjs state :mode :program))
  (value *fn-feed-journal-prefix-size*))

(defun fn-owner-feed-journal-offset (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-feed-safe-offset state)))

; A transit transfer that became durable owes the feed journal the same
; `(:feed-enqueue ...)` records a POST does: a relayed article is fed
; onward (RFC 5537 sec. 3.6) and the entry must survive the process that
; accepted it.  Read before the outcome moves the owner, as for POST.
(defun fn-owner-transit-outcome (id kind reason word state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (records (fn-own-transit-outcome-records owner id kind word))
         (result (fn-own-transit-outcome owner id kind reason word))
         (state (fn-owner-replace-core (cdr result) state))
         (state (fn-owner-install-effects (car result) state))
         (state (fn-owner-feed-install-feed records nil state)))
    (value :fed)))

; The service-log line for the transit outcome about to be fed, read off the
; owner BEFORE fn-owner-transit-outcome moves it (books/owner-log.lisp
; fn-olog-transit-line), with the same id, kind, reason and word.  DETAIL is
; the ingress refusal the host relays (host/native/owner.lisp
; fnn-owner-transit-refused), a log field only.
(defun fn-owner-transit-log-line (id kind reason word detail state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner-log-line
                             (fn-olog-transit-line (fn-owner-core state)
                                                   id kind reason word detail)
                             state)))
    (value :ok)))

(defun fn-owner-transit-kind (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-transit-kind state)))

(defun fn-owner-transit-reason (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-transit-reason state)))

(defun fn-owner-transit-evidence (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-transit-evidence state)))

; The word the host observed for the submission in flight (:durable,
; :refused, :uncertain or anything else) is fed back as one owner event;
; fn-own-outcome renders the reply (240 only when a completion was consumed
; after the take, fn-own-durable-reply-names-a-durable-record) for that
; connection and installs it in fn-owner-output.
; The FNFD records a durable acceptance owes the feed journal are read off
; the owner BEFORE the outcome moves it and installed where the bridge
; reads them, exactly as a tick and a reply do.  Without this the
; `(:feed-enqueue peer msgid tick)' of specs/peering.md sec. 3.3 was never
; written in any deployment, and an article accepted while a peer was
; unreachable did not survive the process that accepted it.
(defun fn-owner-outcome (id word state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         ; The service log line, read before the event consumes the
         ; submission in flight (books/owner-log.lisp).
         (state (f-put-global 'fn-owner-log-line
                              (fn-olog-served-post-line owner id word) state))
         (records (fn-own-outcome-journal-records
                   owner id word
                   (f-get-global 'fn-owner-shared-resolution-id state)))
         ; fn-acar-own-outcome (books/owner-advance-carried.lisp) is
         ; fn-own-outcome under fn-ocl-relation
         ; (fn-acar-own-outcome-is-reference-under-ocl-relation), which the
         ; commit before it keeps (fn-ocmt-post-commit-preserves-ocl-relation):
         ; the re-pin tests the rebuilt session at the node the held session
         ; already carries instead of re-running fn-node-statep on it, and
         ; opens the reader session with fn-acar-nntp-projectionp, which
         ; omits the fn-statep of the whole view archive that
         ; fn-ocl-view-historyp carries (fn-acar-view-historyp-carries-view-statep).
         (result (fn-acar-own-outcome owner id word))
         (state (fn-owner-replace-core (cdr result) state))
         (state (fn-owner-install-effects (car result) state))
         (state (f-put-global 'fn-owner-shared-resolution-id nil state))
         (state (fn-owner-feed-install-feed records nil state)))
    (value :fed)))

; The control result is projected before the event consumes the in-flight
; submission.  The state transition uses fn-own-outcome-completion and
; fn-own-feed-durable exactly as the served outcome; only wire rendering and
; connection re-pinning are absent because the control request has no NNTP
; connection.
(defun fn-owner-control-outcome (word state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (result (fn-own-control-outcome-result owner word))
         (state (f-put-global 'fn-owner-log-line
                              (fn-olog-control-post-line owner word) state))
         (state (fn-owner-step (list :control-outcome word) state)))
    (value result)))

(defun fn-owner-bp-transit-outcome (word state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (result (fn-own-bp-transit-outcome-result owner word))
         (state (fn-owner-step (list :bp-transit-outcome word) state)))
    (value result)))

; The allocation domain the owner's live node carries (every name ever
; created): the store bridge's fn-store-cfg-domain reads the global
; fn-store-sn, which the owner never sets (its store lives in fn-owner), so
; the owner answers the same question from its own node.
(defun fn-owner-domain (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-state-groups (fn-node-acceptance (fn-owner-node state))))))

(defun fn-owner-group-codes (name-octets state)
  ; Resolve submitted names against the owner's current allocation domain.
  ; The separate Store bridge's replayed global does not follow live owner
  ; reconfiguration.  This is the same ACL2 resolver as fn-store-group-codes.
  (declare (xargs :stobjs state :mode :program))
  (let ((names (fn-store-octet-lists->strings name-octets)))
    (value (if (equal names :bad) :bad
             (fn-store-codes-from-groups
              names (fn-state-groups
                     (fn-node-acceptance (fn-owner-node state))))))))

(defun fn-owner-next-txid (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-state-next-txid (fn-node-acceptance (fn-owner-node state)))))

(defun fn-owner-next-store-coordinates (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (value (list (fn-sn-identity-next s) txid txid))))

(defun fn-owner-keyring-snapshot (generation state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-stxk-find generation
                       (fn-sn-keyring-snapshots (fn-owner-store state)))))

(defun fn-owner-hybrid-snapshots (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sn-keyring-snapshots (fn-owner-store state))))

(defun fn-owner-hybrid-current-enrollment (generation state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-hl-current-enrollment
          generation (fn-sn-keyring-snapshots (fn-owner-store state)))))

; TRANSITP is the host's path: t only for the NNTP transit attempt, whose
; delivering boundary fn-owner-transit-decide just read; served POST, bound
; submissions and BP transit pass nil, the D02 decision unchanged
; (fn-pa-current-plan-without-carried-list-never-carries).
(defun fn-owner-transit-carried-list (transitp state)
  (declare (xargs :stobjs state :mode :program))
  (if (and transitp (boundp-global 'fn-owner-transit-carried state))
      (f-get-global 'fn-owner-transit-carried state)
    nil))

;; The login-binding table the native auth profile loaded
;; (books/native-auth-profile.lisp fn-native-auth-load-bindings), installed
;; beside the auth configuration before the listener opens.  Transport only:
;; ACL2 built it, and fn-lb-owner-gate is the only reader.
(defun fn-owner-set-login-bindings (bindings state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner-login-bindings bindings state)))
    (value :ok)))

(defun fn-owner-login-bindings (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-owner-login-bindings state)
      (f-get-global 'fn-owner-login-bindings state)
    nil))

;; The posting policy's gate for the served submission in flight
;; (books/login-binding.lisp fn-lb-owner-gate over the owner, its LIVE
;; configuration and the binding table), called by host/native/owner.lisp
;; fnn-owner-attempt-served before the transit attempt.  The verdict's
;; service-log line is left in fn-owner-login-log-line (nil: no login).
(defun fn-owner-login-gate (received state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((verdict (fn-lb-owner-gate (fn-owner-core state)
                                    (fn-ocfg-config (fn-owner-ocfg state))
                                    (fn-owner-login-bindings state)
                                    received))
         (state (f-put-global 'fn-owner-login-log-line
                              (fn-lb-verdict-line verdict) state)))
    (value verdict)))

(defun fn-owner-peer-carrier-plan (received transitp state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-pa-current-plan
          received (fn-sn-keyring-snapshots (fn-owner-store state))
          (fn-owner-transit-carried-list transitp state)
          (and transitp t))))

;; C1 (control messages): the filing step every ingress takes first,
;; books/peer-authored-accept.lisp fn-pa-filing-plan over the received
;; octets, the ingress's group names and the owner's allocation domain (the
;; table fn-owner-group-codes resolves against).  (:file GROUPS) or
;; (:refused REASON); the host uses GROUPS in place of its own.
(defun fn-owner-control-filing (received group-octets state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-pa-filing-plan
          received group-octets
          (fn-state-groups (fn-node-acceptance (fn-owner-node state))))))

(defun fn-owner-peer-carrier-form (received state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-pa-carrier-form received)))

(defun fn-owner-served-carried-word (word detail state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-pa-served-word word detail)))

; PRF-099: the carried usage of the boundary whose release evidence is
; EVIDENCE (a string), from the owner's (K . TALLY) cache over the committed
; records extended by the records committed since
; (books/peer-carriage.lisp fn-pcb-usage-extend; equal to the replay
; projection fn-pcb-usage when the cache is valid,
; fn-pcb-carried-usage-is-the-projection, and kept valid,
; fn-pcb-extended-cache-is-valid).  Reset at open (fn-owner-install-profile).
(defun fn-owner-carried-usage (evidence state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((records (fn-sf-records (fn-sn-files (fn-owner-store state))))
         (cache (if (boundp-global 'fn-owner-carried-usage state)
                    (f-get-global 'fn-owner-carried-usage state)
                  nil))
         (tally (fn-pcb-usage-extend cache records))
         (state (f-put-global 'fn-owner-carried-usage
                              (cons (len records) tally) state)))
    (mv (fn-pcb-tally-get evidence tally) state)))

; D23 and PRF-099: the carried arm's kind-4 event, for the NNTP transit
; attempt only, gated by the delivering boundary's opaque-carriage budget
; over its carried usage (books/peer-carriage.lisp fn-pcb-carried-event):
; the event, (:refused REASON) naming the exhausted bound, or nil.  No
; primitive observation is taken or claimed.
(defun fn-owner-peer-carried-relay-event
    (coordinates msgid received group-codes obligation subject evidence charge
                 state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes
                  (fn-state-groups (fn-node-acceptance (fn-sn-node s)))))
         (evidence-string (fn-store-octets->string evidence)))
    (mv-let (usage state) (fn-owner-carried-usage evidence-string state)
      (value
       (if (equal groups :bad) nil
         (fn-pcb-carried-event
          (first coordinates) (second coordinates) (third coordinates)
          (fn-store-octets->string msgid) received groups
          (fn-store-octets->string obligation)
          (fn-store-octets->string subject)
          evidence-string charge
          (fn-sn-keyring-snapshots s)
          (fn-owner-transit-carried-list t state)
          (fn-own-clock (fn-owner-core state))
          (if (boundp-global 'fn-owner-transit-budget state)
              (f-get-global 'fn-owner-transit-budget state)
            nil)
          usage))))))

; PRF-099: the refusal class of a present carrier on transit
; (books/peer-carriage.lisp fn-pcb-refusal-class): :no-local-binding,
; :unsupported-profile, :signature-failed or :malformed, or nil.  ED and ML
; are the host's two primitive outcomes (nil when not observed).
(defun fn-owner-transit-refusal-class (received transitp ed ml state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-pcb-refusal-class
          received (fn-sn-keyring-snapshots (fn-owner-store state))
          (fn-owner-transit-carried-list transitp state) ed ml)))

(defun fn-owner-peer-carried-event
    (coordinates msgid received group-codes obligation subject evidence charge
                 observed-ml-key ed-observation ml-observation state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes
                  (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))
    (value
     (if (equal groups :bad) nil
       (fn-pa-authorized-event
        (first coordinates) (second coordinates) (third coordinates)
        (fn-store-octets->string msgid) received groups
        (fn-store-octets->string obligation)
        (fn-store-octets->string subject)
        (fn-store-octets->string evidence) charge
        (fn-sn-keyring-snapshots s)
        observed-ml-key ed-observation ml-observation
        ;; Read the owner clock directly: fn-owner-clock-observation is an
        ;; error triple, and ACL2 refuses it where one value is required
        ;; (the 9c344d1d image build, native-build-production.log:8292).
        (fn-own-clock (fn-owner-core state)))))))

;; PRF-098: the revoked arm's kind-4 event (fn-pa-revoked-event), for the
;; NNTP transit attempt only, with both primitive observations the host made
;; over the carrier's keys (the keys this node once enrolled for the
;; principal).
(defun fn-owner-peer-revoked-event
    (coordinates msgid received group-codes obligation subject evidence charge
                 observed-ml-key ed-observation ml-observation state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes
                  (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))
    (value
     (if (equal groups :bad) nil
       (fn-pa-revoked-event
        (first coordinates) (second coordinates) (third coordinates)
        (fn-store-octets->string msgid) received groups
        (fn-store-octets->string obligation)
        (fn-store-octets->string subject)
        (fn-store-octets->string evidence) charge
        (fn-sn-keyring-snapshots s)
        observed-ml-key ed-observation ml-observation
        (fn-own-clock (fn-owner-core state)))))))

;; PRF-098: the key-statement executor (books/key-statements.lisp), run by
;; the owner after it committed a kind-4 statement composite EVENT.  The
;; request names the primitive observation the host must make (the PoP's
;; D09 subject), or nil; the plan and event are ACL2's.  ROWS are the live
;; configuration's authorities rows (C2).
(defun fn-owner-key-statement-request (event state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-pop-request event)))

(defun fn-owner-key-statement-plan
    (event observed-ml-key ed-observation ml-observation state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-plan event (fn-sn-keyring-snapshots (fn-owner-store state))
                     (fn-cfg-authorities (fn-cfg-value (fn-owner-config state)))
                     observed-ml-key ed-observation ml-observation)))

(defun fn-owner-key-statement-event
    (event observed-ml-key ed-observation ml-observation coordinates state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-execute event (fn-sn-keyring-snapshots (fn-owner-store state))
                        (fn-cfg-authorities (fn-cfg-value (fn-owner-config state)))
                        observed-ml-key ed-observation ml-observation
                        (first coordinates) (second coordinates)
                        (third coordinates))))

(defun fn-owner-key-statement-log-line (plan outcome at-open state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-ks-log-line plan outcome at-open)))

;; PRF-098, the crash cut: the open's recovery (books/key-statements.lisp
;; fn-ks-recover) executes the newest Store record when it is a statement.
;; OCTETS are that record as the open read it; the answer is the decoded
;; event for fnn-owner-key-statement, or nil.
(defun fn-owner-key-statement-pending (octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((records (fn-store-decode-records (list octets))))
    (value (if (and (consp records) (null (cdr records)))
               (fn-ks-pending (car records))
             nil))))

;; D27: the signed composite against the profile the owner was handed at
;; open (books/store-budget-naming.lisp fn-sbud-signed-event-boundary):
;; :ok, :event (no composite formed) or :signed-record (past its R).
(defun fn-owner-signed-event-boundary (event state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sbud-signed-event-boundary (fn-owner-store-profile state) event)))

(defun fn-owner-article-count (state)
  (declare (xargs :stobjs state :mode :program))
  (value (len (fn-state-articles (fn-node-acceptance (fn-owner-node state))))))

; The local-post provenance from the owner's canonical live configuration.
; The native service cannot call fn-store-prov-post: that wrapper reads the
; standalone store bridge's shadow configuration and would stay stale after
; an owner reconfiguration.  This is the same ACL2 construction over the
; configuration that owns the acceptance decision.
(defun fn-owner-prov-post (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((cfg (fn-owner-config state))
         (identity (fn-cfg-policy (fn-cfg-value cfg) "path-identity"))
         (principal (if (and (stringp identity) (not (equal identity "")))
                        identity
                      "local"))
         (p (fn-prov-make-post principal (fn-cfg-generation cfg))))
    (value (fn-record-string-octets
            (if (fn-prov-durablep p) (fn-prov-wire p) (fn-prov-render p))))))

(defun fn-owner-existing-action (msgid-octets payload group-codes state)
  (declare (xargs :stobjs state :mode :program))
  (let ((groups (fn-store-groups-from-codes
                 group-codes
                 (fn-state-groups (fn-node-acceptance (fn-owner-node state))))))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (equal groups :bad) (null groups))
        (value :absent)
      (let ((action (fn-pb-existing-action
                     (fn-store-octets->string msgid-octets) payload groups
                     (fn-owner-store state))))
        (value (if action action :absent))))))

; The same question with the submitted payload in the octet buffer
; (books/octets-stobj.lisp): host/native/owner.lisp fnn-owner-attempt fills
; the buffer once from the byte vector the owner handed back and asks this
; and fn-owner-prepare-buffer over it, so the payload is not consed into a
; list for either.  The decision is fn-pbb-existing-action
; (books/poster-bytes-buffer.lisp), equal to fn-pb-existing-action on the
; buffer's logical value (fn-pbb-existing-action-is-pb-existing-action);
; the list entry's fn-octet-listp test is the buffer's recognizer
; (fn-pbb-buffer-is-octet-listp).
(defun fn-owner-existing-action-buffer (msgid-octets group-codes fn-octets state)
  (declare (xargs :stobjs (fn-octets state) :mode :program))
  (let ((groups (fn-store-groups-from-codes
                 group-codes
                 (fn-state-groups (fn-node-acceptance (fn-owner-node state))))))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (equal groups :bad) (null groups))
        (value :absent)
      (let ((action (fn-pbb-existing-action
                     (fn-store-octets->string msgid-octets) fn-octets groups
                     (fn-owner-store state))))
        (value (if action action :absent))))))

; The subject identity of the payload in the octet buffer.  fn-shb-subject-id
; (books/sha256-buffer.lisp) digests the subject preimage straight from the
; buffer (the fixed head for the buffer's length as a list, the payload by
; index), so the served POST hands the digest no octet list
; (host/native/owner.lisp fnn-owner-attempt through fnn-metadata-buffer,
; host/native/io.lisp).  fn-shb-subject-id-is-id-subject-of-sha256-preimage:
; it is fn-id-subject of fn-sha256 over fn-id-subject-preimage, which is
; fn-id-subject-of-payload (host/store-host.lisp fn-store-subject-id-of-payload,
; the list entry) under books/crypto-attach.lisp.  The length test is the
; list entry's.
(defun fn-owner-subject-id-buffer (fn-octets state)
  (declare (xargs :stobjs (fn-octets state) :mode :program))
  (value (if (<= (fn-octets-len fn-octets) *fn-cbor-max-uint*)
             (fn-shb-subject-id fn-octets)
           nil)))

; -----------------------------------------------------------------------------
; Connections

(defun fn-owner-version (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-view-version (fn-own-view (fn-owner-core state)))))

(defun fn-owner-conn-version (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((conn (fn-own-find-conn id (fn-own-conns (fn-owner-core state)))))
    (value (if conn (fn-own-conn-version conn) nil))))

(defun fn-owner-connection-versions (conns)
  (declare (xargs :mode :program))
  (if (consp conns)
      (cons (fn-own-conn-id (car conns))
            (cons (fn-own-conn-version (car conns))
                  (fn-owner-connection-versions (cdr conns))))
    nil))

(defun fn-owner-connections (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-owner-connection-versions
          (fn-own-conns (fn-owner-core state)))))

; The host's re-entry after the TLS handshake (RFC 4642 section 2.2.2).  It
; is a wire event, not octets: no client input produces it, and
; fn-auth-step is the only thing that reads it.
(defun fn-owner-tls-established (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((owner (fn-owner-core state)))
    (if (not (fn-own-find-conn id (fn-own-conns owner)))
        (value :unknown)
      (let* ((result (fn-ocfg-read-step (fn-owner-ocfg state)
                                        id (list :tls-established)))
             (state (fn-owner-install-ocfg (cdr result) state))
             (state (fn-owner-install-effects (car result) state)))
        (value :ok)))))

; Open pins the committed view and opens one served connection over it
; (fn-own-open); the greeting is the effect list it returns.  A refused open
; (bound reached) installs no connection and returns NIL so the host closes
; the socket without a reply.
(defun fn-owner-open (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (fn-owner-core state))
         (id (fn-own-next-id before))
         (opened (fn-ocfg-open (fn-owner-ocfg state)
                               (fn-owner-auth state)))
         (state (fn-owner-install-ocfg (cdr opened) state))
         (state (fn-owner-install-effects (car opened) state))
         (state (f-put-global 'fn-owner-log-line
                              (fn-olog-connection-line (fn-owner-core state)
                                                       id nil)
                              state)))
    (if (fn-own-find-conn id (fn-own-conns (fn-owner-core state)))
        (value id)
      (value nil))))

; One observed socket region is one ACL2 prefix transition.  Its effects and
; configured-owner state equal fn-ocfg-read over the complete observation
; (fn-ocfg-read-tls-prefix-is-full-read); fn-owner-consumed names the exact
; physical prefix.  The native adapter leaves any suffix for the TLS record
; layer instead of parsing STARTTLS in raw Lisp.
; The call is fn-scar-ocfg-read-tls-prefix (books/owner-served-carried.lisp),
; which equals fn-ocfg-read-tls-prefix under the configured owner's relation
; (fn-scar-ocfg-read-tls-prefix-is-reference-under-ocl-relation): it takes the
; store node's fn-node-statep from that relation instead of re-evaluating it,
; O(N^2) in the archive, four times per read.  It also passes the owner
; view's Message-ID trie to the peer step, so an IHAVE/CHECK duplicate test is
; one trie lookup instead of a scan of the node's articles and bindings
; (books/peer-offer-indexed.lisp, fn-pix-history-hasp-is-peer-history-hasp);
; the trie premise fn-scar-view-indexedp is carried by every owner transition
; (books/owner-offer-indexed.lisp).  A peer session's events run
; fn-pgc-peer-arm (books/peer-guard-carried.lisp, D24), whose guard names no
; node recognizer, so no peer event evaluates fn-node-statep either
; (fn-pgc-peer-arm-is-peer-step-pinned).
(defun fn-owner-chunk (id octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((owner (fn-owner-core state)))
    (if (not (fn-own-find-conn id (fn-own-conns owner)))
        (value :unknown)
      (let* ((result (fn-scar-ocfg-read-tls-prefix
                      (fn-owner-ocfg state) id octets))
             (state (fn-owner-install-ocfg
                     (fn-own-tls-result-owner result) state))
             (state (fn-owner-install-effects
                     (fn-own-tls-result-effects result) state))
             (state (f-put-global 'fn-owner-consumed
                                  (fn-own-tls-result-consumed result) state))
             ; One line per 441 the effects send (books/owner-log.lisp
             ; fn-olog-served-refusal-lines-one-per-441).
             (state (f-put-global 'fn-owner-refusal-lines
                                  (fn-olog-served-refusal-lines
                                   (fn-owner-core state) id
                                   (fn-own-tls-result-effects result))
                                  state)))
        (value :ok)))))

(defun fn-owner-close (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn-owner-step (list :close id) state)))
    (value :closed)))

; The host-fault boundary (books/owner-fault.lisp).
;
; tools/run_owner.py calls this when it has caught an exception it did not
; expect while serving connection `id': the model decides the reply line, the
; close and everything that happens to the owner (`fn-own-fault'), and the
; host's only remaining decision is that it will not use that socket again.
; The result is installed through the same `fn-owner-install-effects' every
; other entry uses, so the host reads the reply out of `fn-owner-output' and
; the close out of `fn-owner-closep' exactly as it does for a served read.
;
; `:faulted' is answered when there was a connection to answer, `:unknown'
; when there was not; the owner has forgotten `id' either way.  The host
; reports the two differently because a fault naming no connection is a host
; defect and not a served event.
(defun fn-owner-fault (id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (knownp (if (fn-own-find-conn id (fn-own-conns owner)) t nil))
         (result (fn-ocfg-fault (fn-owner-ocfg state) id))
         (state (fn-owner-install-ocfg (cdr result) state))
         (state (fn-owner-install-effects (car result) state)))
    (value (if knownp :faulted :unknown))))

(defun fn-owner-advance (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn-owner-step (list :advance id) state)))
    (fn-owner-conn-version id state)))

; -----------------------------------------------------------------------------
; Clock observations and group facts

; The word is fn-own-observe-outcome's (books/owner.lisp; decision D10-a).
; This used to compare the owner before and after the event and answer
; :rejected whenever nothing moved, which spelled an ADMITTED reading equal
; to the one already held exactly like a contradicted clock, and put the
; decision in the host.  Nothing here judges a reading.
(defun fn-owner-observe (monotonic wall wall-error has-wall state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((obs (fn-clock-observation monotonic wall wall-error has-wall))
         (outcome (fn-own-observe-outcome (fn-owner-core state) obs))
         ; fn-ocfg-observe, not fn-owner-step: it is fn-ocfg-step's
         ; (:observe obs) arm (fn-ocfg-step-observe-is-fn-ocfg-observe,
         ; books/owner-config-observe.lisp) with guard t, so the reading the
         ; host takes before every socket read no longer evaluates the
         ; whole-store guard of the unverified fn-ocfg-step.
         (state (fn-owner-install-ocfg
                 (fn-ocfg-observe (fn-owner-ocfg state) obs) state)))
    (value outcome)))

(defun fn-owner-declare-group (name-octets state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-store-text-octetsp name-octets))
      (value :invalid)
    (let* ((before (fn-owner-core state))
           (state (fn-owner-step
                   (list :declare-group (fn-store-octets->string name-octets))
                   state)))
      (value (if (equal (fn-owner-core state) before) :refused :declared)))))

(defun fn-owner-group-facts (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-replay-facts (fn-own-facts (fn-owner-core state)))))

; -----------------------------------------------------------------------------
; The outbound feed (books/owner-feed.lisp; specs/peering.md 3, milestone 3)
;
; One outbound client connection per configured peer with work.  Every
; decision is the book's: which peers an article is offered to
; (fn-own-feed-targets), when an offer may go out (fn-feed-selection inside
; fn-feed-tick-step), what the offer line is (fn-feed-offer-line), what a
; reply code means (fn-feed-observe) and what the journal record for each is
; (fn-own-feed-*-record).  This file frames octets and moves them; it names
; no code, no wildmat, no Message-ID and no FNFD field.
;
; The order is "durable before the effect": every entry point below leaves
; the records it authorizes in `fn-owner-feed-records' and the bytes in
; `fn-owner-feed-command'; tools/run_owner.py appends the records to
; <journal>/feed/<peer>.fnfd and fsyncs BEFORE it writes the bytes.

(defun fn-owner-feed-configure (state)
  ; Rebuild the feed table from the live configuration: at open and after
  ; every :set-peer / :remove-peer delta.
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn-owner-step (list :feeds (fn-owner-config state)) state)))
    (value (fn-store-cfg-join-names
            (fn-own-feed-names (fn-own-feeds (fn-owner-core state)))))))

(defun fn-owner-feed-peers (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-own-feed-names (fn-own-feeds (fn-owner-core state))))))

(defun fn-owner-feed-record (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        nil
      (fn-own-feed-record-of peer (fn-own-feeds (fn-owner-core state))))))

; Where to dial: the peer record's transport row, read by ACL2.  The host
; does not parse the configuration.
(defun fn-owner-feed-host (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((transport (fn-cfg-peer-transport (fn-owner-feed-record peer-octets state))))
    (value (if (and (consp transport) (equal (car transport) :nntp))
               (fn-record-string-octets
                (if (equal (len transport) 5) (caddr transport)
                  (fn-cfg-ag-car (fn-cfg-ag-cdr transport))))
             nil))))

(defun fn-owner-feed-port (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((transport (fn-cfg-peer-transport (fn-owner-feed-record peer-octets state))))
    (value (if (and (consp transport) (equal (car transport) :nntp))
               (nfix (if (equal (len transport) 5) (cadddr transport)
                       (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr transport)))))
             0))))

(defun fn-owner-feed-security (peer-octets state)
  "ACL2-owned outbound security tuple; old records are clear by definition."
  (declare (xargs :stobjs state :mode :program))
  (let ((transport (fn-cfg-peer-transport (fn-owner-feed-record peer-octets state))))
    (value (if (and (equal (car transport) :nntp) (equal (len transport) 5))
               (car (cddddr transport))
             '(:clear)))))

(defun fn-owner-feed-auth-policy (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cfg-peer-outbound-auth
          (fn-owner-feed-record peer-octets state))))

(defun fn-owner-feed-profile-decode (octets)
  (declare (xargs :mode :program))
  (fn-fap-decode octets))

(defun fn-owner-feed-profile-max-octets ()
  (declare (xargs :mode :program))
  *fn-fap-max-octets*)

(defun fn-owner-feed-streamingp (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (value (if (fn-cfg-peer-streamingp (fn-owner-feed-record peer-octets state))
             t
           nil)))

; How long the host must wait between dial attempts for this peer: the peer
; record's own outbound backoff.  Read here so the NUMBER stays ACL2's; the
; host only measures the interval with the clock it already owns.
;
; Without it the host dialled on queue length alone, and the feed machine's
; backoff does not gate a dial (it gates `fn-feed-selection`, which needs a
; connection first).  A peer that was down therefore drew a fresh TCP
; connection about five times a second for as long as one entry stayed
; queued: 9,479 refused connections in one two-node gate run, all of them in
; the window where one node was restarting.
(defun fn-owner-feed-backoff-ms (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((record (fn-owner-feed-record peer-octets state)))
    (value (if (and record (natp (fn-cfg-peer-backoff record)))
               (fn-cfg-peer-backoff record)
             0))))

; Is there an entry this feed could OFFER if it had a connection: a
; `:queued` one, which is what `fn-feed-selection` picks.  Queue length is
; not that question -- an entry in flight is in the queue -- and answering
; the wrong one is what made a peer that lost a reply a denial of service:
; the entry stayed `:sent`, the host re-dialled on queue length alone every
; few seconds, each dial took a connection on the peer that the peer did not
; release, and the peer reached its `--max-connections` bound and began
; refusing EVERY client at accept.  Measured on two-node gate `a5c6792`:
; seven tap sessions, `MODE STREAM` and nothing else in each, and node B
; closing the harness's reader probes for the next 90 s.
;
; This does not resolve the in-flight entry -- only a restart does today,
; and the packet that fixes it is in the lane handoff.  It stops the host
; opening a socket it has nothing to send on.
(defun fn-owner-feed-has-queued (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (value (if (fn-feed-head-queued
                  (fn-feed-queue
                   (fn-own-feed-find peer (fn-own-feeds
                                           (fn-owner-core state)))))
                 t
               nil)))))

(defun fn-owner-feed-queue-length (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value 0)
      (value (len (fn-feed-queue
                   (fn-own-feed-find peer (fn-own-feeds
                                           (fn-owner-core state)))))))))

; A raw TCP descriptor starts in the ACL2 connection phase below.  Only a
; successful greeting (and configured MODE STREAM exchange) makes this feed
; live for selection.
(defun fn-owner-feed-connect (peer-octets conn state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (or (equal peer :bad) (not (natp conn)))
        (value nil)
      (let ((state (fn-owner-step (list :feed-conn peer conn) state)))
        (value :ok)))))

(defun fn-owner-feed-dial-open (peer-octets conn user pass allow-clear state)
  "Install greeting/MODE state without treating a TCP socket as a feed.

FN-OWNER-RECOVER installs the carried table invariant, and this is its only
constructor thereafter.  It deliberately does not rescan every peer/framer on
a dial: the selected peer entry is the owner-feed boundary being opened."
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (or (equal peer :bad) (not (natp conn)))
        (value :invalid)
      (let* ((inputs (f-get-global 'fn-owner-feed-inputs state))
             (entry (fn-own-feed-entry-of peer
                                          (fn-own-feeds (fn-owner-core state)))))
        (if (null entry)
            (value :fault)
          (let* ((streamingp (fn-cfg-peer-streamingp
                               (fn-own-feed-entry-record entry)))
                 (transport (fn-cfg-peer-transport (fn-own-feed-entry-record entry)))
                 (security (if (equal (len transport) 5)
                               (let ((s (car (cddddr transport))))
                                 (if (equal s '(:clear)) :clear (cadr s)))
                             :clear))
                 (state (f-put-global
                         'fn-owner-feed-inputs
                         (fn-fc-table-put
                          peer
                          (if user
                              (fn-fc-initial-auth-state streamingp conn security
                                                        user pass allow-clear)
                            (fn-fc-initial-state streamingp conn security))
                          inputs)
                         state)))
            (value (if (equal security :implicit) :await-tls :await-greeting))))))))

(defun fn-owner-feed-tls-established (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((peer (fn-store-octets->string peer-octets))
         (inputs (f-get-global 'fn-owner-feed-inputs state))
         (step (and (not (equal peer :bad))
                    (fn-fc-after-tls (fn-fc-table-lookup peer inputs)))))
    (if (null step) (value :invalid)
      (let ((state (f-put-global 'fn-owner-feed-inputs
                                 (fn-fc-table-put peer (fn-fc-next-state step) inputs) state)))
        (case (fn-fc-kind step)
          (:mode (let ((state (f-put-global 'fn-owner-feed-command
                                            (fn-fc-mode-command) state))) (value :mode)))
          (:auth-user
           (let ((state (f-put-global 'fn-owner-feed-command
                                      (fn-fc-auth-user-command
                                       (fn-fc-next-state step)) state)))
             (value :auth-user)))
          (:ready (value :ready))
          (:need-input (value :need-input))
          (otherwise (value :invalid)))))))

(defun fn-owner-feed-read-limit ()
  "ACL2-owned upper bound for one native feed socket-read observation."
  (declare (xargs :mode :program))
  *fn-feed-wire-input-max-chunk-octets*)

; The raw socket layer enforces this one TCP completion deadline after DNS has
; produced an address.  It is deliberately a local ACL2 policy rather than a
; feed-service literal: a caller cannot silently widen an unavailable peer's
; attempt window.  DNS remains a separate host availability boundary.
(defconst *fn-owner-feed-connect-timeout-seconds* 10)

(defun fn-owner-feed-connect-timeout ()
  "ACL2-owned TCP completion deadline for one outbound peer dial."
  (declare (xargs :mode :program))
  *fn-owner-feed-connect-timeout-seconds*)

; One tick for one peer: the records first, then the bytes.
(defun fn-owner-feed-tick (peer-octets monotonic state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (let* ((owner (fn-owner-core state))
             (obs (fn-clock-observation monotonic 0 0 nil))
             (result (fn-own-feed-port-tick-peer
                      peer (fn-own-feeds owner) obs)))
        (mv-let (status state)
          (fn-owner-feed-install-port-result owner result state)
          (value (if (equal status :refused) :refused
                   (if (fn-own-feed-port-effects result) :offer :idle))))))))

; One reply line from one peer.
(defun fn-owner-feed-octets (peer-octets line monotonic state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (let* ((owner (fn-owner-core state))
             (obs (fn-clock-observation monotonic 0 0 nil))
             (entry (fn-own-feed-entry-of peer (fn-own-feeds owner)))
             (feed (fn-own-feed-entry-feed entry))
             (msgid (fn-own-feed-inflight-msgid (fn-feed-queue feed)))
             (response (fn-own-feed-parse-response line msgid)))
        (if (null response)
            (let ((state (fn-owner-feed-install-feed nil nil state)))
              (value :quiet))
          (let* ((result (fn-own-feed-port-observe-peer
                         peer (fn-own-feeds owner) response
                         (fn-own-feed-article owner msgid) obs))
                ; The sender's one line for this reply (nil for a 335/238),
                ; books/owner-log.lisp fn-olog-feed-reply-line.
                (state (f-put-global 'fn-owner-feed-log-line
                                     (fn-olog-feed-reply-line owner peer response)
                                     state)))
            (mv-let (status state)
              (fn-owner-feed-install-port-result owner result state)
              (value (if (equal status :refused) :refused
                       (if (fn-own-feed-port-effects result) :send :quiet))))))))))

(defun fn-owner-feed-connection-result-kind (step)
  "Map only a connection-phase refusal away from the feed-port outcome tag.

The feed port's :REFUSED means an ACL2 transition may have produced a fresh
FNFD record batch.  A greeting or MODE rejection produces no such batch, so
it is :CONNECTION-REFUSED and the raw adapter must close this peer without
flushing the previous peer's pending projection."
  (if (equal (fn-fc-kind step) :refused) :connection-refused (fn-fc-kind step)))

(defun fn-owner-feed-reply-chunk (peer-octets octets monotonic state)
  "Consume one ACL2 connection/reply event; nil drains retained input.

Greeting and MODE replies stay inside fn-fc.  A normal feed reply reaches the
existing port only after fn-fc has made this connection ready."
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (or (equal peer :bad) (not (fn-wire-octet-listp octets)))
        (value :invalid)
      (let* ((inputs (f-get-global 'fn-owner-feed-inputs state))
             (input (fn-fc-table-lookup peer inputs)))
        ;; The table invariant is carried from recovery through only
        ;; put/remove.  This served path validates the selected connection,
        ;; never every peer's retained buffer.
        (if (not (fn-fc-statep input))
            (value :invalid)
          (let* ((state (f-put-global 'fn-owner-feed-log-line nil state))
                 (step (fn-fc-step input octets))
                 (kind (fn-owner-feed-connection-result-kind step))
                 (state (f-put-global
                         'fn-owner-feed-inputs
                         (fn-fc-table-put peer (fn-fc-next-state step) inputs)
                         state)))
            (case kind
                  (:mode
                   (let ((command (fn-fc-mode-command)))
                     (if (null command)
                         (value :fault)
                       (let ((state (f-put-global 'fn-owner-feed-command command state)))
                         (value :mode)))))
                  (:auth-user
                   (let ((command (fn-fc-auth-user-command (fn-fc-next-state step))))
                     (if (null command) (value :fault)
                       (let ((state (f-put-global 'fn-owner-feed-command command state)))
                         (value :auth-user)))))
                  (:auth-pass
                   (let ((command (fn-fc-auth-pass-command (fn-fc-next-state step))))
                     (if (null command) (value :fault)
                       (let ((state (f-put-global 'fn-owner-feed-command command state)))
                         (value :auth-pass)))))
                  (:starttls
                   (let ((command (fn-fc-starttls-command)))
                     (if (null command) (value :fault)
                       (let ((state (f-put-global 'fn-owner-feed-command command state)))
                         (value :starttls)))))
                  (:tls (value :tls))
                  (:ready
                   (mv-let (erp word state)
                     (fn-owner-feed-connect peer-octets
                                            (fn-fc-conn (fn-fc-next-state step)) state)
                     (if erp (mv erp word state)
                       (if (equal word :ok) (value :ready) (value :fault)))))
                  (:reply
                   (mv-let (erp word state)
                     (fn-owner-feed-octets peer-octets (fn-fc-line step)
                                            monotonic state)
                     (if erp (mv erp word state) (value word))))
                  (:need-input (value :need-input))
                  (:connection-refused (value :connection-refused))
                  (:closed (value :closed))
                  (:invalid (value :invalid))
                  (otherwise (value :fault)))))))))


; The connection to ONE peer is gone.  The host reports the event and the
; time it happened; ACL2 decides what it means.  `fn-own-feed-lost-records'
; is read off the state BEFORE it moves and `fn-own-feed-lost' moves it, so
; the frame the host then appends is the one the transition authorized.
; There are no bytes: a lost connection emits no command, which is why the
; effects argument is nil.
;
; Before this entry point existed the host told the owner only
; `(:feed-conn peer nil)' and the in-flight entry stayed :sent until the
; PROCESS restarted -- the blocker in front of K5's restart-by-offer
; (planning/lanes/HANDOFF-w11-twonode-feed.md).  The requeue decision is
; `fn-feed-lost''s; the host decides only when to hand the model the event.
(defun fn-owner-feed-lost (peer-octets monotonic state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (let* ((inputs (f-get-global 'fn-owner-feed-inputs state))
             (owner (fn-owner-core state))
             (obs (fn-clock-observation monotonic 0 0 nil))
             (result (fn-own-feed-port-lost-peer
                      peer (fn-own-feeds owner) obs)))
        ;; Removal is the other carried-table transition; a lost peer has no
        ;; reason to revalidate unrelated live connections or suffixes.
        (mv-let (status state)
          (fn-owner-feed-install-port-result owner result state)
          (let ((state (f-put-global 'fn-owner-feed-inputs
                                     (fn-fc-table-remove peer inputs)
                                     state)))
            (value (if (equal status :refused) :refused :ok))))))))

; Which peer's journal each pending frame belongs in, in the same order as
; the frames: the record's own field 0, read by ACL2.
(defun fn-owner-feed-record-peer-names (records)
  (declare (xargs :mode :program))
  (if (consp records)
      (cons (fn-record-octets-string
             (fn-feed-record-peer (fn-feed-journal-values (car records))))
            (fn-owner-feed-record-peer-names (cdr records)))
    nil))

(defun fn-owner-feed-record-peers (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-owner-feed-record-peer-names
           (f-get-global 'fn-owner-feed-records state)))))

(defun fn-owner-feed-frames (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-feed-frames state)))

(defun fn-owner-feed-command (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-feed-command state)))

(defun fn-owner-feed-command-status (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-feed-command-status state)))

; The protected prefix and trailer belong to ACL2, including the boundary
; between them. Python receives the whole sealed frame and never slices it.
(defun fn-owner-feed-sealed-frame (index state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((frame (fn-frame-item index (f-get-global 'fn-owner-feed-frames state)))
         (prefix (fn-frame-protected-prefix frame)))
    (value (append prefix (fn-frame-trailer prefix)))))

; One bounded read from the physical journal. The scanner owns acceptance,
; the exact safe offset and the entry fed to the existing replay transition.
(defun fn-owner-feed-journal-scan (peer-octets prefix frame state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((peer (fn-store-octets->string peer-octets))
         (result (fn-feed-journal-scan peer-octets prefix frame
                   (f-get-global 'fn-owner-feed-safe-offset state))))
    (if (equal peer :bad)
        (value :invalid)
      (if (equal (car result) :next)
          (let* ((entry (nth 2 result))
                 (state (fn-owner-step
                         (list :feed-replay peer (list entry)) state))
                 (state (f-put-global
                         'fn-owner-feed-intents
                         (fn-own-feed-intent-apply
                          (f-get-global 'fn-owner-feed-intents state)
                          (fn-feed-journal-kind entry)
                          (fn-feed-journal-values entry))
                         state))
                 (state (f-put-global 'fn-owner-feed-safe-offset
                                      (nth 1 result) state)))
            (value :next))
        (value (car result))))))

; The fence a process death owes every feed: one (:feed-restart peer) record
; per peer, durable, then fn-feed-restart on each.  fn-own-reopen does the
; restart; this is the record side and the entry point a recovering host
; calls once, after the replay and before any command.
(defun fn-owner-feed-restart (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (fn-owner-core state))
         (table (fn-own-feeds owner))
         (result (fn-own-feed-port-restart-fold
                  (fn-own-feed-names table) table table)))
    (mv-let (status state)
      (fn-owner-feed-install-port-result owner result state)
      (value (if (equal status :refused) :refused
               (len (fn-own-feed-port-records result)))))))

; -----------------------------------------------------------------------------
; The NEWNEWS pull feed (PRF-100, books/peer-pull.lisp).  The pulled peers of
; the one live configuration, read by ACL2; host/native/pull-service.lisp
; drives each round through the pure fn-pull-* functions.
(defun fn-owner-pull-plans (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-pull-plans (fn-cfg-peers (fn-owner-config state)))))
