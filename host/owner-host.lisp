; Experimental owner bridge: :program wrappers over the proved fn-own machine.
;
; tools/run_owner.py drives one owner per store through these entry points.
; Every wrapper is one fn-own-step, one fn-own-read (the served port: one
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
(include-book "../books/owner")
;
; Loaded here, not left to a bridge's `ld' order: this file uses names
; host/store-node-host.lisp (and host/store-host.lisp under it) defines, so a session that loads this file alone
; must get them too.  A second `ld' of a file already in the session
; re-admits identical definitions, which ACL2 accepts as redundant.
(ld "store-node-host.lisp" :ld-error-action :error)

; The injecting-agent identity this owner uses (books/injection.lisp reads
; it for Path, Injection-Info and any generated Message-ID).  Configuration,
; not a decision.
(defconst *fn-owner-agent*
  '(102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100))

(defun fn-owner-group-octets (names)
  (declare (xargs :mode :program))
  (if (consp names)
      (cons (fn-nntp-string-octets (car names))
            (fn-owner-group-octets (cdr names)))
    nil))

; The posting configuration: the groups served at the live configuration
; generation (books/node-config, fn-cnode-served-of), the store's payload
; bound.  Derived from the replayed configuration by ACL2.
; The node's own <path-identity>, from the ONE slot that holds it: the
; configuration policy `path-identity`, which `fn-peer-local-identity`
; (books/peer-inbound.lisp) and `fn-store-prov-post` also read.
; `*fn-owner-agent*` was a second copy of a node's identity, and that is how
; two fn nodes on one gate came to write the SAME Path -- so neither could
; recognise itself in the other's articles and RFC 5537 section 3.5 loop
; suppression had nothing to compare. The constant is now only the fallback
; for a store whose slot is unset.
(defun fn-owner-agent-of (cfg)
  (declare (xargs :mode :program))
  (let ((identity (fn-cfg-policy (fn-cfg-value cfg) "path-identity")))
    (if (and (stringp identity) (not (equal identity "")))
        (fn-record-string-octets identity)
      *fn-owner-agent*)))

(defun fn-owner-post-config (cfg)
  (declare (xargs :mode :program))
  (fn-inj-make-config t (fn-owner-agent-of cfg)
                      (fn-owner-group-octets (fn-cnode-served-of cfg))
                      *fn-store-max-payload*))

(defun fn-owner-state (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner state)))

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

; The process root.  A decoded observed image opens through
; fn-sn-open-observed exactly as host/store-node-host.lisp does; the owner
; is started over that state (fn-own-open-observed-start-relation).  The
; dispatch is on the typed result's kind, never on fn-sn-open-okp, which
; would run the whole-state recognizer once more per recovery: a result of
; kind :ok is fn-sn-open-okp by fn-own-open-kind-ok-is-okp
; (books/owner-invariants.lisp, under fn-sn-open-observed-result-is-typed).
; The configuration history is replayed first (fn-cnode-config-replay,
; books/node-config), exactly as host/store-node-host.lisp fn-store-sn-recover
; does; the node opens over the allocation domain and the configured capacity
; and the live configuration is kept in the same global the store bridge's
; fn-store-cfg-* entries read.
(defun fn-owner-recover (octet-records frontier config-octet-records max-conns state)
  (declare (xargs :stobjs state :mode :program))
  (let ((records (fn-store-decode-records octet-records))
        (config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (equal records :bad) (equal config-records :bad)
            (null config-records) (not (natp max-conns)))
        (value :fault)
      (let ((replayed (fn-cnode-config-replay config-records)))
        (if (not (equal (fn-replay-result-kind replayed) :ok))
            (value :fault)
          (let* ((cn (fn-replay-result-node replayed))
                 (cfg (fn-cnode-config cn))
                 (opened (fn-sn-open-observed (fn-cnode-domain cn)
                                              (fn-cfg-capacity (fn-cfg-value cfg))
                                              frontier records)))
            (if (and (equal (fn-sn-open-kind opened) :ok)
                     (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                            :recovering))
                (let* ((state (f-put-global 'fn-store-cfg cfg state))
                       (state (f-put-global 'fn-owner
                                            (fn-own-configure
                                             (fn-own-start (fn-sn-open-state opened)
                                                           max-conns)
                                             (fn-owner-post-config cfg))
                                            state)))
                  (value :recovering))
              (value :fault))))))))

(defun fn-owner-store (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-own-store (f-get-global 'fn-owner state)))

(defun fn-owner-node (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-sn-node (fn-owner-store state)))

(defun fn-owner-step (event state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner
                             (fn-own-step (f-get-global 'fn-owner state) event)
                             state)))
    state))

; -----------------------------------------------------------------------------
; The transaction path: the same observations run_store.py reports, each one
; a (:store ...) owner event.

(defun fn-owner-io (operation result state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn-owner-step (list :store (list :io operation result)) state)))
    (value (fn-sf-phase (fn-sn-files (fn-owner-store state))))))

(defun fn-owner-prepare (msgid-octets payload group-codes id-octets
                          subject-octets evidence-octets charge state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (> (len payload) *fn-store-max-payload*)
            (equal groups :bad) (null groups)
            (not (fn-store-text-octetsp id-octets))
            (not (fn-store-text-octetsp subject-octets))
            (not (fn-store-text-octetsp evidence-octets)) (not (posp charge)))
        (value :invalid)
      ; A name in the domain but not served at the live generation (a retired
      ; group) is refused by the predicate fn-cnode-prepare applies.
      (if (not (fn-cnode-selection-servedp (f-get-global 'fn-store-cfg state) groups))
          (value :refused)
      (let* ((node (fn-sn-node s))
             (msgid (fn-store-octets->string msgid-octets))
             (existing (fn-store-article-match msgid payload groups node)))
        (if existing
            (value existing)
          (let* ((record (fn-record-make (len (fn-sf-records (fn-sn-files s)))
                                         (fn-state-next-txid (fn-node-acceptance node))
                                         (fn-state-next-txid (fn-node-acceptance node))
                                         msgid payload groups
                                         (fn-store-octets->string id-octets)
                                         (fn-store-octets->string subject-octets)
                                         (fn-store-octets->string evidence-octets)
                                         charge))
                 (state (fn-owner-step (list :store (list :prepare record)) state)))
            (if (equal (fn-owner-store state) s)
                (value :refused)
              (value :prepared)))))))))

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
  (let ((record (fn-sf-record-candidate (fn-sn-files (fn-owner-store state)))))
    (value (if record (fn-record-encode record) nil))))

; Completion is the owner's (:complete) event: fn-sn-finish consumed once,
; its pair appended to the ledger once (fn-own-completion-consumed-once).
(defun fn-owner-finish (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (f-get-global 'fn-owner state))
         (before-files (fn-sn-files (fn-own-store before)))
         (state (fn-owner-step (list :complete) state))
         (after (f-get-global 'fn-owner state))
         (after-files (fn-sn-files (fn-own-store after))))
    (if (and (equal (fn-sf-phase before-files) :completing)
             (equal (fn-sf-phase after-files) :ready)
             (equal (len (fn-own-ledger after))
                    (1+ (len (fn-own-ledger before)))))
        (value :durable)
      (value :fault))))

(defun fn-owner-begin (id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (f-get-global 'fn-owner state))
         (state (fn-owner-step (list :begin id) state)))
    (value (if (equal (f-get-global 'fn-owner state) before) :refused :begun))))

; The writer step: fn-own-take-submission moves the oldest queued submission
; into the durable path when nothing is in flight, no transaction is pending
; and the store is :ready.  The submission in flight is exposed to the host
; through four globals read off the injection decision; the host passes them
; back through fn-owner-prepare exactly as the CLI passes its own.
(defun fn-owner-take (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (f-get-global 'fn-owner state))
         (state (fn-owner-step (list :take) state))
         (after (f-get-global 'fn-owner state))
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
             (state (f-put-global 'fn-owner-submit-octets
                                  (if transitp
                                      (fn-peer-submission-octets decision)
                                    (fn-inj-decision-octets decision))
                                  state))
             ; A transit submission's memberships are not in the submission:
             ; they are fn-peer-scope-groups of the article's Newsgroups and
             ; the peer record, computed by fn-owner-transit-decide below
             ; over the live node, never here and never in Python.
             (state (f-put-global 'fn-owner-submit-groups
                                  (if transitp nil (fn-inj-decision-groups decision))
                                  state)))
        (value (if transitp :taken-transit :taken))))))

; -----------------------------------------------------------------------------
; The transit port (specs/peering.md 2.2).
;
; Accept: the host resolves the connecting address to a configured peer name
; with fn-owner-peer-for-address (the record's auth slot decides, not the
; client) and opens the connection with fn-own-open-peer, which pins the
; node and the live configuration into the session.  A reader opens with
; fn-owner-open as before, on the same listener.

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
                   (fn-cfg-peers (fn-cfg-value (f-get-global 'fn-store-cfg state)))
                   address)))
        (value (if name (fn-record-string-octets name) nil))))))

(defun fn-owner-open-peer (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (let* ((before (f-get-global 'fn-owner state))
             (id (fn-own-next-id before))
             (opened (fn-own-open-peer before peer (f-get-global 'fn-store-cfg state)))
             (state (f-put-global 'fn-owner (cdr opened) state))
             (state (fn-owner-install-effects (car opened) state)))
        (if (fn-own-find-conn id (fn-own-conns (f-get-global 'fn-owner state)))
            (value id)
          (value nil))))))

; The transfer decision for the transit submission in flight, over the LIVE
; node and the live configuration (RFC 4644 2.4.2: the offer was advisory).
; Every check of specs/peering.md 2.2 is in fn-peer-decide-transfer; this
; wrapper only reads its answer and the memberships fn-peer-injection-arguments
; derives, and leaves them where the bridge can read them.  The obligation id
; and the subject are the host's digests, as for POST (fn-frame-digest is
; constrained and unattached).
(defun fn-owner-group-octet-list (names)
  ; Group NAMES as octets, so `fn-owner-submit-groups' holds one
  ; representation whatever path filled it.
  (declare (xargs :mode :program))
  (if (consp names)
      (cons (fn-record-string-octets (car names))
            (fn-owner-group-octet-list (cdr names)))
    nil))

(defun fn-owner-transit-decide (id-octets subject-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (f-get-global 'fn-owner state))
         (sub (fn-own-inflight owner)))
    (if (not (fn-own-transit-subp sub))
        (value :not-transit)
      (let* ((decision (fn-own-sub-decision sub))
             (node (fn-sn-node (fn-own-store owner)))
             (cfg (f-get-global 'fn-store-cfg state))
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
                                                    0 id subject))
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
                 ; It answers with STRINGS (`fn-record-octets-string', see
                 ; books/peer-inbound.lisp fn-peer-scope-groups) where the
                 ; POST path's `fn-inj-decision-groups' answers with octets,
                 ; and the host reads ONE global for both.  Reading a string
                 ; as an octet list raised `unexpected ACL2 octet-list
                 ; result' inside `Owner.drain', which does not catch, so the
                 ; OWNER PROCESS DIED on the first article a peer transferred
                 ; -- the second half of the w10/v0-matrix board ASK.  The
                 ; conversion is ACL2's own and happens here, so the two
                 ; paths agree on a representation without Python choosing
                 ; one.
                 (state (f-put-global 'fn-owner-submit-groups
                                      (if (equal (fn-peer-decision-kind d) :want)
                                          (fn-owner-group-octet-list (nth 3 args))
                                        nil)
                                      state))
                 (state (f-put-global 'fn-owner-transit-evidence
                                      (fn-record-string-octets
                                       (fn-peer-evidence peer cfg))
                                      state)))
            (value (fn-peer-decision-kind d))))))))

; The transit reply.  `kind' and `reason' are the decision this image just
; made; `word' is the store's observed outcome (:durable, :refused,
; :uncertain), ignored unless the decision was :want.
(defun fn-owner-transit-outcome (id kind reason word state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((result (fn-own-transit-outcome (f-get-global 'fn-owner state)
                                         id kind reason word))
         (state (f-put-global 'fn-owner (cdr result) state))
         (state (fn-owner-install-effects (car result) state)))
    (value :fed)))

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
(defun fn-owner-outcome (id word state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((result (fn-own-outcome (f-get-global 'fn-owner state) id word))
         (state (f-put-global 'fn-owner (cdr result) state))
         (state (fn-owner-install-effects (car result) state)))
    (value :fed)))

; The allocation domain the owner's live node carries (every name ever
; created): the store bridge's fn-store-cfg-domain reads the global
; fn-store-sn, which the owner never sets (its store lives in fn-owner), so
; the owner answers the same question from its own node.
(defun fn-owner-domain (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-state-groups (fn-node-acceptance (fn-owner-node state))))))

(defun fn-owner-next-txid (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-state-next-txid (fn-node-acceptance (fn-owner-node state)))))

(defun fn-owner-article-count (state)
  (declare (xargs :stobjs state :mode :program))
  (value (len (fn-state-articles (fn-node-acceptance (fn-owner-node state))))))

(defun fn-owner-existing-action (msgid-octets payload group-codes state)
  (declare (xargs :stobjs state :mode :program))
  (let ((groups (fn-store-groups-from-codes
                 group-codes
                 (fn-state-groups (fn-node-acceptance (fn-owner-node state))))))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (equal groups :bad) (null groups))
        (value :absent)
      (let ((action (fn-store-article-match
                     (fn-store-octets->string msgid-octets) payload groups
                     (fn-owner-node state))))
        (value (if action action :absent))))))

; -----------------------------------------------------------------------------
; Connections

(defun fn-owner-version (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-view-version (fn-own-view (f-get-global 'fn-owner state)))))

(defun fn-owner-conn-version (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((conn (fn-own-find-conn id (fn-own-conns (f-get-global 'fn-owner state)))))
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
          (fn-own-conns (f-get-global 'fn-owner state)))))

; Open pins the committed view and opens one served connection over it
; (fn-own-open); the greeting is the effect list it returns.  A refused open
; (bound reached) installs no connection and returns NIL so the host closes
; the socket without a reply.
; -----------------------------------------------------------------------------
; The AUTHINFO policy (RFC 4643), set once at start-up and pinned per
; connection.
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

; The host's re-entry after the TLS handshake (RFC 4642 section 2.2.2).  It
; is a wire event, not octets: no client input produces it, and
; fn-auth-step is the only thing that reads it.
(defun fn-owner-tls-established (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((owner (f-get-global 'fn-owner state)))
    (if (not (fn-own-find-conn id (fn-own-conns owner)))
        (value :unknown)
      (let* ((result (fn-own-read-step owner id (list :tls-established)))
             (state (f-put-global 'fn-owner (cdr result) state))
             (state (fn-owner-install-effects (car result) state)))
        (value :ok)))))

(defun fn-owner-open (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (f-get-global 'fn-owner state))
         (id (fn-own-next-id before))
         (opened (fn-own-open before (fn-owner-auth state)))
         (state (f-put-global 'fn-owner (cdr opened) state))
         (state (fn-owner-install-effects (car opened) state)))
    (if (fn-own-find-conn id (fn-own-conns (f-get-global 'fn-owner state)))
        (value id)
      (value nil))))

; One socket read of one connection is one fn-own-read: fn-served-step over
; the connection's wire, session and pinned archive
; (fn-own-read-is-served-step-on-pinned-prefix).  The whole chunk is
; consumed; there is no suffix and no loop in Python.
(defun fn-owner-chunk (id octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((owner (f-get-global 'fn-owner state)))
    (if (not (fn-own-find-conn id (fn-own-conns owner)))
        (value :unknown)
      (let* ((result (fn-own-read owner id octets))
             (state (f-put-global 'fn-owner (cdr result) state))
             (state (fn-owner-install-effects (car result) state)))
        (value :ok)))))

(defun fn-owner-close (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn-owner-step (list :close id) state)))
    (value :closed)))

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
         (outcome (fn-own-observe-outcome (f-get-global 'fn-owner state) obs))
         (state (fn-owner-step (list :observe obs) state)))
    (value outcome)))

(defun fn-owner-declare-group (name-octets state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-store-text-octetsp name-octets))
      (value :invalid)
    (let* ((before (f-get-global 'fn-owner state))
           (state (fn-owner-step
                   (list :declare-group (fn-store-octets->string name-octets))
                   state)))
      (value (if (equal (f-get-global 'fn-owner state) before) :refused :declared)))))

(defun fn-owner-group-facts (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-replay-facts (fn-own-facts (f-get-global 'fn-owner state)))))

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
  (let ((state (fn-owner-step (list :feeds (f-get-global 'fn-store-cfg state))
                              state)))
    (value (fn-store-cfg-join-names
            (fn-own-feed-names (fn-own-feeds (f-get-global 'fn-owner state)))))))

(defun fn-owner-feed-peers (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-own-feed-names (fn-own-feeds (f-get-global 'fn-owner state))))))

(defun fn-owner-feed-record (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        nil
      (fn-own-feed-record-of peer (fn-own-feeds (f-get-global 'fn-owner state))))))

; Where to dial: the peer record's transport row, read by ACL2.  The host
; does not parse the configuration.
(defun fn-owner-feed-host (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((transport (fn-cfg-peer-transport (fn-owner-feed-record peer-octets state))))
    (value (if (and (consp transport) (equal (car transport) :nntp))
               (fn-record-string-octets (fn-cfg-ag-car (fn-cfg-ag-cdr transport)))
             nil))))

(defun fn-owner-feed-port (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((transport (fn-cfg-peer-transport (fn-owner-feed-record peer-octets state))))
    (value (if (and (consp transport) (equal (car transport) :nntp))
               (nfix (fn-cfg-ag-car (fn-cfg-ag-cdr (fn-cfg-ag-cdr transport))))
             0))))

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
                                           (f-get-global 'fn-owner state)))))
                 t
               nil)))))

(defun fn-owner-feed-queue-length (peer-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value 0)
      (value (len (fn-feed-queue
                   (fn-own-feed-find peer (fn-own-feeds
                                           (f-get-global 'fn-owner state)))))))))

; The host's socket identifier for one peer's outbound connection; nil when
; the socket is gone, which stops selection at once (fn-feed-selection wants
; a natural conn) and returns the in-flight entry at the next observation.
(defun fn-owner-feed-connect (peer-octets conn state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (let ((state (fn-owner-step (list :feed-conn peer conn) state)))
        (value :ok)))))

; The frames the host has to make durable, and the bytes they authorize.
; `fn-owner-feed-frames' is a list of encoded FNFD frames, each sealed with
; the constrained trailer (A-CRYPTO); the host writes them length-prefixed.
; `fn-feed-encode' takes the trailer as an argument, so these frames carry a
; ZERO trailer: tools/run_owner.py hashes the protected prefix and appends the
; real one (A-CRYPTO), exactly as tools/run_feed.py does.  The header, the
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

(defun fn-owner-feed-install-feed (records effects state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-owner-feed-records records state))
         (state (f-put-global 'fn-owner-feed-frames
                              (fn-owner-feed-encode-records records) state))
         (state (f-put-global 'fn-owner-feed-command
                              (fn-own-feed-effect-octets effects) state))
         (state (f-put-global 'fn-owner-feed-peer
                              (fn-own-feed-effect-peer effects) state)))
    state))

; One tick for one peer: the records first, then the bytes.
(defun fn-owner-feed-tick (peer-octets monotonic state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (let* ((owner (f-get-global 'fn-owner state))
             (obs (fn-clock-observation monotonic 0 0 nil))
             (records (fn-own-tick-peer-records owner peer obs))
             (result (fn-own-tick-peer owner peer obs))
             (state (f-put-global 'fn-owner (cdr result) state))
             (state (fn-owner-feed-install-feed records (car result) state)))
        (value (if (car result) :offer :idle))))))

; One reply line from one peer.
(defun fn-owner-feed-octets (peer-octets line monotonic state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (let* ((owner (f-get-global 'fn-owner state))
             (obs (fn-clock-observation monotonic 0 0 nil))
             (records (fn-own-feed-reply-records owner peer line))
             (result (fn-own-feed-reply owner peer line obs))
             (state (f-put-global 'fn-owner (cdr result) state))
             (state (fn-owner-feed-install-feed records (car result) state)))
        (value (if (car result) :send :quiet))))))

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

; Replay: one journal frame at a time, decoded and folded through the feed
; machine before any command is emitted.  The host supplies the digest it
; computed over the protected prefix; `fn-feed-decode' checks it.
(defun fn-owner-feed-entry-of-frame (frame digest)
  (declare (xargs :mode :program))
  (let ((decoded (fn-feed-decode frame digest)))
    (if (fn-frame-result-okp decoded)
        (fn-feed-journal-entry (fn-frame-result-kind decoded)
                               (fn-frame-result-payload decoded))
      nil)))

(defun fn-owner-feed-replay-frame (peer-octets frame digest state)
  (declare (xargs :stobjs state :mode :program))
  (let ((peer (fn-store-octets->string peer-octets))
        (entry (fn-owner-feed-entry-of-frame frame digest)))
    (if (or (equal peer :bad) (null entry))
        (value :bad)
      (let ((state (fn-owner-step (list :feed-replay peer (list entry)) state)))
        (value :ok)))))

; The fence a process death owes every feed: one (:feed-restart peer) record
; per peer, durable, then fn-feed-restart on each.  fn-own-reopen does the
; restart; this is the record side and the entry point a recovering host
; calls once, after the replay and before any command.
(defun fn-owner-feed-restart (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((owner (f-get-global 'fn-owner state))
         (records (fn-own-feed-restart-records (fn-own-feeds owner)))
         (state (f-put-global 'fn-owner
                              (fn-own-with-feeds
                               owner (fn-own-feed-restart-all (fn-own-feeds owner)))
                              state))
         (state (fn-owner-feed-install-feed records nil state)))
    (value (len records))))
