; Experimental store bridge: physical observations drive the proved fn-sn core.
(in-package "ACL2")
(include-book "../books/store-observed")
(include-book "../books/store-sweep")
(include-book "../books/store-node-resolution")
(include-book "../books/node-config")
;
; Loaded here, not left to a bridge's `ld' order: this file uses names
; host/store-host.lisp defines, so a session that loads this file alone
; must get them too.  A second `ld' of a file already in the session
; re-admits identical definitions, which ACL2 accepts as redundant.
(ld "store-host.lisp" :ld-error-action :error)

(include-book "../books/peer-config")
(include-book "../books/provenance-codec")

; This wrapper reuses the established decimal-octet boundary helpers from the
; store host. Python supplies only ordered filesystem observations.
(defun fn-store-sn-reset (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-store-sn
                             ; No compiled group table and no compiled
                             ; capacity: the domain is empty and the capacity
                             ; is zero until the configuration history is
                             ; replayed.  That is the fail-closed floor of
                             ; specs/reconfiguration.md section 1.6 -- a store
                             ; that has not been configured accepts nothing,
                             ; rather than accepting into a compiled-in
                             ; default (the last `*fn-store-capacity*' read
                             ; outside host/checkpoint-host.lisp).
                             (fn-sn-initial nil 0) state)))
    (value :ready)))

(defun fn-store-sn-state (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-store-sn state)))

; The bounded observed-image entry validates the decoded record list and
; frontier, constructs its own replaying kernel image, and invokes actual
; fn-sn-recover.  This wrapper installs only its tagged successful result.
(defun fn-store-cfg-decode-records (octet-records)
  ; Each durable configuration record decodes exactly, or the list is :bad.
  (declare (xargs :mode :program))
  (if (consp octet-records)
      (let ((parsed (fn-cfg-decode-exact (car octet-records))))
        (if (not (fn-record-parse-okp parsed))
            :bad
          (let ((rest (fn-store-cfg-decode-records (cdr octet-records))))
            (if (equal rest :bad) :bad (cons (fn-record-parse-value parsed) rest)))))
    (if (null octet-records) nil :bad)))

; The configuration history is replayed first (`fn-cnode-config-replay',
; books/node-config), and the node the article history is replayed into takes
; its allocation domain and its capacity from that configured node.  The
; configuration is then held beside the store state for admission and for
; the operator's reconfiguration requests.  Fail closed: an undecodable,
; out-of-order or inadmissible configuration record is a :fault at open.
(defun fn-store-sn-recover (octet-records frontier config-octet-records state)
  (declare (xargs :stobjs state :mode :program))
  (let ((records (fn-store-decode-records octet-records))
        (config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (equal records :bad) (equal config-records :bad)
            (null config-records))
        (value :fault)
      (let ((replayed (fn-cnode-config-replay config-records)))
        (if (not (equal (fn-replay-result-kind replayed) :ok))
            (value :fault)
          (let* ((cn (fn-replay-result-node replayed))
                 (cfg (fn-cnode-config cn))
                 (opened (fn-sn-open-observed (fn-cnode-domain cn)
                                              (fn-cfg-capacity (fn-cfg-value cfg))
                                              frontier records)))
            ; No barrier is fabricated here: Python must report each of five
            ; real fsync observations via fn-store-sn-io before this state is
            ; :ready.
            (if (and (fn-sn-open-okp opened)
                     (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                            :recovering))
                (let* ((state (f-put-global 'fn-store-sn (fn-sn-open-state opened)
                                            state))
                       (state (f-put-global 'fn-store-cfg cfg state)))
                  (value :recovering))
              (value :fault))))))))

(defun fn-store-sn-domain (state)
  ; The allocation domain the live node carries: every name ever created.
  (declare (xargs :stobjs state :mode :program))
  (fn-state-groups (fn-node-acceptance (fn-sn-node (f-get-global 'fn-store-sn state)))))

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
  ; group pattern selects the absent half.
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
                  (list ingroups (nfix in-max-octets) (nfix in-inflight)))
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

(defun fn-store-cfg-set-peer (name-octets path-octets host-octets port
                              in-groups-octets in-max-octets in-inflight
                              out-groups-octets out-streaming out-max-queue
                              out-backoff auth-kind auth-octets
                              monotonic wall state)
  (declare (xargs :stobjs state :mode :program))
  (let ((p (fn-store-cfg-peer-record
            name-octets path-octets host-octets port in-groups-octets
            in-max-octets in-inflight out-groups-octets out-streaming
            out-max-queue out-backoff auth-kind auth-octets)))
    (if (null p)
        (let ((state (f-put-global 'fn-store-cfg-last-reason :peer-record state)))
          (value :refused))
      (fn-store-cfg-peer-delta-record (list (fn-cfg-set-peer-delta p))
                                      monotonic wall state))))

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
; rendered by Python from a shape it guessed.
(defun fn-store-cfg-peer-name-list (rows)
  (declare (xargs :mode :program))
  (if (consp rows)
      (if (equal (fn-cfg-row-b (car rows)) "path-identity")
          (cons (fn-cfg-row-a (car rows)) (fn-store-cfg-peer-name-list (cdr rows)))
        (fn-store-cfg-peer-name-list (cdr rows)))
    nil))

(defun fn-store-cfg-peer-names (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-cfg-join-names
          (fn-store-cfg-peer-name-list
           (fn-cfg-peers (fn-cfg-value (f-get-global 'fn-store-cfg state)))))))

(defun fn-store-cfg-peer-rows-of (name-octets state)
  (declare (xargs :mode :program :stobjs state))
  (let ((name (fn-store-octets->string name-octets)))
    (if (equal name :bad)
        nil
      (fn-cfg-rows-with-key (fn-cfg-peers (fn-cfg-value (f-get-global 'fn-store-cfg state)))
                            name))))

(defun fn-store-cfg-peer-slot-text (name-octets slot-octets state)
  ; The text half of one row of a peer's group, as octets; nil when absent.
  (declare (xargs :stobjs state :mode :program))
  (let* ((slot (fn-store-octets->string slot-octets))
         (row (and (not (equal slot :bad))
                   (fn-cfg-peer-slot (fn-store-cfg-peer-rows-of name-octets state) slot))))
    (value (if row (fn-record-string-octets (fn-cfg-row-c row)) nil))))

(defun fn-store-cfg-peer-slot-nat (name-octets slot-octets state)
  ; The numeric half of one row, or -1 when the row is absent: the CLI never
  ; substitutes a default for a slot the record does not carry.
  (declare (xargs :stobjs state :mode :program))
  (let* ((slot (fn-store-octets->string slot-octets))
         (row (and (not (equal slot :bad))
                   (fn-cfg-peer-slot (fn-store-cfg-peer-rows-of name-octets state) slot))))
    (value (if row (fn-cfg-row-n row) -1))))

(defun fn-store-cfg-last-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-store-cfg-last-octets state)))

(defun fn-store-cfg-last-reason (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-store-cfg-last-reason state)))

(defun fn-store-sn-io (operation result state)
  (declare (xargs :stobjs state :mode :program))
  (let ((next (fn-sn-io (f-get-global 'fn-store-sn state) operation result)))
    (let ((state (f-put-global 'fn-store-sn next state)))
      (value (fn-sf-phase (fn-sn-files next))))))

(defun fn-store-sn-prepare (msgid-octets payload group-codes id-octets
                             subject-octets evidence-octets charge state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (f-get-global 'fn-store-sn state))
         (groups (fn-store-groups-from-codes group-codes (fn-store-sn-domain state))))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (> (len payload) *fn-store-max-payload*)
            (equal groups :bad) (null groups)
            (not (fn-store-text-octetsp id-octets))
            (not (fn-store-text-octetsp subject-octets))
            (not (fn-store-text-octetsp evidence-octets)) (not (posp charge)))
        (value :invalid)
      ; A name in the domain but not served at the live generation (a retired
      ; group) is a refusal, decided by the same predicate fn-cnode-prepare
      ; applies (books/node-config).
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
                 (next (fn-sn-prepare s record)))
            (if (equal next s)
                (value :refused)
                (let ((state (f-put-global 'fn-store-sn next state)))
                  (value :prepared))))))))))

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

(defun fn-store-sn-pending-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((record (fn-sf-record-candidate
                 (fn-sn-files (f-get-global 'fn-store-sn state)))))
    (value (if record (fn-record-encode record) nil))))

(defun fn-store-sn-finish (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (f-get-global 'fn-store-sn state))
         (before-files (fn-sn-files before))
         (next (fn-sn-finish before))
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

(defun fn-store-sn-existing-action (msgid-octets payload group-codes state)
  (declare (xargs :stobjs state :mode :program))
  (let ((groups (fn-store-groups-from-codes group-codes (fn-store-sn-domain state))))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (equal groups :bad) (null groups))
        (value :absent)
      (let ((action (fn-store-article-match
                     (fn-store-octets->string msgid-octets) payload groups
                     (fn-sn-node (f-get-global 'fn-store-sn state)))))
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
  (value (len (fn-retain-pins
               (fn-node-retention
                (fn-sn-node (f-get-global 'fn-store-sn state)))))))

(defun fn-store-sn-reserved (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-retain-reserved
          (fn-node-retention
           (fn-sn-node (f-get-global 'fn-store-sn state))))))

(defun fn-store-sn-lookup (msgid-octets state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-store-msgid-octetsp msgid-octets))
      (value nil)
    (let ((article (fn-find-article
                    (fn-store-octets->string msgid-octets)
                    (fn-state-articles
                     (fn-node-acceptance
                      (fn-sn-node (f-get-global 'fn-store-sn state)))))))
      (value (if article (fn-article-payload article) nil)))))

(defun fn-store-sn-lookup-foundp (msgid-octets state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-store-msgid-octetsp msgid-octets))
      (value nil)
    (value (if (fn-find-article
                (fn-store-octets->string msgid-octets)
                (fn-state-articles
                 (fn-node-acceptance
                  (fn-sn-node (f-get-global 'fn-store-sn state)))))
               t nil))))

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
  ; The provenance of an article this node injected: the principal is the
  ; node's configured <path-identity> (books/path.lisp syntax, the same slot
  ; `fn-peer-local-identity' reads) and the generation is the configuration
  ; generation the acceptance is made under.  ACL2 also decides which FORM
  ; goes to the store: the canonical wire when the record fits the record
  ; grammar's evidence field, and otherwise the legacy rendering, so the
  ; host can never hand the store a value the grammar refuses.
  (declare (xargs :stobjs state :mode :program))
  (let* ((cfg (f-get-global 'fn-store-cfg state))
         (identity (fn-cfg-policy (fn-cfg-value cfg) "path-identity"))
         ; An unset "path-identity" policy reads as the empty string; a
         ; provenance never names an empty principal, so ACL2 substitutes
         ; the one honest word for "this node, unidentified".
         (principal (if (and (stringp identity) (not (equal identity "")))
                        identity
                      "local"))
         (p (fn-prov-make-post principal (fn-cfg-generation cfg))))
    (value (fn-record-string-octets
            (if (fn-prov-durablep p) (fn-prov-wire p) (fn-prov-render p))))))

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
  ; pin has been released.
  (declare (xargs :stobjs state :mode :program))
  (let* ((node (fn-sn-node (f-get-global 'fn-store-sn state)))
         (msgid (fn-store-octets->string msgid-octets))
         (binding (and (not (equal msgid :bad))
                       (fn-node-find-binding msgid (fn-node-bindings node))))
         (pin (and binding
                   (fn-retain-find-id (fn-node-binding-id binding)
                                      (fn-retain-pins (fn-node-retention node))))))
    (value (if pin
               (let ((ev (fn-retain-obligation-evidence pin)))
                 (fn-record-string-octets
                  (fn-prov-describe (if (stringp ev) (fn-prov-of-wire ev) ev))))
             nil))))
