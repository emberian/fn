; Experimental store bridge: physical observations drive the proved fn-sn core.
; These program-mode wrappers are inside the adapter trust boundary. Callee
; guard verification is conditional on valid inputs/state; it does not prove
; that this wrapper establishes each precondition. Keep actual host/model
; correspondence and growing-history execution cost explicit when changing
; these entries. Do not add whole-store recognition per served operation.
(in-package "ACL2")
(include-book "../books/store-observed")
; D25: the duplicate-versus-conflict decision keys on the poster's bytes.
(include-book "../books/poster-bytes")
(include-book "../books/native-config-observation")
(include-book "../books/store-sweep")
(include-book "../books/store-node-resolution")
(include-book "../books/store-prepare-correspondence")
(include-book "../books/store-budget")
(include-book "../books/node-config")
(include-book "../books/native-admin")
; P3: open from an exact-state checkpoint.
(include-book "../books/store-checkpoint-open")
(include-book "../books/store-checkpoint-codec")
; fn-bs-scp-program: the checkpoint file name is its rename target.
(include-book "../books/byte-store-state-checkpoint-program")
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

; The operator's headroom for the replayed Store: (used budget
; reserved-charge charge-capacity), from PROFILE (the values ACL2 decoded
; from the store's metadata file at open) and the Store state this session
; carries.  `fn-sbud-used' is the committed record count
; (fn-sbud-used-names-the-transaction-namespace); the host counts nothing.
(defun fn-store-sn-publication-verdict (profile kind state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sbud-verdict profile kind (f-get-global 'fn-store-sn state))))

(defun fn-store-sn-headroom (profile state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-sbud-headroom profile (f-get-global 'fn-store-sn state))))

; The bounded observed-image entry validates the decoded record list and
; frontier, constructs its own replaying kernel image, and invokes actual
; fn-sn-recover.  This wrapper installs only its tagged successful result.
(defun fn-store-config-observation-limit ()
  ; The bounded physical scan uses the same ACL2-owned limit as its plan.
  *fn-nco-max-config-observations*)

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

(defun fn-store-config-observation (entries)
  "The recovery subject for one bounded physical config directory observation."
  (declare (xargs :mode :program))
  (let ((converted (fn-store-config-observation-entries entries)))
    (if (equal converted :bad)
        (fn-nco-result :fault :input nil)
      (fn-nco-observe converted))))

(defun fn-store-config-initial-observation (entries)
  "Initialization-only observation; an empty directory may receive genesis."
  (declare (xargs :mode :program))
  (let ((converted (fn-store-config-observation-entries entries)))
    (if (equal converted :bad)
        (fn-nco-result :fault :input nil)
      (fn-nco-observe-initial converted))))

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
      (if (fn-native-admin-candidate-openp records frontier config-records) t nil))))

(defun fn-store-cfg-native-admin-authorize
    (octet-records frontier config-octet-records record-octets lock-owned observed-name-octets)
  "The existing exact byte decoders feed one logical publication authorization.
The result binds the core's record generation, the ACL2 filename, candidate
reopen predicate, writer-lock observation and observed final namespace."
  (declare (xargs :mode :program))
  (let ((records (fn-store-decode-records octet-records))
        (config-records (fn-store-cfg-decode-records config-octet-records))
        (parsed (fn-cfg-decode-exact record-octets))
        (names (fn-store-octet-lists->strings observed-name-octets)))
    (if (or (equal records :bad) (equal config-records :bad) (null config-records)
            (equal names :bad) (not (fn-record-parse-okp parsed)))
        (fn-native-admin-publication-result :refused :decode nil nil nil)
      (fn-native-admin-publication-authorize
       records frontier config-records (fn-record-parse-value parsed)
       lock-owned names))))

; The physical configuration and Store histories share transaction IDs, but
; have independent sequence spaces. ACL2 interleaves them at recovery, with
; configuration before a tied Store event, and carries that history in the
; opened Store. The final configuration remains available for administration.
(defun fn-store-sn-recover (octet-records frontier config-octet-records state)
  (declare (xargs :stobjs state :mode :program))
  (let ((records (fn-store-decode-records octet-records))
        (config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (equal records :bad) (equal config-records :bad)
            (null config-records))
        (value :fault)
      (let ((replayed (fn-cpr-replay config-records records)))
        (if (not (equal (fn-replay-result-kind replayed) :ok))
            (value :fault)
          (let* ((cn (fn-replay-result-node replayed))
                 (cfg (fn-cnode-config cn))
                 (opened (fn-cpo-open-observed config-records frontier records)))
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
  (let ((state (f-put-global 'fn-store-sco-checkpoint nil state)))
    (value :cleared)))

; SEGMENTS: each segment's octets, in file order, as the host's range reads
; returned them (fnn-state-checkpoint-segments, host/native/checkpoint.lisp).
(defun fn-store-sco-decode (segments state)
  (declare (xargs :stobjs state :mode :program))
  (let ((decoded (fn-scc-decode-segments segments)))
    (if (and (consp decoded) (eq (car decoded) :ok) (consp (cdr decoded)))
        (let ((state (f-put-global 'fn-store-sco-checkpoint (cadr decoded) state)))
          (value (list :ok (fn-sco-sequence (cadr decoded)))))
      (let ((state (f-put-global 'fn-store-sco-checkpoint nil state)))
        (value (list :refused (if (and (consp decoded) (consp (cdr decoded)))
                                  (cadr decoded)
                                :malformed)))))))

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

; The committed record count the open observed: the selected pack's
; coverage LOWER, or one past the last ACL2-bound transaction sequence.
(defun fn-store-sco-observed-count (sequences lower)
  (declare (xargs :mode :program))
  (let ((last-sequence (car (last sequences))))
    (if (and (consp sequences) (natp last-sequence) (natp lower))
        (max lower (+ 1 last-sequence))
      (nfix lower))))

; The open's choice (fn-sco-select) under the profile's K.
(defun fn-store-sco-select (status sequence count profile)
  (declare (xargs :mode :program))
  (fn-sco-select status sequence count (fn-bs-profile-max-open-suffix profile)))

; How many of the ACL2-bound transaction sequences (ascending, from
; fn-store-txn-observation-selected) lie below S: the host drops exactly
; those and reads the rest.  A wrong split cannot open: fn-sco-open runs
; the history recognizer over the checkpoint's records and the suffix.
(defun fn-store-sco-covered-count (sequences s)
  (declare (xargs :mode :program))
  (if (and (consp sequences) (natp (car sequences)) (natp s) (< (car sequences) s))
      (+ 1 (fn-store-sco-covered-count (cdr sequences) s))
    0))

; The open from the decoded checkpoint and the suffix's octets.  It mirrors
; fn-store-sn-recover line for line; the keystone
; fn-sn-recover-from-checkpoint-equals-full-recover is about the fn-sco-open
; call below.
(defun fn-store-sn-recover-from-checkpoint (octet-records frontier config-octet-records state)
  (declare (xargs :stobjs state :mode :program))
  (let ((checkpoint (fn-store-sco-current state))
        (records (fn-store-decode-records octet-records))
        (config-records (fn-store-cfg-decode-records config-octet-records)))
    (if (or (null checkpoint) (equal records :bad) (equal config-records :bad)
            (null config-records))
        (value :fault)
      (let ((replayed (fn-sco-replay-result checkpoint config-records records)))
        (if (not (equal (fn-replay-result-kind replayed) :ok))
            (value :fault)
          (let* ((cn (fn-replay-result-node replayed))
                 (cfg (fn-cnode-config cn))
                 (opened (fn-sco-open checkpoint config-records frontier records)))
            (if (and (fn-sn-open-okp opened)
                     (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                            :recovering))
                (let* ((state (f-put-global 'fn-store-sn (fn-sn-open-state opened)
                                            state))
                       (state (f-put-global 'fn-store-cfg cfg state)))
                  (value :recovering))
              (value :fault))))))))

(defun fn-store-sco-encode-records (records)
  (declare (xargs :mode :program))
  (if (consp records)
      (cons (fn-rcon-store-event-encode (car records))
            (fn-store-sco-encode-records (cdr records)))
    nil))

; The covered prefix's record octets, for the callers of the host's open
; that take the whole record list (pack publication, compaction, the
; owner).  Each is the canonical encoding of a record the checkpoint holds
; (fn-rcon-store-event-encode-is-store-event-encode, books/records-concrete).
(defun fn-store-sco-prefix-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-store-sco-encode-records (fn-sco-records (fn-store-sco-current state)))))

; The next checkpoint's file octets from the recovered Store: the open's
; checkpoint extended over the records after it (fn-sco-extend), or, when
; the open replayed in full, the capture of the whole history.  The answer
; is (OCTETS S) or :unencodable.
(defun fn-store-sco-publish-octets (segment-octets state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((st (f-get-global 'fn-store-sn state))
         (records (fn-sf-records (fn-sn-files st)))
         (configs (fn-sn-config-history st))
         (old (fn-store-sco-current state))
         ; The open's checkpoint is extended only when it holds exactly the
         ; recovered history's first S records (a linear comparison);
         ; otherwise the whole history is captured.
         (next (if (and old (<= (fn-sco-sequence old) (len records))
                        (equal (fn-sco-records old)
                               (take (fn-sco-sequence old) records)))
                   (fn-sco-extend old configs (nthcdr (fn-sco-sequence old) records))
                 (fn-sco-capture configs records)))
         (octets (fn-scc-file-octets next segment-octets)))
    (if (equal octets :unencodable)
        (value :unencodable)
      (value (list octets (fn-sco-sequence next))))))

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
  ; fn-rcon-sn-io-is-sn-io (books/records-concrete): fn-sn-io with the
  ; concrete record dispatchers.
  (let ((next (fn-rcon-sn-io (f-get-global 'fn-store-sn state) operation result)))
    (let ((state (f-put-global 'fn-store-sn next state)))
      (value (fn-sf-phase (fn-sn-files next))))))

(defun fn-store-sn-prepare (msgid-octets payload group-codes id-octets
                             subject-octets evidence-octets charge observation state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (f-get-global 'fn-store-sn state))
         (groups (fn-store-groups-from-codes group-codes (fn-store-sn-domain state))))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (> (len payload) *fn-record-max-payload*)
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
      (let* ((msgid (fn-store-octets->string msgid-octets))
             (existing (fn-pb-existing-action msgid payload groups s)))
        (if existing
            (value existing)
          (let* ((record (fn-sn-article-record
                          s observation msgid payload groups
                          (fn-store-octets->string id-octets)
                          (fn-store-octets->string subject-octets)
                          (fn-store-octets->string evidence-octets)
                          charge))
                 ; The host-called prepare is the executable projection from
                 ; books/store-prepare-correspondence.  Its keystone
                 ; fn-spc-prepare-equals-specification-under-relation equates
                 ; this call to fn-sn-prepare for every state reachable from
                 ; successful observed open through the actual mutators.
                 (next (if (equal record :clock-unusable)
                           s
                         (fn-spc-prepare s record))))
            (if (equal record :clock-unusable)
                (value :clock-unusable)
              (if (equal next s)
                (value :refused)
                (let ((state (f-put-global 'fn-store-sn next state)))
                  (value :prepared)))))))))))

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

(defun fn-store-sn-pending-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((record (fn-sf-record-candidate
                 (fn-sn-files (f-get-global 'fn-store-sn state)))))
    ; fn-rcon-store-event-encode-is-store-event-encode (books/records-concrete).
    (value (if record (fn-rcon-store-event-encode record) nil))))

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
      (let ((action (fn-pb-existing-action
                     (fn-store-octets->string msgid-octets) payload groups
                     (f-get-global 'fn-store-sn state))))
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

; -----------------------------------------------------------------------------
; The served statement query (decision D21)
;
; THE HOST LINE THE ASSURANCE RULE ASKS FOR.  fn-store-sn-statement below
; calls fn-sn-statement-lookup (books/store-node.lisp) on the value of the
; 'fn-store-sn global, and that function reads the carried index and nothing
; else: it does not walk the store, does not re-parse an article and does not
; verify a signature.  What licenses reading the index instead of the lace
; projection is fn-sn-statement-lookup-is-the-lace-lookup
; (books/store-node-invariants.lisp).  Its hypothesis, fn-sn-indexedp, holds
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

(defun fn-store-sn-set-keyring (pairs state)
  (declare (xargs :stobjs state :mode :program))
  (let ((keyring (fn-store-sn-keyring-of-pairs pairs)))
    (if (or (equal keyring :bad) (not (fn-prin-keyringp keyring)))
        (value :invalid)
      (let ((state (f-put-global
                    'fn-store-sn
                    (fn-sn-set-keyring (f-get-global 'fn-store-sn state)
                                       keyring)
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
  (if (not (fn-store-msgid-octetsp msgid-octets))
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
; (fn-sn-equivocatorp-is-the-lace-equivocator), never an independent
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
