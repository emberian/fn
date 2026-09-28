; Checkpoint bridge: the host marshals octets; ACL2 captures, encodes, decodes,
; validates and restores.  Python computes only the SHA-256 trailer (A-CRYPTO)
; and slices the suffix by the sequence ACL2 returned; ACL2 revalidates that
; suffix in fn-checkpoint-restore.
(in-package "ACL2")
(include-book "../books/checkpoint-publish")
(include-book "../books/checkpoint-auxiliary")
(include-book "../books/store-reclaim-stream")
(include-book "../books/store-log-reclaim")
(include-book "../books/reclaim-instant")
;
; Loaded here, not left to a bridge's `ld' order: this file uses names
; host/store-node-host.lisp (and host/store-host.lisp under it) defines, so a session that loads this file alone
; must get them too.  A second `ld' of a file already in the session
; re-admits identical definitions, which ACL2 accepts as redundant.
(ld "store-node-host.lisp" :ld-error-action :error)

(defun fn-store-checkpoint-rollover-proposal (fresh-id state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cpa-rollover-proposal (f-get-global 'fn-store-sn state) fresh-id)))

(defun fn-store-checkpoint-clone-fence-name ()
  (declare (xargs :mode :program))
  *fn-cpa-clone-fence-name*)

(defun fn-store-checkpoint-clone-fence-read-bound ()
  (declare (xargs :mode :program))
  (fn-cpa-clone-fence-read-bound))

(defun fn-store-checkpoint-clone-max-depth ()
  (declare (xargs :mode :program))
  (fn-cpa-clone-max-depth))

(defun fn-store-checkpoint-clone-max-entries ()
  (declare (xargs :mode :program))
  (fn-cpa-clone-max-entries))

(defun fn-store-checkpoint-clone-max-bytes ()
  (declare (xargs :mode :program))
  (fn-cpa-clone-max-bytes))

(defun fn-store-checkpoint-clone-path-bound ()
  (declare (xargs :mode :program))
  (fn-cpa-clone-path-bound))

(defun fn-store-checkpoint-clone-input-pathp (path)
  (declare (xargs :mode :program))
  (fn-cpa-clone-input-pathp path))

(defun fn-store-checkpoint-clone-phase (marker-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp marker-octets)))
  (value (fn-cpa-clone-phase-of-octets
          (f-get-global 'fn-store-sn state) marker-octets)))

; The protected prefix of a checkpoint generation captured from the decoded
; durable records at the durable allocator frontier.  Capture replays the
; records in ACL2 (fn-checkpoint-capture); Python never sees the node.
;
; The allocation domain is the live node's, read with the same accessor the
; rest of the store host uses (fn-store-sn-domain).  `*fn-store-groups*' was
; deleted with the compiled group table in 4ba5599; these three sites still
; named it, so every Acl2Store bridge failed to load this file.
;
; Under the records flip the capture replays ROWS (the decoded events
; interned into a local arena, books/store-intern.lisp fn-intern-events), and
; a captured node holding an article would carry arena handles its frame does
; not resolve: such a capture is refused by name (:error :arena) until the
; checkpoint frame carries the arena's bytes (the same open item as the state
; checkpoint, host/store-node-host.lisp fn-store-sco-decode).
(defun fn-store-checkpoint-protected (octet-records frontier state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-octet-list-listp octet-records)))
  (let* ((decoded (fn-store-decode-records octet-records))
         (records (if (equal decoded :bad) :bad
                    (fn-store-intern-records-local decoded))))
    (if (equal records :bad)
        (value :bad)
      (if (fn-store-rows-hold-handles-p records)
          (value (list :error :arena))
      (let ((captured (fn-checkpoint-capture (fn-store-sn-domain state)
                                             (fn-store-sn-capacity state)
                                             records frontier)))
        (if (not (equal (car captured) :ok))
            (value captured)
          (value (fn-cpc-frame-protected
                  (fn-checkpoint-capture-value captured)))))))))

(defun fn-store-checkpoint-selection-protected (generation)
  (declare (xargs :mode :program))
  (fn-cpc-selection-protected generation))

(defun fn-store-checkpoint-selection-decode (octets digest)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-cpc-selection-decode octets digest))

; ACL2 owns the complete checkpoint directory vocabulary, its finite
; observation bound, canonical decimal parsing/rendering, and the sorted
; generation plan.  Hosts marshal directory-entry strings as UTF-8 octets.
(defun fn-store-checkpoint-generation-name-octets (generation)
  (declare (xargs :mode :program))
  (let ((chars (fn-cpp-generation-name-chars generation)))
    (if (equal chars :bad)
        :bad
      (fn-record-string-octets (coerce chars 'string)))))

(defun fn-store-checkpoint-selection-name-octets ()
  (declare (xargs :mode :program))
  (fn-record-string-octets (coerce *fn-cpp-selection-name* 'string)))

(defun fn-store-checkpoint-selection-read-bound ()
  (declare (xargs :mode :program))
  *fn-cpp-selection-read-bound*)

; D27, PRF-171: the retained-generation capacity is the opened profile's
; max-transactions plus one (`fn-cpp-generation-capacity'); VALUES is the
; profile the host opened the store under (`fnn-store-config').
(defun fn-store-checkpoint-generation-capacity (values)
  (declare (xargs :mode :program))
  (fn-cpp-generation-capacity (fn-bs-profile-max-transactions values)))

(defun fn-store-checkpoint-namespace-observation-limit (values)
  (declare (xargs :mode :program))
  (fn-cpp-namespace-observation-limit
   (fn-store-checkpoint-generation-capacity values)))

(defun fn-store-checkpoint-name-octets->chars (octets)
  (declare (xargs :mode :program))
  (if (fn-cbor-octet-listp octets)
      (coerce (fn-record-octets-string octets) 'list)
    :bad))

(defun fn-store-checkpoint-names-octets->chars (names)
  (declare (xargs :mode :program))
  (if (consp names)
      (let ((name (fn-store-checkpoint-name-octets->chars (car names))))
        (if (equal name :bad)
            :bad
          (let ((rest (fn-store-checkpoint-names-octets->chars (cdr names))))
            (if (equal rest :bad) :bad (cons name rest)))))
    (if (null names) nil :bad)))

(defun fn-store-checkpoint-namespace-plan (name-octets values)
  (declare (xargs :mode :program
                  :guard (fn-octet-list-listp name-octets)))
  (let ((names (fn-store-checkpoint-names-octets->chars name-octets)))
    (if (equal names :bad) '(:error :octets)
      (fn-cpp-namespace-plan names
                             (fn-store-checkpoint-generation-capacity values)))))

; The sorted generation plan is gap-checked here.  Exhaustion names both the
; finite retained-generation policy and the enclosing uint32 codec domain.
(defun fn-store-checkpoint-next-generation (generations values)
  (declare (xargs :mode :program))
  (fn-cpp-next-generation generations
                          (fn-store-checkpoint-generation-capacity values)))

;; `operator CONFIG store reclaim [--dry-run]' over the record log
;; (host/native/checkpoint.lisp `fnn-log-reclaim-steps'): the host folds
;; `fn-store-reclaim-step' (books/store-reclaim-stream.lisp's fn-rcls-step)
;; over the log's records under `fn-store-reclaim-context' from
;; `fn-store-reclaim-init', then asks `fn-store-log-reclaim-decide-stream'
;; with the same clock observation.  The rule is the configuration's; the
;; instant is the clock observation's stamp, derived as an article's stamp is
;; (`fn-record-stamp-of-observation').
(defun fn-store-reclaim-rule-and-stamp (clock state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((cfg (f-get-global 'fn-store-cfg state))
         (rule (fn-rcl-config-rule (fn-cfg-value cfg)))
         (stamp (fn-record-stamp-of-observation clock)))
    (mv rule (if (natp stamp) stamp nil))))

(defun fn-store-reclaim-context (clock state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (rule now) (fn-store-reclaim-rule-and-stamp clock state)
    (value (fn-rclp-ctx rule now (f-get-global 'fn-store-sn state)))))

(defun fn-store-reclaim-init ()
  (declare (xargs :mode :program))
  (fn-rcls-init))

(defun fn-store-reclaim-step (acc octets ctx)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-rcls-step acc octets ctx))

;; The streamed reclaim over the record log (books/store-log-reclaim.lisp
;; fn-lgr-decide-stream, over compact-arena's fold fn-rcls-*): one record's
;; rewrite, and the decision over the fold.
(defun fn-store-log-reclaim-event (octets ctx)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-rclp-event octets ctx))

(defun fn-store-log-reclaim-decide-stream (profile clock acc dry fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (mv-let (rule now) (fn-store-reclaim-rule-and-stamp clock state)
    (value (fn-lgr-decide-stream profile rule now (f-get-global 'fn-store-sn state) acc dry fn-arena))))

;; The reclaim's instant, recorded (books/reclaim-instant.lisp, PKT-857):
;; before a reclaim rewrites anything, the host publishes the configuration
;; record carrying the one delta `fn-rci-delta' of the SAME clock's stamp
;; (the stamp `fn-store-reclaim-rule-and-stamp' hands the context), built and
;; admitted by the configuration record path every administrative change
;; takes.  :ok leaves the octets in `fn-store-cfg-last-octets'; :refused the
;; reason in `fn-store-cfg-last-reason' (an unrepresentable instant is
;; :reclaim-instant).  KEYSTONE fn-rci-recorded-context-is-the-decided-context:
;; the configuration this record yields names the rule and instant the
;; decision used.
(defun fn-store-reclaim-instant-record (clock stamp state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (rule now) (fn-store-reclaim-rule-and-stamp clock state)
    (declare (ignore rule))
    (if (fn-rci-representablep now)
        (fn-store-cfg-peer-delta-record (list (fn-rci-delta now)) stamp state)
      (let ((state (f-put-global 'fn-store-cfg-last-reason :reclaim-instant state)))
        (value :refused)))))

;; `store reclaim --recorded': the context and the decision from the
;; configuration the store opened with -- its rule and its recorded instant
;; (fn-rci-context, fn-rci-decide-stream; refused :no-recorded-instant when no
;; reclaim was ever recorded).  KEYSTONE fn-rci-recorded-decision-is-the-
;; decision: over the record `store reclaim' published, this is the decision
;; it took at its clock.
(defun fn-store-reclaim-context-recorded (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-rci-context (fn-cfg-value (f-get-global 'fn-store-cfg state))
                         (f-get-global 'fn-store-sn state))))

(defun fn-store-log-reclaim-decide-recorded (profile acc dry fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-rci-decide-stream profile (fn-cfg-value (f-get-global 'fn-store-cfg state))
                               (f-get-global 'fn-store-sn state) acc dry fn-arena)))

(defun fn-store-checkpoint-publication-initial
  (generations proposed-generation exclusivep final-absentp values)
  (declare (xargs :mode :program))
  (fn-cpp-publication-initial generations proposed-generation exclusivep
                              final-absentp
                              (fn-store-checkpoint-generation-capacity values)))

; Selection replacement is a separate contract from immutable generation
; publication.  The native adapter retains this returned phase and asks ACL2
; for every next action, observation transition, and terminal outcome.
(defun fn-store-checkpoint-marker-action (phase)
  (declare (xargs :mode :program))
  (fn-cpp-marker-driver-action phase))

(defun fn-store-checkpoint-marker-step (phase result)
  (declare (xargs :mode :program))
  (fn-cpp-marker-driver-step phase result))

(defun fn-store-checkpoint-marker-outcome (phase)
  (declare (xargs :mode :program))
  (fn-cpp-marker-driver-outcome phase))

; Decode a selected generation against the live configuration and the
; observed durable frontier and record count.  The accepted checkpoint is
; installed for the restore call; the reply carries only its sequence and
; frontier so the host can slice the suffix ACL2 will revalidate.
(defun fn-store-checkpoint-decode (octets digest max-frontier max-sequence state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (let ((decoded (fn-cpc-frame-decode octets digest (fn-store-sn-domain state)
                                      (fn-store-sn-capacity state) max-frontier
                                      max-sequence)))
    (if (not (fn-cpc-result-okp decoded))
        (value decoded)
      (let* ((checkpoint (fn-cpc-result-value decoded))
             (state (f-put-global 'fn-store-checkpoint checkpoint state)))
        (value (list :ok (fn-checkpoint-sequence checkpoint)
                     (fn-checkpoint-frontier checkpoint)))))))

; Restore the installed checkpoint with the suffix records at the observed
; final frontier.  fn-checkpoint-restore is the proved subject
; (fn-checkpoint-plus-suffix-equals-full-replay); its result node is kept for
; the differential comparison below.
(defun fn-store-checkpoint-restore (octet-suffix frontier state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-octet-list-listp octet-suffix)))
  (let* ((decoded (fn-store-decode-records octet-suffix))
         (suffix (if (equal decoded :bad) :bad
                   (fn-store-intern-records-local decoded))))
    (if (equal suffix :bad)
        (value (list :error :suffix-octets))
      (if (fn-store-rows-hold-handles-p suffix)
          (value (list :error :arena))
      (let ((restored (fn-checkpoint-restore
                       (f-get-global 'fn-store-checkpoint state)
                       (fn-store-sn-domain state) (fn-store-sn-capacity state)
                       suffix frontier)))
        (if (not (equal (car restored) :ok))
            (value restored)
          (let ((state (f-put-global 'fn-store-checkpoint-node
                                     (car (cdr restored)) state)))
            (value :ok))))))))

; The differential test: the node restored from checkpoint plus suffix against
; the node the live composition rebuilt by full replay (fn-sn-open-observed).
; This is a comparison of two values ACL2 computed, not a production
; dependency; the host asserts on it only under its debug flag.
(defun fn-store-checkpoint-differential (state)
  (declare (xargs :stobjs state :mode :program))
  (value (if (equal (f-get-global 'fn-store-checkpoint-node state)
                    (fn-sn-node (f-get-global 'fn-store-sn state)))
             t
           nil)))

; The node-only checkpoint is not a complete Store image.  Compare the
; consumer, topic, derived index and historical authorship projections of the actual reopened
; Store with an independent replay of its exact journal records.  This runs
; once during selected-checkpoint diagnostics, never on a served request.
(defun fn-store-checkpoint-auxiliary-differential (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cpa-store-auxiliary-agrees
          (f-get-global 'fn-store-sn state))))
