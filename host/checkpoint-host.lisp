; Checkpoint bridge: the host marshals octets; ACL2 captures, encodes, decodes,
; validates and restores.  Python computes only the SHA-256 trailer (A-CRYPTO)
; and slices the suffix by the sequence ACL2 returned; ACL2 revalidates that
; suffix in fn-checkpoint-restore.
(in-package "ACL2")
(include-book "../books/checkpoint-publish")
(include-book "../books/checkpoint-compaction")
(include-book "../books/checkpoint-auxiliary")
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

(defun fn-store-checkpoint-clone-phase (marker-octets state)
  (declare (xargs :stobjs state :mode :program))
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
(defun fn-store-checkpoint-protected (octet-records frontier state)
  (declare (xargs :stobjs state :mode :program))
  (let ((records (fn-store-decode-records octet-records)))
    (if (equal records :bad)
        (value :bad)
      (let ((captured (fn-checkpoint-capture (fn-store-sn-domain state)
                                             *fn-store-capacity*
                                             records frontier)))
        (if (not (equal (car captured) :ok))
            (value captured)
          (value (fn-cpc-frame-protected
                  (fn-checkpoint-capture-value captured))))))))

(defun fn-store-checkpoint-selection-protected (generation)
  (declare (xargs :mode :program))
  (fn-cpc-selection-protected generation))

(defun fn-store-checkpoint-selection-decode (octets digest)
  (declare (xargs :mode :program))
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

(defun fn-store-checkpoint-namespace-observation-limit ()
  (declare (xargs :mode :program))
  *fn-cpp-namespace-observation-limit*)

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

(defun fn-store-checkpoint-namespace-plan (name-octets)
  (declare (xargs :mode :program))
  (let ((names (fn-store-checkpoint-names-octets->chars name-octets)))
    (if (equal names :bad) '(:error :octets)
      (fn-cpp-namespace-plan names))))

; The sorted generation plan is gap-checked here.  Exhaustion names both the
; finite retained-generation policy and the enclosing uint32 codec domain.
(defun fn-store-checkpoint-next-generation (generations)
  (declare (xargs :mode :program))
  (fn-cpp-next-generation generations))

; Native compaction/recovery boundary.  The returned octet records are the
; exact prefix held by the selected summary followed by the observed suffix;
; the native host does not interpret, merge or recreate any transaction fact.
(defun fn-store-checkpoint-compaction-capture (octet-records frontier)
  (declare (xargs :mode :program))
  (let ((captured (fn-cc-capture octet-records frontier)))
    (if (not (equal (car captured) :ok)) captured
      (list :ok (fn-cc-encode (car (cdr captured)))))))

(defun fn-store-checkpoint-compaction-expand (summary-octets octet-suffix frontier)
  (declare (xargs :mode :program))
  (let ((decoded (fn-cc-decode-exact summary-octets)))
    (if (not (equal (car decoded) :ok)) decoded
      (fn-cc-expand (car (cdr decoded)) octet-suffix frontier))))

(defun fn-store-checkpoint-compaction-open (framed digest octet-suffix frontier)
  (declare (xargs :mode :program))
  (if (or (not (fn-cbor-octet-listp framed))
          (< (len framed) *fn-frame-trailer-octets*))
      '(:error :frame)
    (let* ((n (- (len framed) *fn-frame-trailer-octets*))
           (payload (take n framed))
           (trailer (nthcdr n framed)))
      (if (not (equal trailer digest)) '(:error :integrity)
        (fn-store-checkpoint-compaction-expand payload octet-suffix frontier)))))

(defun fn-store-checkpoint-compaction-max-octets ()
  (declare (xargs :mode :program))
  *fn-cc-max-octets*)

(defun fn-store-checkpoint-compaction-observe (framed digest observed frontier)
  (declare (xargs :mode :program))
  (if (or (not (fn-cbor-octet-listp framed))
          (< (len framed) *fn-frame-trailer-octets*))
      '(:error :frame)
    (let* ((n (- (len framed) *fn-frame-trailer-octets*))
           (payload (take n framed))
           (trailer (nthcdr n framed))
           (decoded (and (equal trailer digest) (fn-cc-decode-exact payload))))
      (if (or (not (consp decoded)) (not (equal (car decoded) :ok)))
          '(:error :integrity)
        (let* ((summary (cadr decoded))
               (answer (fn-cc-recover-observation summary observed frontier)))
          answer)))))

; Inspect the selected authority before the host slices its bounded physical
; observation.  ACL2 returns the only accepted coverage boundary.
(defun fn-store-checkpoint-compaction-coverage (framed digest observed-count frontier)
  (declare (xargs :mode :program))
  (if (or (not (fn-cbor-octet-listp framed))
          (< (len framed) *fn-frame-trailer-octets*))
      '(:error :frame)
    (let* ((n (- (len framed) *fn-frame-trailer-octets*))
           (payload (take n framed))
           (trailer (nthcdr n framed))
           (decoded (and (equal trailer digest) (fn-cc-decode-exact payload))))
      (if (or (not (consp decoded)) (not (equal (car decoded) :ok)))
          '(:error :integrity)
        (let ((summary (car (cdr decoded))))
          (if (or (< observed-count (fn-cc-sequence summary))
                  (< frontier (fn-cc-frontier summary)))
              '(:error :coverage)
            (list :ok (fn-cc-sequence summary)
                  (fn-cc-frontier summary))))))))

(defun fn-store-checkpoint-publication-initial
  (generations proposed-generation exclusivep final-absentp)
  (declare (xargs :mode :program))
  (fn-cpp-publication-initial generations proposed-generation exclusivep
                              final-absentp))

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
  (declare (xargs :stobjs state :mode :program))
  (let ((decoded (fn-cpc-frame-decode octets digest (fn-store-sn-domain state)
                                      *fn-store-capacity* max-frontier
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
  (declare (xargs :stobjs state :mode :program))
  (let ((suffix (fn-store-decode-records octet-suffix)))
    (if (equal suffix :bad)
        (value (list :error :suffix-octets))
      (let ((restored (fn-checkpoint-restore
                       (f-get-global 'fn-store-checkpoint state)
                       (fn-store-sn-domain state) *fn-store-capacity*
                       suffix frontier)))
        (if (not (equal (car restored) :ok))
            (value restored)
          (let ((state (f-put-global 'fn-store-checkpoint-node
                                     (car (cdr restored)) state)))
            (value :ok)))))))

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
; consumer and historical authorship projections of the actual reopened
; Store with an independent replay of its exact journal records.  This runs
; once during selected-checkpoint diagnostics, never on a served request.
(defun fn-store-checkpoint-auxiliary-differential (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cpa-store-auxiliary-agrees
          (f-get-global 'fn-store-sn state))))
