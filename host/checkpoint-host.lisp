; Checkpoint bridge: the host marshals octets; ACL2 captures, encodes, decodes,
; validates and restores.  Python computes only the SHA-256 trailer (A-CRYPTO)
; and slices the suffix by the sequence ACL2 returned; ACL2 revalidates that
; suffix in fn-checkpoint-restore.
(in-package "ACL2")
(include-book "../books/checkpoint-publish")
;
; Loaded here, not left to a bridge's `ld' order: this file uses names
; host/store-node-host.lisp (and host/store-host.lisp under it) defines, so a session that loads this file alone
; must get them too.  A second `ld' of a file already in the session
; re-admits identical definitions, which ACL2 accepts as redundant.
(ld "store-node-host.lisp" :ld-error-action :error)

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

; The native adapter parses only the bounded filename grammar.  ACL2 owns the
; namespace decision: ascending generation numbers must be gap-free from zero,
; and the uint32 successor has a distinct exhaustion result.
(defun fn-store-checkpoint-next-generation (generations)
  (declare (xargs :mode :program))
  (fn-cpp-next-generation generations))

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
