; Experimental store bridge: physical observations drive the proved fn-sn core.
(in-package "ACL2")
(include-book "../books/store-observed")
(include-book "../books/store-node-resolution")

; This wrapper reuses the established decimal-octet boundary helpers from the
; store host. Python supplies only ordered filesystem observations.
(defun fn-store-sn-reset (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-store-sn
                             (fn-sn-initial *fn-store-groups*
                                            *fn-store-capacity*) state)))
    (value :ready)))

(defun fn-store-sn-state (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-store-sn state)))

; The bounded observed-image entry validates the decoded record list and
; frontier, constructs its own replaying kernel image, and invokes actual
; fn-sn-recover.  This wrapper installs only its tagged successful result.
(defun fn-store-sn-recover (octet-records frontier state)
  (declare (xargs :stobjs state :mode :program))
  (let ((records (fn-store-decode-records octet-records)))
    (if (equal records :bad)
        (value :fault)
      (let ((opened (fn-sn-open-observed *fn-store-groups*
                                         *fn-store-capacity* frontier records)))
        ; No barrier is fabricated here: Python must report each of five real
        ; fsync observations via fn-store-sn-io before this state is :ready.
        (if (and (fn-sn-open-okp opened)
                 (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                        :recovering))
            (let ((state (f-put-global 'fn-store-sn (fn-sn-open-state opened) state)))
              (value :recovering))
          (value :fault))))))

(defun fn-store-sn-io (operation result state)
  (declare (xargs :stobjs state :mode :program))
  (let ((next (fn-sn-io (f-get-global 'fn-store-sn state) operation result)))
    (let ((state (f-put-global 'fn-store-sn next state)))
      (value (fn-sf-phase (fn-sn-files next))))))

(defun fn-store-sn-prepare (msgid-octets payload group-codes id-octets
                             subject-octets evidence-octets charge state)
  (declare (xargs :stobjs state :mode :program))
  (let ((groups (fn-store-groups-from-codes group-codes))
        (s (f-get-global 'fn-store-sn state)))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (> (len payload) *fn-store-max-payload*)
            (equal groups :bad) (null groups)
            (not (fn-store-text-octetsp id-octets))
            (not (fn-store-text-octetsp subject-octets))
            (not (fn-store-text-octetsp evidence-octets)) (not (posp charge)))
        (value :invalid)
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
                  (value :prepared)))))))))

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
  (let ((groups (fn-store-groups-from-codes group-codes)))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (equal groups :bad) (null groups))
        (value :absent)
      (let ((action (fn-store-article-match
                     (fn-store-octets->string msgid-octets) payload groups
                     (fn-sn-node (f-get-global 'fn-store-sn state)))))
        (value (if action action :absent))))))

(defun fn-store-sn-group-next (code state)
  (declare (xargs :stobjs state :mode :program))
  (let ((group (fn-store-group-code code)))
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
