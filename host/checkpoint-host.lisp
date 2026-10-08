; Checkpoint host entries: the clone-fence and rollover constants and
; decisions host/native/checkpoint.lisp asks ACL2 (fn-cpa-*), and the offline
; `operator ... store reclaim' folds over the record log.  The generation
; checkpoint wrappers (capture, decode, restore, the differentials, the
; directory-observation plan) had no caller once the Python Acl2Store bridge
; was retired and are gone (S117); their books remain as the representation
; checks.
(in-package "ACL2")
(include-book "../books/checkpoint-publish")
(include-book "../books/checkpoint-auxiliary")
(include-book "../books/store-reclaim-stream")
(include-book "../books/store-log-reclaim")
(include-book "../books/reclaim-instant")
(include-book "../books/expiry-instant")
; The sibling edge is an include-book, the discipline the account-*/index-*
; host books already follow for owner-host: certify-book refuses an `ld'
; (LD-FN is not an embedded event form), so a host file that carries one
; has never certified.  store-host comes with store-node-host's own
; include of it.  In a session that ld'd the sibling earlier the include
; is redundant and loads nothing.
(include-book "store-node-host")

(defun fn-store-checkpoint-rollover-proposal (fresh-id state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cpa-rollover-proposal (f-get-global 'fn-store-sn state) fresh-id)))

(definterface fn-store-checkpoint-rollover-proposal
  :class ::program)

(defun fn-store-checkpoint-clone-fence-name ()
  (declare (xargs :mode :program))
  *fn-cpa-clone-fence-name*)

(definterface fn-store-checkpoint-clone-fence-name
  :class ::program)

(defun fn-store-checkpoint-clone-fence-read-bound ()
  (declare (xargs :mode :program))
  (fn-cpa-clone-fence-read-bound))

(definterface fn-store-checkpoint-clone-fence-read-bound
  :class ::program)

(defun fn-store-checkpoint-clone-max-depth ()
  (declare (xargs :mode :program))
  (fn-cpa-clone-max-depth))

(definterface fn-store-checkpoint-clone-max-depth
  :class ::program)

(defun fn-store-checkpoint-clone-max-entries ()
  (declare (xargs :mode :program))
  (fn-cpa-clone-max-entries))

(definterface fn-store-checkpoint-clone-max-entries
  :class ::program)

(defun fn-store-checkpoint-clone-max-bytes ()
  (declare (xargs :mode :program))
  (fn-cpa-clone-max-bytes))

(definterface fn-store-checkpoint-clone-max-bytes
  :class ::program)

(defun fn-store-checkpoint-clone-path-bound ()
  (declare (xargs :mode :program))
  (fn-cpa-clone-path-bound))

(definterface fn-store-checkpoint-clone-path-bound
  :class ::program)

(defun fn-store-checkpoint-clone-input-pathp (path)
  (declare (xargs :mode :program))
  (fn-cpa-clone-input-pathp path))

(definterface fn-store-checkpoint-clone-input-pathp
  :class ::program)

(defun fn-store-checkpoint-clone-phase (marker-octets state)
  (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp marker-octets)))
  (value (fn-cpa-clone-phase-of-octets
          (f-get-global 'fn-store-sn state) marker-octets)))

(definterface fn-store-checkpoint-clone-phase
  :class ::program
  :kinds ((marker-octets fn-cbor-octet-listp)))

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

; The context carries the Message-IDs the operator's expiry policy expires
; at the same instant (books/expiry.lisp fn-xpy-ctx; Q14): the configuration's
; quota rows, the Store's articles and their payload headers in the arena.
(defun fn-store-reclaim-context (clock fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (mv-let (rule now) (fn-store-reclaim-rule-and-stamp clock state)
    (value (fn-xpy-ctx rule now (f-get-global 'fn-store-sn state)
                       (fn-cfg-value (f-get-global 'fn-store-cfg state)) fn-arena))))

(definterface fn-store-reclaim-context
  :class ::program)

;; The classes the verb reports before it rewrites (books/expiry.lisp
;; fn-xpy-ctx-classes, KEYSTONE fn-xpy-classes-partition-the-articles):
;; (reclaimable expired held reclaimed signed kept) over the context.
(defun fn-store-reclaim-ctx-classes (ctx fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-xpy-ctx-classes ctx fn-arena)))

(definterface fn-store-reclaim-ctx-classes
  :class ::program)

(defun fn-store-reclaim-init ()
  (declare (xargs :mode :program))
  (fn-rcls-init))

(definterface fn-store-reclaim-init
  :class ::program)

(defun fn-store-reclaim-step (acc octets ctx)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-rcls-step acc octets ctx))

(definterface fn-store-reclaim-step
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

;; The streamed reclaim over the record log (books/store-log-reclaim.lisp
;; fn-lgr-decide-stream, over compact-arena's fold fn-rcls-*): one record's
;; rewrite, and the decision over the fold.
(defun fn-store-log-reclaim-event (octets ctx)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-rclp-event octets ctx))

(definterface fn-store-log-reclaim-event
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-store-log-reclaim-decide-stream (profile clock acc dry fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (mv-let (rule now) (fn-store-reclaim-rule-and-stamp clock state)
    (value (fn-lgr-decide-stream profile rule now (f-get-global 'fn-store-sn state) acc dry fn-arena))))

(definterface fn-store-log-reclaim-decide-stream
  :class ::program)

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

(definterface fn-store-reclaim-instant-record
  :class ::program)

;; `store reclaim --recorded': the context and the decision from the
;; configuration the store opened with -- its rule and its recorded instant
;; (fn-rci-context, fn-rci-decide-stream; refused :no-recorded-instant when no
;; reclaim was ever recorded).  KEYSTONE fn-rci-recorded-decision-is-the-
;; decision: over the record `store reclaim' published, this is the decision
;; it took at its clock.
(defun fn-store-reclaim-context-recorded (fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-xpy-rci-context (fn-cfg-value (f-get-global 'fn-store-cfg state))
                             (f-get-global 'fn-store-sn state) fn-arena)))

(definterface fn-store-reclaim-context-recorded
  :class ::program)

(defun fn-store-log-reclaim-decide-recorded (profile acc dry fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-rci-decide-stream profile (fn-cfg-value (f-get-global 'fn-store-cfg state))
                               (f-get-global 'fn-store-sn state) acc dry fn-arena)))

(definterface fn-store-log-reclaim-decide-recorded
  :class ::program)
