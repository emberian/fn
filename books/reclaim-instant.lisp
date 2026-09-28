; fn: the reclaim's instant, recorded (lane log-leftovers, 2026-09-27;
; PKT-857, N2 of lane proto-determinism; planning/evidence/
; log-leftovers-reclaim-2026-09-27.md).
;
; `store reclaim' rewrites every article record its context releases into
; the record's tombstone (books/store-log-reclaim.lisp).  Under the rule
; `release-after DAYS' the context reads the clock (NOW, whole seconds of
; the wall reading, books/records-stamp.lisp fn-record-stamp-of-observation),
; and until this book that reading was recorded nowhere: the rewritten
; history was a function of the pre-reclaim history AND a value no replay
; could see.
;
; The instant is now a configuration row, recorded before the rewrite.  The
; retention rule is two `:set-limit' rows (books/reclaim-rule.lisp); the
; instant is a third, "retention-reclaim-at", published by the ordinary
; configuration record (host/native/checkpoint.lisp fnn-log-reclaim-steps,
; through the administrative authorization, publication and read-back of
; host/native/admin.lisp) before the rewritten history's checkpoint.  The
; configuration history is the store's other durable half: the open replays
; it (books/config.lisp fn-cfg-apply-record), it survives the drop that
; unlinks the covered log segments, and a copy of the store carries it.
;
; Why a configuration row and not a new record-log event kind: every
; existing reader refuses a log record it cannot decode (books/store-
; recover-stream.lisp fn-srs-decode answers :bad and the open faults), so a
; new kind would be a store-format change under D34; a `:set-limit' row
; whose slot no reader names is admitted by every existing image
; (fn-cfg-limit-ceiling is the CBOR maximum for any slot it does not list)
; and read by none, so this is no format change.
;
; The row's value is CODE = NOW + 1, or 0 when the clock had no usable wall
; reading (the context's NOW is then nil and `release-after' permits
; nothing).  KEYSTONES:
;   fn-rci-recorded-context-is-the-decided-context: the configuration the
;     published record yields names the same rule and the same NOW, so the
;     context a replay derives from it (fn-rci-context) is the context the
;     host decided under;
;   fn-rci-recorded-decision-is-the-decision: the decision over the recorded
;     configuration (fn-rci-decide-stream, which `store reclaim --recorded'
;     calls) is the decision `store reclaim' took at the clock, so a copy of
;     the pre-reclaim store given the record reclaims exactly as the store
;     did.
(in-package "ACL2")
(include-book "store-log-reclaim")
(include-book "reclaim-rule")

(defconst *fn-rci-slot* "retention-reclaim-at")

(defun fn-rci-code (now)
  (declare (xargs :guard t))
  (if (natp now) (+ 1 now) 0))

; The instants the row represents: no wall reading, or a stamp whose code is
; a uint32 (the delta's N field).
(defun fn-rci-representablep (now)
  (declare (xargs :guard t))
  (or (null now)
      (and (natp now) (fn-record-uint32p (+ 1 now)))))

; The instants the host's context carries (host/checkpoint-host.lisp
; fn-store-reclaim-rule-and-stamp: the stamp when it is a natural, else nil).
(defun fn-rci-instantp (now)
  (declare (xargs :guard t))
  (or (null now) (natp now)))

(defun fn-rci-delta (now)
  (declare (xargs :guard t))
  (fn-cfg-set-limit *fn-rci-slot* (fn-rci-code now)))

(defun fn-rci-recordedp (v)
  (declare (xargs :guard t))
  (if (fn-rcl-limit-row (fn-cfg-limits v) *fn-rci-slot*) t nil))

(defun fn-rci-config-now (v)
  (declare (xargs :guard t))
  (let ((n (fn-cfg-row-n (fn-rcl-limit-row (fn-cfg-limits v) *fn-rci-slot*))))
    (if (posp n) (1- n) nil)))

; The context a replay derives from a configuration value and the store.
(defun fn-rci-context (v s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-rclp-ctx (fn-rcl-config-rule v) (fn-rci-config-now v) s))

; The decision over the recorded configuration: `store reclaim --recorded'
; (host/checkpoint-host.lisp fn-store-log-reclaim-decide-recorded).  With no
; recorded instant it is refused by name.
(defun fn-rci-decide-stream (profile v s acc dry fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (fn-rci-recordedp v)
      (fn-lgr-decide-stream profile (fn-rcl-config-rule v) (fn-rci-config-now v)
                            s acc dry fn-arena)
    (list :refused :no-recorded-instant)))

; -----------------------------------------------------------------------------
; Lookup after the row's upsert (books/reclaim-rule.lisp keeps its own local).

(local
 (defthm fn-rci-limit-row-of-upsert-same
   (implies (and (equal (fn-cfg-row-a row) slot)
                 (equal (fn-cfg-row-b row) ""))
            (equal (fn-rcl-limit-row (fn-cfg-row-upsert rows row) slot) row))
   :hints (("Goal" :induct (fn-cfg-row-upsert rows row)
            :in-theory (enable fn-cfg-row-upsert)))))

(local
 (defthm fn-rci-limit-row-of-upsert-other
   (implies (not (equal (fn-cfg-row-a row) slot))
            (equal (fn-rcl-limit-row (fn-cfg-row-upsert rows row) slot)
                   (fn-rcl-limit-row rows slot)))
   :hints (("Goal" :induct (fn-cfg-row-upsert rows row)
            :in-theory (enable fn-cfg-row-upsert)))))

(local
 (defthm fn-rci-limits-of-set-limit
   (equal (fn-cfg-limits (fn-cfg-apply-delta v gen stamp
                                             (list :set-limit slot "" n nil)))
          (fn-cfg-row-upsert (fn-cfg-limits v) (fn-cfg-row-make slot "" "" n)))
   :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-delta-kind fn-cfg-delta-a
                                      fn-cfg-delta-b fn-cfg-delta-n fn-cfg-delta-rows
                                      fn-cfg-ag-car fn-cfg-ag-cdr)))))

(local
 (defthm fn-rci-value-of-apply-record
   (equal (fn-cfg-value (fn-cfg-apply-record cfg (fn-cfg-record-make q tx g change stamp)))
          (fn-cfg-apply (fn-cfg-value cfg) g stamp change))
   :hints (("Goal" :in-theory (enable fn-cfg-apply-record fn-cfg-value fn-cfg-make
                                      fn-cfg-ag-car fn-cfg-ag-cdr)))))

(local
 (defthm fn-rci-limits-of-the-record
   (equal (fn-cfg-limits (fn-cfg-apply v g stamp (list (fn-rci-delta now))))
          (fn-cfg-row-upsert (fn-cfg-limits v)
                             (fn-cfg-row-make *fn-rci-slot* "" "" (fn-rci-code now))))
   :hints (("Goal" :in-theory (enable fn-cfg-apply fn-cfg-set-limit fn-cfg-delta-make)))))

(local (in-theory (disable fn-cfg-apply-delta fn-cfg-apply fn-cfg-apply-record
                           fn-cfg-set-limit fn-cfg-limits fn-cfg-row-upsert
                           fn-cfg-value fn-cfg-record-make fn-rci-delta (:e fn-rci-delta))))

; The configuration the published record yields: the record the host builds
; (host/store-node-host.lisp fn-store-cfg-peer-delta-record over the one
; delta fn-rci-delta, called from host/checkpoint-host.lisp
; fn-store-reclaim-instant-record) applied as every open applies it.
(defun fn-rci-recorded-config (cfg q tx g stamp now)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cfg-apply-record cfg (fn-cfg-record-make q tx g (list (fn-rci-delta now)) stamp)))

; The row reads back: recorded, at NOW; the retention rule's two rows are
; untouched.
(defthm fn-rci-recorded-instant-reads-back
  (implies (fn-rci-instantp now)
           (let ((v (fn-cfg-value (fn-rci-recorded-config cfg q tx g stamp now))))
             (and (fn-rci-recordedp v)
                  (equal (fn-rci-config-now v) now)
                  (equal (fn-rcl-config-rule v) (fn-rcl-config-rule (fn-cfg-value cfg))))))
  :hints (("Goal" :in-theory (e/d (fn-rcl-config-rule fn-cfg-row-n fn-cfg-row-make
                                   fn-cfg-row-a fn-cfg-row-b fn-cfg-ag-car fn-cfg-ag-cdr
                                   fn-record-uint32p)
                                  (fn-rci-delta (:e fn-rci-delta))))))

; KEYSTONE.  The context a replay derives from the recorded configuration is
; the context the host decided under (host/checkpoint-host.lisp
; fn-store-reclaim-context: RULE the configuration's, NOW the clock's stamp).
(defthm fn-rci-recorded-context-is-the-decided-context
  (implies (fn-rci-instantp now)
           (equal (fn-rci-context (fn-cfg-value (fn-rci-recorded-config cfg q tx g stamp now)) s)
                  (fn-rclp-ctx (fn-rcl-config-rule (fn-cfg-value cfg)) now s)))
  :hints (("Goal" :in-theory (disable fn-rci-recorded-config fn-rclp-ctx fn-rcl-config-rule
                                      fn-rci-config-now fn-rci-recordedp)
           :use fn-rci-recorded-instant-reads-back)))

; KEYSTONE.  The decision over the recorded configuration
; (fn-rci-decide-stream: `store reclaim --recorded', host/checkpoint-host.lisp
; fn-store-log-reclaim-decide-recorded, called by host/native/checkpoint.lisp
; fnn-log-reclaim-steps) is the decision `store reclaim' took at the clock
; (fn-lgr-decide-stream at RULE and NOW: fn-store-log-reclaim-decide-stream),
; over the same store and fold.  With fn-lgr-decide-stream-is-lgr-decide and
; fn-lgr-decide-checkpoints-the-rewrite, the rewritten history a replay
; derives from the pre-reclaim history and the record is the one the host
; checkpointed.
(defthm fn-rci-recorded-decision-is-the-decision
  (implies (fn-rci-instantp now)
           (equal (fn-rci-decide-stream profile
                                        (fn-cfg-value (fn-rci-recorded-config cfg q tx g stamp now))
                                        s acc dry fn-arena)
                  (fn-lgr-decide-stream profile (fn-rcl-config-rule (fn-cfg-value cfg)) now
                                        s acc dry fn-arena)))
  :hints (("Goal" :in-theory (disable fn-rci-recorded-config fn-lgr-decide-stream
                                      fn-rcl-config-rule fn-rci-config-now fn-rci-recordedp)
           :use fn-rci-recorded-instant-reads-back)))

; A configuration with no recorded instant reclaims nothing on --recorded:
; it is refused by name.
(defthm fn-rci-unrecorded-is-refused-by-definition
  (implies (not (fn-rci-recordedp v))
           (equal (fn-rci-decide-stream profile v s acc dry fn-arena)
                  (list :refused :no-recorded-instant))))

; The delta the host stages is a configuration delta (so the record passes
; the configuration's own admission, fn-cfg-delta-listp).
(defthm fn-rci-delta-is-a-delta
  (implies (fn-rci-representablep now)
           (fn-cfg-delta-listp (list (fn-rci-delta now))))
  :hints (("Goal" :in-theory (enable fn-rci-delta (:e fn-rci-delta) fn-cfg-set-limit
                                     fn-cfg-deltap fn-cfg-delta-listp
                                     fn-cfg-labelp fn-record-uint32p))))

(in-theory (disable fn-rci-decide-stream fn-rci-context fn-rci-recorded-config
                    fn-rci-config-now fn-rci-recordedp fn-rci-delta))
