; e-surface.md sections 4.2 and 5. The existing kind 28 cursor and
; result-free refusal use one counted NNTP status line and one FNCT frame.
; The peer read in 13.4 needs its own result layout. The inbox page codec
; has no fields for the peer batch header or for a history/evidence pair.
(in-package "ACL2")
(include-book "cns")
(include-book "xfnc-view")
(include-book "xfnc-ops")
(fn2-book-layer :e)

(defun fn2-xfnc-refusal-word (reason)
  (declare (xargs :guard t))
  (case reason
    (:frame *fn2-cns-reason-frame*)
    (:access *fn2-cns-reason-access*)
    ((:absent :query) *fn2-cns-reason-query*)
    (:scope *fn2-cns-reason-scope*)
    (:behind *fn2-cns-reason-behind*)
    (:beyond-frontier *fn2-cns-reason-beyond-frontier*)
    (:meter *fn2-cns-reason-meter*)
    (:cursor-version *fn2-cns-reason-cursor-version*)
    (:unknown-consumer *fn2-cns-reason-unknown-consumer*)
    (:rebase-required *fn2-cns-reason-rebase-required*)
    (:unavailable *fn2-cns-reason-unavailable*)
    (otherwise nil)))

(defconst *fn2-xfnc-reply-line-room* 16)

(defun fn2-xfnc-assemble-reply (reply mask frame-at frame-count slot gen conn cgen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (b* ((end (fn2-pool-fill-value slot fn2-pool))
       ((unless (and (natp frame-at) (posp frame-count)
                     (<= *fn2-xfnc-reply-line-room* frame-at)
                     (equal (+ frame-at frame-count) end)))
        (mv :bounds fn2-pool))
       (kind *fn2-conn-kind*)
       ((mv code fn2-pool)
        (fn2-answer-say *fn2-nntp-command-xfnc* reply mask frame-count slot gen kind conn cgen fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool))
       (line-count (nfix (- (fn2-pool-fill-value slot fn2-pool) end)))
       ((unless (and (posp line-count) (<= line-count *fn2-xfnc-reply-line-room*)))
        (mv :bounds fn2-pool))
       ((mv code fn2-pool) (fn2-pool-copy-range slot gen end slot gen 0 line-count kind conn cgen fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool))
       ((mv code fn2-pool)
        (fn2-pool-copy-range slot gen frame-at slot gen line-count frame-count kind conn cgen fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool)))
    (fn2-pool-truncate slot gen (+ line-count frame-count) kind conn cgen fn2-pool)))
(fn2-pool-preserves fn2-xfnc-assemble-reply (reply mask frame-at frame-count slot gen conn cgen fn2-pool)
 :position 1 :rows nil)
(in-theory (disable fn2-xfnc-assemble-reply))

(defun fn2-xfnc-stage-reply (row class word principal history incarnation stream cid epoch version view position
                             mask slot gen conn cgen fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (stringp word))))
  (b* ((kind *fn2-conn-kind*)
       (base (* 128 (nfix row)))
       ((mv code fn2-pool)
        (fn2-fnct-put-be 0 0 *fn2-xfnc-reply-line-room* slot gen kind conn cgen fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-fields fn2-digests fn2-b3 fn2-pool))
       (roff *fn2-xfnc-reply-line-room*)
       ((mv code fn2-pool) (fn2-answer-put-text 0 word slot gen kind conn cgen fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-fields fn2-digests fn2-b3 fn2-pool))
       (result-at (fn2-pool-fill-value slot fn2-pool))
       ((mv code qoff qlen fn2-fields fn2-pool)
        (if (equal class 0)
            (fn2-cns-put-query-cursor base cid principal history incarnation stream version view epoch position
                                     slot gen kind conn cgen fn2-fields fn2-pool)
          (mv :ok result-at 0 fn2-fields fn2-pool)))
       ((unless (eq code :ok)) (mv code fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv code frame-at frame-count fn2-fields fn2-digests fn2-b3 fn2-pool)
        (fn2-fnct-put-k28 base row class roff (length word) qoff qlen slot gen kind conn cgen
                          fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-fields fn2-digests fn2-b3 fn2-pool))
       (reply (case class
                (0 *fn2-nntp-reply-xfnc-accepted*)
                (1 *fn2-nntp-reply-xfnc-refused*)
                (otherwise *fn2-nntp-reply-xfnc-uncertain*)))
       ((mv code fn2-pool) (fn2-xfnc-assemble-reply reply mask frame-at frame-count slot gen conn cgen fn2-pool)))
    (mv code fn2-fields fn2-digests fn2-b3 fn2-pool)))
(fn2-pool-block-shape fn2-xfnc-stage-reply-shape
  (fn2-xfnc-stage-reply row class word principal history incarnation stream cid epoch version view position
                        mask slot gen conn cgen fn2-fields fn2-digests fn2-b3 fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
       (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
       (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 1) (fn2-digests 2) (fn2-b3 3) (fn2-pool 4))
  (("Goal" :in-theory (e/d (fn2-xfnc-stage-reply)
                           (fn2-fieldsp fn2-fields-wfp fn2-digestsp fn2-digests-wfp
                            fn2-b3p fn2-b3-wfp fn2-poolp fn2-pool-wfp
                            fn2-fields-rows fn2-digests-rows fn2-b3-rows fn2-pool-rows)))))
(in-theory (disable fn2-xfnc-stage-reply))

; A successful return owns one complete page at TX[0,fill). On a staged
; failure the workspace is reset. No transport borrow is taken here.
(fn2-csnapshot-op fn2-xfnc-render-reply
 (conn cgen class word principal stream cid epoch version view position) 1
 (b* (((mv auth &) (fn2-conn-authenticated-principal conn cgen fn2-core))
      ((unless (and (eq auth :ok) (stringp word)
                    (<= (length word) 64) (member-equal class '(0 1 2))))
       (mv :state fn2-core))
      ((mv workspace row) (fn2-xfnc-fc-row conn fn2-core))
      ((unless (eq workspace :ok)) (mv workspace fn2-core))
      (slot (fn2-conn-row-tx-slot conn fn2-core))
      (gen (fn2-conn-row-tx-gen conn fn2-core))
      (mask (fn2-conn-row-mask conn fn2-core))
      ((mv history incarnation) (fn2-core-history-values fn2-core)))
   (stobj-let ((fn2-fields (fn2-core-fields fn2-core))
               (fn2-digests (fn2-core-digests fn2-core))
               (fn2-b3 (fn2-core-b3 fn2-core))
               (fn2-pool (fn2-core-pool fn2-core)))
    (code fn2-fields fn2-digests fn2-b3 fn2-pool)
    (b* (((unless (eq (fn2-pool-workspace-code slot gen *fn2-conn-kind* conn cgen fn2-pool) :ok))
          (mv :busy fn2-fields fn2-digests fn2-b3 fn2-pool))
         ((unless (zp (fn2-pool-fill-value slot fn2-pool)))
          (mv :state fn2-fields fn2-digests fn2-b3 fn2-pool))
         ((mv code fn2-fields fn2-digests fn2-b3 fn2-pool)
          (fn2-xfnc-stage-reply row class word principal history incarnation stream cid epoch version view position
                                mask slot gen conn cgen fn2-fields fn2-digests fn2-b3 fn2-pool))
         ((when (eq code :ok)) (mv :ok fn2-fields fn2-digests fn2-b3 fn2-pool))
         ((mv reset fn2-pool) (fn2-pool-reset slot gen *fn2-conn-kind* conn cgen fn2-pool)))
      (mv (if (eq reset :ok) code :state) fn2-fields fn2-digests fn2-b3 fn2-pool))
    (mv code fn2-core))))
(in-theory (disable fn2-xfnc-render-reply))

; The kind 28 refusal has no verb discriminator, and its result is empty.
; A malformed outer frame therefore uses :none with the same "frame" word.
(fn2-csnapshot-op fn2-xfnc-reply-refusal (conn cgen verb reason) 1
 (b* ((word (fn2-xfnc-refusal-word reason))
      ((unless (and word (member-eq verb '(:none :register :read))))
       (mv :state fn2-core)))
   (fn2-xfnc-render-reply conn cgen 1 (fn2-cns-reason-word *fn2-cns-verb-register* word)
                         0 0 0 0 0 0 0 fn2-core)))
(in-theory (disable fn2-xfnc-reply-refusal))
(defcost fn2-xfnc-reply-refusal :answers t :bytes 512
 :tables (fn2-core-pool fn2-core-fields fn2-core-digests fn2-core-b3)
 :doc "Render a typed counted XFNC refusal into the idle connection TX workspace.")

; Durability uncertainty is its own class and carries no cursor.
(fn2-csnapshot-op fn2-xfnc-reply-uncertain (conn cgen) 1
 (fn2-xfnc-render-reply conn cgen 2 "" 0 0 0 0 0 0 0 fn2-core))
(in-theory (disable fn2-xfnc-reply-uncertain))
(defcost fn2-xfnc-reply-uncertain :answers t :bytes 512
 :tables (fn2-core-pool fn2-core-fields fn2-core-digests fn2-core-b3)
 :doc "Render a typed counted XFNC uncertainty into the idle connection TX workspace.")

; The register actor passes the registration it read back from the ledger.
; The live request supplies the reply owner and principal.
(defmacro fn2-xfnc-register-reply-events ()
 '(progn
(fn2-csnapshot-op fn2-xfnc-register-reply (cursor generation stream consumer epoch version view position) 1
 (b* (((mv code pid conn cgen) (fn2-xfnc-live-login cursor generation fn2-core))
      ((unless (and (eq code :ok) (posp stream) (unsigned-byte-p 60 stream)
                    (posp consumer) (unsigned-byte-p 60 consumer) (posp epoch) (unsigned-byte-p 60 epoch)
                    (posp version) (unsigned-byte-p 60 version) (posp view) (unsigned-byte-p 60 view)
                    (unsigned-byte-p 60 position)))
       (mv :state fn2-core)))
   (fn2-xfnc-render-reply conn cgen 0 "" pid stream consumer epoch version view position fn2-core)))
(in-theory (disable fn2-xfnc-register-reply))))
(defcost fn2-xfnc-register-reply :answers t :bytes 2048
 :tables (fn2-core-pool fn2-core-fields fn2-core-digests fn2-core-b3)
 :doc "Render the live request's materialized register result into its idle TX workspace.")
