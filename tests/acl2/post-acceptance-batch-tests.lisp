; Teeth for the approved A2/A4 contracts and context-v2 batch homes.
(in-package "ACL2")
(include-book "../../books/post-acceptance-batch")
(include-book "../../books/records-attach")

(with-guard-checking-event :none
 (encapsulate ()
(defun pbtt-encode-row (row fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (mv (fn-rcon-store-event-encode (fn-row-wire-of row fn-arena)) fn-arena))
(defun pbtt-event-octets (row)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena (mv-let (e fn-arena) (pbtt-encode-row row fn-arena) e)))
; Capture executable multiple values before using them in ground events.
(defun pbtt-prepare-retention (oc event)
 (declare (xargs :verify-guards nil))
 (mv-let (answer next) (fn-pdc-pout-prepare-retention oc event)
  (list answer next)))
(defun pbtt-end-okp (a blen)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (ok pre ins ioff sufhead suf) (fn-pacc-end a blen)
  (declare (ignore pre ins ioff sufhead suf))
  ok))
(defun pbtt-reserve-owner (o events)
 (declare (xargs :verify-guards nil))
 (if (consp events)
  (pbtt-reserve-owner (fn-own-store-step o (car events)) (cdr events)) o))
(defconst *pbtt-initial* (fn-sn-initial '("fn.test") 100))
(defconst *pbtt-live-owner*
 (pbtt-reserve-owner (fn-own-start *pbtt-initial* 1)
  '((:io :start-frontier nil) (:io :frontier-file :ok)
    (:io :frontier-replace :ok) (:io :frontier-directory :ok))))
(defconst *pbtt-live* (fn-own-store *pbtt-live-owner*))
(defconst *pbtt-oc* (fn-ocfg-make *pbtt-live-owner* (fn-cfg-initial) nil nil))
(defconst *pbtt-ret* (fn-store-retention-event-make :undertake 0 0 0 "r" "s" "e" 1))
(defconst *pbtt-id* (fn-stxk-make 0 0 0 1 '(102 110) '(7)))
(defconst *pbtt-consumer* (fn-cpe-make 0 0 0 (list :bootstrap '(1) '(2))))
(defconst *pbtt-topic* (list :topic-admin-install 0 0 0 0 (make-list 32 :initial-element 7)))
(defconst *pbtt-prepare-result* (pbtt-prepare-retention *pbtt-oc* *pbtt-ret*))
(defconst *pbtt-answer* (nth 0 *pbtt-prepare-result*))
(defconst *pbtt-prepared* (nth 1 *pbtt-prepare-result*))
(defconst *pbtt-after* (fn-sbud-oc-store *pbtt-prepared*))
(defconst *pbtt-row* (fn-sf-record-candidate (fn-sn-files *pbtt-after*)))
(defconst *pbtt-ctx* (fn-pctx-of-batch *pbtt-row*))
(defconst *pbtt-next* (fn-state-next-txid (fn-node-acceptance (fn-sn-node *pbtt-live*))))
(defconst *pbtt-e* (pbtt-event-octets *pbtt-row*))
; The image's carried owner prepare, following the actual four successful
; frontier operations from an initial store, stages and lays out at kernel-next.
(assert-event
 (and (fn-sn-statep *pbtt-initial*) (fn-sn-statep *pbtt-live*)
      (fn-cfgp (fn-cfg-initial)) (equal *pbtt-answer* :prepared)
      (fn-store-retention-event-p *pbtt-ret*) (fn-pout-stagedp *pbtt-live* *pbtt-after*)
      (fn-store-retention-event-p *pbtt-row*) (fn-pctx-p *pbtt-ctx*)
      (equal (fn-rcon-store-event-txid *pbtt-row*) *pbtt-next*)
      (<= (len *pbtt-e*) *fn-pbatch-max*)
      (pbtt-end-okp
                 (fn-pacc-feed* (fn-pacc-begin (list *pbtt-next* *pbtt-ctx*))
                  (list (take 7 *pbtt-e*) (nthcdr 7 *pbtt-e*))) (len *pbtt-e*))))
; The draft-3 six-field counterexample is the old/new-context tooth.
(assert-event
 (and (not (fn-pctx-p (list (fn-rcon-store-event-txid *pbtt-row*) nil nil 0 nil nil)))
      (fn-pctx-p *pbtt-ctx*)
      (not (pbtt-end-okp
        (fn-pacc-feed*
         (fn-pacc-begin (list *pbtt-next* (list (fn-rcon-store-event-txid *pbtt-row*) nil nil 0 nil nil)))
         (list *pbtt-e*))
        (len *pbtt-e*)))))
; A2 stale refuses, matching lays out: dropping its inequality breaks refusal.
(assert-event
 (and (not (equal (1+ *pbtt-next*) (nth 0 *pbtt-ctx*)))
      (not (pbtt-end-okp (fn-pacc-feed*
       (fn-pacc-begin (list (1+ *pbtt-next*) *pbtt-ctx*)) (list *pbtt-e*)) (len *pbtt-e*)))
      (equal *pbtt-next* (nth 0 *pbtt-ctx*))
      (pbtt-end-okp (fn-pacc-feed*
       (fn-pacc-begin (list *pbtt-next* *pbtt-ctx*)) (list *pbtt-e*)) (len *pbtt-e*))))
; Structural store recognition admits a frontier gap; the real producer stages
; txid 1, but the kernel-next 0 acceptance refuses it. A4c's ok hypothesis is
; necessary: its txid-equality conclusion is false on this refused input.
(defconst *pbtt-gap*
 (fn-sn-update *pbtt-initial*
  (fn-sf-make :reserved 2 nil nil nil nil nil *fn-sf-recovery-barrier-count*)
  (fn-sn-node *pbtt-initial*)))
(defconst *pbtt-gap-event* (fn-store-retention-event-make :undertake 0 1 1 "r" "s" "e" 1))
(defconst *pbtt-gap-after* (fn-pdc-sn-prepare-retention *pbtt-gap* *pbtt-gap-event*))
(defconst *pbtt-gap-row* (fn-sf-record-candidate (fn-sn-files *pbtt-gap-after*)))
(defconst *pbtt-gap-next* (fn-state-next-txid (fn-node-acceptance (fn-sn-node *pbtt-gap*))))
(assert-event
 (and (fn-sn-statep *pbtt-gap*) (fn-store-retention-event-p *pbtt-gap-event*)
      (fn-pout-stagedp *pbtt-gap* *pbtt-gap-after*)
      (fn-pctx-p (fn-pctx-of-batch *pbtt-gap-row*))
      (not (equal (fn-rcon-store-event-txid *pbtt-gap-row*) *pbtt-gap-next*))
      (not (pbtt-end-okp
       (fn-pacc-begin (list *pbtt-gap-next* (fn-pctx-of-batch *pbtt-gap-row*)))
       (len (pbtt-event-octets *pbtt-gap-row*))))))

; retention whole antecedent/conclusion, then success-hypothesis removal.
(assert-event
 (let* ((s *pbtt-live*) (event *pbtt-ret*) (after (fn-pdc-sn-prepare-retention s event))
        (row (fn-sf-record-candidate (fn-sn-files after))))
  (and (fn-sn-statep s) (fn-store-retention-event-p event) (fn-pout-stagedp s after)
       (fn-store-retention-event-p row) (fn-pctx-p (fn-pctx-of-batch row)))))
(assert-event
 (let* ((s *pbtt-initial*) (event *pbtt-ret*) (after (fn-pdc-sn-prepare-retention s event))
        (row (fn-sf-record-candidate (fn-sn-files after))))
  (and (fn-sn-statep s) (fn-store-retention-event-p event) (not (fn-pout-stagedp s after))
       (not (and (fn-store-retention-event-p row) (fn-pctx-p (fn-pctx-of-batch row)))))))

; identity whole antecedent/conclusion, then success-hypothesis removal.
(assert-event
 (let* ((s *pbtt-live*) (event *pbtt-id*) (after (fn-ccar-sn-prepare-identity s event))
        (row (fn-sf-record-candidate (fn-sn-files after))))
  (and (fn-sn-statep s) (or (fn-stxk-p event) (fn-stxe-p event)) (fn-pout-stagedp s after)
       (or (fn-stxk-p row) (fn-stxe-p row)) (fn-pctx-p (fn-pctx-of-batch row)))))
(assert-event
 (let* ((s *pbtt-initial*) (event *pbtt-id*) (after (fn-ccar-sn-prepare-identity s event))
        (row (fn-sf-record-candidate (fn-sn-files after))))
  (and (fn-sn-statep s) (or (fn-stxk-p event) (fn-stxe-p event)) (not (fn-pout-stagedp s after))
       (not (and (or (fn-stxk-p row) (fn-stxe-p row)) (fn-pctx-p (fn-pctx-of-batch row)))))))

; consumer whole antecedent/conclusion, then success-hypothesis removal.
(assert-event
 (let* ((s *pbtt-live*) (event *pbtt-consumer*) (after (fn-pdc-sn-prepare-consumer s event))
        (row (fn-sf-record-candidate (fn-sn-files after))))
  (and (fn-sn-statep s) (fn-cpe-eventp event) (fn-pout-stagedp s after)
       (fn-cpe-eventp row) (fn-pctx-p (fn-pctx-of-batch row)))))
(assert-event
 (let* ((s *pbtt-initial*) (event *pbtt-consumer*) (after (fn-pdc-sn-prepare-consumer s event))
        (row (fn-sf-record-candidate (fn-sn-files after))))
  (and (fn-sn-statep s) (fn-cpe-eventp event) (not (fn-pout-stagedp s after))
       (not (and (fn-cpe-eventp row) (fn-pctx-p (fn-pctx-of-batch row)))))))

; topic whole antecedent/conclusion, then success-hypothesis removal.
(assert-event
 (let* ((s *pbtt-live*) (event *pbtt-topic*) (after (fn-pdc-sn-prepare-topic s event))
        (row (fn-sf-record-candidate (fn-sn-files after))))
  (and (fn-sn-statep s) (fn-th-topic-eventp event) (fn-pout-stagedp s after)
       (fn-th-topic-eventp row) (fn-pctx-p (fn-pctx-of-batch row)))))
(assert-event
 (let* ((s *pbtt-initial*) (event *pbtt-topic*) (after (fn-pdc-sn-prepare-topic s event))
        (row (fn-sf-record-candidate (fn-sn-files after))))
  (and (fn-sn-statep s) (fn-th-topic-eventp event) (not (fn-pout-stagedp s after))
       (not (and (fn-th-topic-eventp row) (fn-pctx-p (fn-pctx-of-batch row)))))))

; The codec maximum is attained. A home four octets smaller is refuted.
(defconst *pbtt-max-row*
 (fn-stxk-make *fn-cbor-max-uint* *fn-cbor-max-uint* *fn-cbor-max-uint* *fn-cbor-max-uint*
              (make-list *fn-stxk-max-profile* :initial-element 7)
              (make-list *fn-stxk-max-snapshot* :initial-element 7)))
(assert-event
 (let ((row *pbtt-max-row*))
  (and (fn-pbatch-rowp row) (fn-pctx-p (fn-pctx-of-batch row))
       (equal (len (pbtt-event-octets row)) *fn-pbatch-max*)
       (equal (len (fn-pctx-encode (fn-pctx-of-batch row))) *fn-pbatch-context-octets*)
       (equal (+ (len (fn-pctx-encode (fn-pctx-of-batch row))) (len (pbtt-event-octets row))) *fn-pth-cs*)
       (> (+ (len (fn-pctx-encode (fn-pctx-of-batch row))) (len (pbtt-event-octets row))) 65663))))
(value-triple (cw "A2/A4 TEETH: owner liveness, stale/matching, frontier gap, four success removals, v1/v2, maximal keyring home PASS.~%"))
))
