; Concrete source join drafts, intentionally not activated: actual paired
; recovery owns prefix FILES/history, captured projection root and custody.
(in-package "ACL2")
(include-book "consumer-configured-authority-replay")
(include-book "control-config-projection")

; ONE actual C decision produces state/full7-or8 and the projection entry.
; The entry records the actual parsed row coordinates and actual next config,
; not a generic synthesized delta or a replay under final configuration.
; Source token/root originate in the retained INITIAL/checkpoint operation;
; this function neither issues them nor establishes their custody.
(defun fn-capr-config-step-with-projection (s predecessor recorded-source current-event-count)
 (declare (xargs :guard (fn-cnode-statep (fn-cp-nth 1 s)) :verify-guards nil))
 (let* ((record (fn-cp-nth 0 (fn-cp-nth 14 s)))
        (one (fn-capr-config-step s current-event-count)))
  (if (not (eq (fn-cp-nth 0 one) :advanced)) one
   (let* ((next (fn-cp-nth 1 one))
          (config (fn-cnode-config (fn-cp-nth 1 next)))
          (entry (fn-ccpx-entry config (fn-cfg-record-sequence record)
                    (fn-cfg-record-txid record)
                    (fn-stxk-context-current-generation (fn-cp-nth 2 next))
                    recorded-source predecessor)))
    (list :advanced next (fn-cp-nth 2 one) entry)))))

; Legacy high reference only; the served successor is FnCTCD/FnCAPE.
; This draft still reads whole historical inputs before yielding and is
; NOT a bounded served entry. Begin from the SAME prefix lookup used by control
; producer. Before every yielded step, the actual caller rechecks current
; custody of captured chain root separately from account authority.
; EVENT-UPPER-TXID is actual included E-prefix bound, not last Ctxid. The
; caller must establish its association to this SAME captured prefix source.
; Verdict and target locks are retained BEFORE any config-lookup yield.
(defun fn-ctcp-article-begin (article verdicts files fn-hist chain captured-source event-upper-txid)
 (declare (xargs :stobjs fn-hist :guard t :verify-guards nil))
 (if (not (consp article)) '(:plan nil)
  (let* ((msgid (fn-article-msgid article))
         (event (fn-ctl-row-event-fx msgid files fn-hist))
         (control (if event (fn-hf-control (fn-held-facts (fn-ctl-event-row event))) nil))
         (target (fn-ctl-control-target control)))
   (if (not target) '(:plan nil)
    (let ((query (fn-store-event-txid event)))
     (if (not (and (natp event-upper-txid) (natp query) (<= query event-upper-txid)))
         '(:unavailable :control-event-source-bound)
      (let ((lookup (fn-ccpx-begin chain query captured-source)))
       (if (not (eq (fn-cp-nth 0 lookup) :yield)) lookup
        (list :yield (list :control-article-lookup msgid target control event
                           (fn-cp-nth 1 lookup) captured-source
                           (fn-ctl-lookup-verdict msgid verdicts)
                           (fn-ctl-control-locks
                            (fn-ctl-row-control-fx target files fn-hist))))))))))))

; ONE lookup cell, then the actual withdrawal-plan/tlocks constructors using
; exactly that selected historical config and the saved original verdict/locks.
; No fresh history/verdict reads after yield. Never call ordinary FnCTLConfigAt
; on typed C evidence. Verdict/source representation and per-step allocation
; relation remain obligations of the actual owner/recovery caller.
(defun fn-ctcp-article-step (cursor)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (and (fn-cbor-at-mostp cursor 9) (true-listp cursor)
               (equal (len cursor) 9) (eq (fn-cp-nth 0 cursor) :control-article-lookup)))
     '(:refused :control-article-cursor)
  (let ((one (fn-ccpx-tick (fn-cp-nth 5 cursor))))
   (cond ((eq (fn-cp-nth 0 one) :yield)
          (list :yield (ec-call (update-nth 5 (fn-cp-nth 1 one) cursor))))
         ((not (eq (fn-cp-nth 0 one) :configuration)) one)
         (t
          (let ((msgid (fn-cp-nth 1 cursor)) (target (fn-cp-nth 2 cursor))
                (control (fn-cp-nth 3 cursor)))
           (list :plan
             (fn-ctl-w-with-tlocks
              (fn-ctl-withdrawal-plan msgid (fn-cp-nth 7 cursor)
                                     target (fn-ctl-control-keys control) (fn-cp-nth 1 one))
              (fn-cp-nth 8 cursor))
             one)))))))

(in-theory (disable fn-capr-config-step-with-projection
                    fn-ctcp-article-begin fn-ctcp-article-step))
