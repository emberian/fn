; fn: replay the two physical journals in their actual coordinate systems.
;
; Configuration records have a dense sequence of their own and name the next
; unconsumed Store transaction id. Store events have their own dense sequence
; and consume a transaction id. A configuration at the same id precedes the
; event; several such configurations are ordered by their own sequence. This
; preserves the existing on-disk formats, including stores written before
; live reconfiguration. This fold runs only at recovery, never per command.

(in-package "ACL2")
(include-book "config-stream")

(defun fn-cpr-config-firstp (configs events)
  (declare (xargs :guard t))
  (and (consp configs)
       (or (not (consp events))
           (<= (nfix (fn-cfg-record-txid (car configs)))
               (nfix (fn-store-event-txid (car events)))))))

(defthm fn-cpr-config-firstp-has-config
  (implies (fn-cpr-config-firstp configs events) (consp configs))
  :hints (("Goal" :in-theory (enable fn-cpr-config-firstp))))

(defun fn-cpr-event-servedp (cn event)
  ; The served-domain check belongs only to events that create an article.
  ; A retention or identity-neutral event has no selected group; applying
  ; fn-cnode-apply-record to it would incorrectly refuse every such event.
  (declare (xargs :guard t))
  (cond ((fn-record-p event)
         (fn-cnode-selection-servedp (fn-cnode-config cn)
                                     (fn-record-groups event)))
        ((fn-stxa-p event)
         (fn-cnode-selection-servedp
          (fn-cnode-config cn)
          (fn-record-groups (fn-replay-composite-record event))))
        (t t)))

(defun fn-cpr-apply-event (cn event)
  ; Replay uses the same Store-event interpreter as the standalone Store.
  ; This is recovery-only, so checking the carried node recognizer here does
  ; not put whole-state revalidation on a served command path.
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-cnode-statep cn)
           (fn-store-event-p event)
           (fn-cpr-event-servedp cn event))
      (let ((next (fn-replay-apply-record (fn-cnode-node cn) event)))
        (if (and (consp next) (fn-node-statep next))
            (fn-cnode-make next (fn-cnode-config cn))
          nil))
    nil))

(verify-guards fn-cpr-apply-event
  :hints (("Goal" :in-theory (e/d (fn-cnode-statep)
                                  (fn-cpr-event-servedp fn-record-p fn-stxa-p
                                   fn-store-event-p)))))

(defun fn-cpr-loop (cn configs events config-sequence event-sequence)
  (declare (xargs :guard t :verify-guards nil
                  :measure (+ (len configs) (len events))))
  (let ((position (+ (nfix config-sequence) (nfix event-sequence))))
    (if (not (fn-cnode-statep cn))
        (fn-replay-fault cn position :invalid-node)
      (if (fn-cpr-config-firstp configs events)
          (let* ((record (car configs))
                 (txid (fn-cfg-record-txid record))
                 (node (fn-cnode-node cn)))
            (cond ((not (fn-cfg-recordp record))
                   (fn-replay-fault cn position :invalid-config-record))
                  ((not (equal (fn-cfg-record-sequence record) config-sequence))
                   (fn-replay-fault cn position :config-sequence))
                  ((not (fn-replay-advance-okp node txid))
                   (fn-replay-fault cn position :config-txid))
                  (t (let ((at (fn-cnode-make
                                (fn-replay-advance-txid node txid)
                                (fn-cnode-config cn))))
                       (if (not (fn-cnode-statep at))
                           (fn-replay-fault cn position :invalid-node)
                         (if (not (fn-cnode-record-acceptablep
                                   at record (fn-cnode-line-ceiling)))
                             (fn-replay-fault cn position :config-refusal)
                           (fn-cpr-loop
                            (fn-cnode-apply-config
                             at record (fn-cnode-line-ceiling))
                            (cdr configs) events
                            (+ 1 (nfix config-sequence)) event-sequence)))))))
        (if (consp events)
            (let ((event (car events)))
              (cond ((not (fn-store-event-p event))
                     (fn-replay-fault cn position :invalid-event))
                    ((not (equal (fn-store-event-sequence event) event-sequence))
                     (fn-replay-fault cn position :event-sequence))
                    (t (let ((next (fn-cpr-apply-event cn event)))
                         (if (not (fn-cnode-statep next))
                             (fn-replay-fault cn position :event-refusal)
                           (fn-cpr-loop next configs (cdr events)
                                        config-sequence
                                        (+ 1 (nfix event-sequence))))))))
          (if (and (null configs) (null events))
              (fn-replay-ok cn position)
            (fn-replay-fault cn position :improper-history)))))))

(defun fn-cpr-replay (configs events)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cpr-loop (fn-cnode-initial (fn-cfg-initial)) configs events 0 0))

; A successful fold has not merely parsed two byte streams. It has checked
; each configuration at the reservation total produced by all earlier Store
; events, and its resulting node remains one coherent configured state.
(defthm fn-cpr-loop-ok-is-configured
  (implies (equal (fn-replay-result-kind
                  (fn-cpr-loop cn configs events config-sequence
                               event-sequence))
                 :ok)
           (fn-cnode-statep
            (fn-replay-result-node
             (fn-cpr-loop cn configs events config-sequence
                          event-sequence))))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events config-sequence
                                     event-sequence)
           :in-theory (e/d (fn-cpr-loop)
                           (fn-cnode-statep fn-cnode-apply-config
                            fn-cpr-apply-event fn-cnode-record-acceptablep
                            fn-store-event-p fn-cfg-recordp)))))

(defthm fn-cpr-replay-ok-is-configured
  (implies (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
           (fn-cnode-statep
            (fn-replay-result-node (fn-cpr-replay configs events))))
  :hints (("Goal" :use ((:instance fn-cpr-loop-ok-is-configured
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (config-sequence 0) (event-sequence 0)))
           :in-theory (disable fn-cpr-loop-ok-is-configured))))

(verify-guards fn-cpr-loop
  :hints (("Goal" :in-theory (e/d (fn-cnode-statep)
                                  (fn-cpr-config-firstp fn-cpr-apply-event
                                   fn-cfg-recordp fn-store-event-p)))))
(verify-guards fn-cpr-replay)

(deftheory fn-cpr-vocabulary
  '(fn-cpr-config-firstp fn-cpr-event-servedp fn-cpr-apply-event
    fn-cpr-loop fn-cpr-replay))
(in-theory (disable fn-cpr-vocabulary))
