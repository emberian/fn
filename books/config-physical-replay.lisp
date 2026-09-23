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
                       (if (not (fn-cnode-record-acceptablep
                                 at record (fn-cnode-line-ceiling)))
                           (fn-replay-fault cn position :config-refusal)
                         (fn-cpr-loop
                          (fn-cnode-apply-config
                           at record (fn-cnode-line-ceiling))
                          (cdr configs) events
                          (+ 1 (nfix config-sequence)) event-sequence))))))
        (if (consp events)
            (let ((event (car events)))
              (cond ((not (fn-store-event-p event))
                     (fn-replay-fault cn position :invalid-event))
                    ((not (equal (fn-store-event-sequence event) event-sequence))
                     (fn-replay-fault cn position :event-sequence))
                    (t (let ((next (fn-cnode-apply-record cn event)))
                         (if (not (consp next))
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
                            fn-cnode-apply-record fn-cnode-record-acceptablep
                            fn-store-event-p fn-cfg-recordp)))))

(defthm fn-cpr-replay-ok-is-configured
  (implies (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
           (fn-cnode-statep
            (fn-replay-result-node (fn-cpr-replay configs events))))
  :hints (("Goal" :use ((:instance fn-cpr-loop-ok-is-configured
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (config-sequence 0) (event-sequence 0)))
           :in-theory (disable fn-cpr-loop-ok-is-configured))))

(verify-guards fn-cpr-loop)
(verify-guards fn-cpr-replay)

(deftheory fn-cpr-vocabulary
  '(fn-cpr-config-firstp fn-cpr-loop fn-cpr-replay))
(in-theory (disable fn-cpr-vocabulary))
