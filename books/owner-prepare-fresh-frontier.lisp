; The reserved frontier is newer than every committed transaction.
(in-package "ACL2")
(include-book "owner-prepare-served-ocl")

(defthm fn-hpf-apply-event-successor
 (implies (and (fn-cstp-idlep (fn-cnode-node cn))
               (consp (fn-cpr-apply-event cn event)))
  (equal (fn-state-next-txid
          (fn-node-acceptance (fn-cnode-node (fn-cpr-apply-event cn event))))
         (+ 1 (fn-store-event-txid event))))
 :hints (("Goal" :use ((:instance fn-snt-apply-event-from-idle-is-at-the-successor
 (node (fn-cnode-node cn)) (record event)))
 :in-theory (e/d (fn-cpr-apply-event fn-cnode-statep fn-cstp-idlep)
 (fn-replay-apply-record fn-node-statep fn-store-event-p fn-cpr-event-servedp)))))

(defthm fn-hpf-next-lower-nonempty
 (implies (consp xs) (equal (fn-sf-next-lower xs lower) (fn-sf-next-lower xs 0)))
 :hints (("Goal" :induct (fn-sf-next-lower xs lower)
 :in-theory '(fn-sf-next-lower))))

(in-theory (disable fn-hpf-next-lower-nonempty))

(defthm fn-hpf-next-lower-cons
 (equal (fn-sf-next-lower (cons a xs) 0)
        (if (consp xs) (fn-sf-next-lower xs 0) (+ 1 (fn-store-event-txid a))))
 :hints (("Goal" :use ((:instance fn-hpf-next-lower-nonempty (lower (+ 1 (fn-store-event-txid a)))))
 :in-theory '(fn-sf-next-lower car-cons cdr-cons))))

(defthm fn-hpf-loop-next-bounds-history
 (implies (and (fn-cstp-idlep (fn-cnode-node cn))
               (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cs es)) :ok))
  (<= (fn-sf-next-lower events 0)
      (fn-state-next-txid
       (fn-node-acceptance
        (fn-cnode-node (fn-replay-result-node (fn-cpr-loop cn configs events cs es)))))))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-cpr-loop cn configs events cs es)
 :in-theory (e/d (fn-cpr-loop fn-hpf-next-lower-cons)
 (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
 fn-cnode-record-acceptablep fn-store-event-p fn-cfg-recordp
 fn-replay-advance-okp fn-replay-advance-txid fn-cnode-carried-acceptablep
 fn-cpr-config-firstp fn-store-event-txid fn-sf-next-lower)))))

(defthm fn-hpf-recoverable-bounds-history
 (implies (fn-cst-recoverablep configs events frontier)
          (<= (fn-sf-next-lower events 0) frontier))
 :rule-classes :linear
 :hints (("Goal"
 :use (fn-cstp-recoverable-facts
       (:instance fn-hpf-loop-next-bounds-history
        (cn (fn-cnode-initial (fn-cfg-initial))) (cs 0) (es 0)))
 :in-theory '(fn-cpr-replay fn-cstp-fold fn-cstp-initial-idle
 fn-cstp-advance-okp-bound))))

(defthm fn-hpf-reserved-frontier-is-fresh
 (implies (and (fn-cst-relation s)
               (equal (fn-sf-phase (fn-sn-files s)) :reserved))
  (<= (fn-sf-next-lower (fn-sf-records (fn-sn-files s)) 0)
      (+ -1 (fn-sf-frontier (fn-sn-files s)))))
 :rule-classes :linear
 :hints (("Goal" :use (fn-psrv-reserved-relation-facts
 (:instance fn-hpf-recoverable-bounds-history (configs (fn-sn-config-history s))
  (events (fn-sf-records (fn-sn-files s)))
  (frontier (+ -1 (fn-sf-frontier (fn-sn-files s))))))
 :in-theory nil)))

(defun fn-hpf-files-candidatep (record files)
 (declare (xargs :guard (fn-sf-statep files)
 :guard-hints (("Goal" :in-theory (enable fn-rcon-event-twin-rules)))))
 (and (fn-rcon-store-event-p record)
      (equal (fn-rcon-store-event-sequence record) (fn-sf-records-count files))
      (equal (1+ (fn-rcon-store-event-txid record)) (fn-sf-frontier files))
      (equal (fn-rcon-store-event-generation record) (fn-rcon-store-event-txid record))))

(defthm fn-hpf-files-candidatep-is-reference
 (implies (<= (fn-sf-next-lower (fn-sf-records files) 0)
              (+ -1 (fn-sf-frontier files)))
  (equal (fn-hpf-files-candidatep record files) (fn-pcar-files-candidatep record files)))
 :hints (("Goal" :in-theory '(fn-hpf-files-candidatep
 fn-pcar-files-candidatep-is-candidatep fn-pcar-candidatep
 fn-pcar-next-lower-is-next-lower fn-sf-records-count))))

(defun fn-hpf-stage-record (files record)
 (declare (xargs :guard (fn-sf-statep files)
 :guard-hints (("Goal" :in-theory (enable fn-rcon-event-twin-rules)))))
 (if (and (equal (fn-sf-phase files) :reserved)
          (fn-hpf-files-candidatep record files))
     (fn-sf-remake :record-staged (fn-sf-frontier files) nil
                   record nil (fn-sf-barriers files) files)
   files))

(defthm fn-hpf-stage-record-is-reference
 (implies (fn-cst-relation s)
  (equal (fn-hpf-stage-record (fn-sn-files s) record)
         (fn-pcar-stage-record (fn-sn-files s) record)))
 :hints (("Goal" :in-theory '(fn-hpf-stage-record fn-pcar-stage-record
 fn-hpf-files-candidatep-is-reference fn-hpf-reserved-frontier-is-fresh))))

(in-theory (disable fn-hpf-files-candidatep fn-hpf-stage-record))
