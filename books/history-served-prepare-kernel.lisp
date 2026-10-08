; Candidate staging without the historical last-record read.
(in-package "ACL2")
(include-book "owner-prepare-fresh-frontier")
(include-book "owner-prepare-deferred-carried")
(include-book "identity-retain-carried")
(include-book "post-prepare-catalog")

(defun fn-hpf-pdc-sn-prepare-retention (s event)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (fn-store-retention-event-p event)
           (eq (car (fn-ccar-cpe-projection-step (fn-sn-consumer s) event (fn-sn-identity-next s)))
               :ok)
           (consp (fn-replay-apply-retention-event (fn-sn-node s) event)))
      (let ((files (fn-hpf-stage-record (fn-sn-files s) event)))
        (if (equal (fn-sf-phase files) :record-staged) (fn-sn-update s files (fn-sn-node s)) s))
    s))

(defthm fn-hpf-pdc-sn-prepare-retention-is-reference
 (implies (fn-cst-relation s)
  (equal (fn-hpf-pdc-sn-prepare-retention s event) (fn-pdc-sn-prepare-retention s event)))
 :hints (("Goal" :in-theory '(fn-hpf-pdc-sn-prepare-retention fn-pdc-sn-prepare-retention fn-hpf-stage-record-is-reference))))
(verify-guards fn-hpf-pdc-sn-prepare-retention
 :hints (("Goal" :use ((:guard-theorem fn-pdc-sn-prepare-retention))
 :in-theory (disable fn-sn-statep fn-sf-statep fn-prc-carryp
 fn-node-statep fn-store-event-p fn-hpf-stage-record fn-pcar-stage-record))))
(in-theory (disable fn-hpf-pdc-sn-prepare-retention))

(defun fn-hpf-pdc-sn-prepare-consumer (s event)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (fn-cpe-eventp event)
           (eq (car (fn-ccar-cpe-projection-step (fn-sn-consumer s) event (fn-sn-identity-next s)))
               :ok)
           (consp (fn-replay-apply-record (fn-sn-node s) event)))
      (let ((files (fn-hpf-stage-record (fn-sn-files s) event)))
        (if (equal (fn-sf-phase files) :record-staged) (fn-sn-update s files (fn-sn-node s)) s))
    s))

(defthm fn-hpf-pdc-sn-prepare-consumer-is-reference
 (implies (fn-cst-relation s)
  (equal (fn-hpf-pdc-sn-prepare-consumer s event) (fn-pdc-sn-prepare-consumer s event)))
 :hints (("Goal" :in-theory '(fn-hpf-pdc-sn-prepare-consumer fn-pdc-sn-prepare-consumer fn-hpf-stage-record-is-reference))))
(verify-guards fn-hpf-pdc-sn-prepare-consumer
 :hints (("Goal" :use ((:guard-theorem fn-pdc-sn-prepare-consumer))
 :in-theory (disable fn-sn-statep fn-sf-statep fn-prc-carryp
 fn-node-statep fn-store-event-p fn-hpf-stage-record fn-pcar-stage-record))))
(in-theory (disable fn-hpf-pdc-sn-prepare-consumer))

(defun fn-hpf-pdc-sn-prepare-topic (s event)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (fn-th-topic-eventp event)
           (eq (fn-th-at 0 (fn-th-prefix-step (fn-sn-topic s) event)) :ok)
           (consp (fn-replay-apply-record (fn-sn-node s) event)))
      (let ((files (fn-hpf-stage-record (fn-sn-files s) event)))
        (if (equal (fn-sf-phase files) :record-staged) (fn-sn-update s files (fn-sn-node s)) s))
    s))

(defthm fn-hpf-pdc-sn-prepare-topic-is-reference
 (implies (fn-cst-relation s)
  (equal (fn-hpf-pdc-sn-prepare-topic s event) (fn-pdc-sn-prepare-topic s event)))
 :hints (("Goal" :in-theory '(fn-hpf-pdc-sn-prepare-topic fn-pdc-sn-prepare-topic fn-hpf-stage-record-is-reference))))
(verify-guards fn-hpf-pdc-sn-prepare-topic
 :hints (("Goal" :use ((:guard-theorem fn-pdc-sn-prepare-topic))
 :in-theory (disable fn-sn-statep fn-sf-statep fn-prc-carryp
 fn-node-statep fn-store-event-p fn-hpf-stage-record fn-pcar-stage-record))))
(in-theory (disable fn-hpf-pdc-sn-prepare-topic))

(defun fn-hpf-irc-sn-prepare-identity (s event carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-prc-carryp carry)) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (or (fn-stxe-p event) (fn-stxk-p event) (fn-hstxa-p event))
           (eq (car (fn-ccar-cpe-projection-step (fn-sn-consumer s) event (fn-sn-identity-next s)))
               :ok)
           (consp (fn-irc-apply-record (fn-sn-node s) event carry))
           (equal (fn-stxk-context-kind (fn-replay-identity-step (fn-sn-identity-context s) event))
                  :ok))
      (let ((files (fn-hpf-stage-record (fn-sn-files s) event)))
        (if (equal (fn-sf-phase files) :record-staged) (fn-sn-update s files (fn-sn-node s)) s))
    s))

(defthm fn-hpf-irc-sn-prepare-identity-is-reference
 (implies (fn-cst-relation s)
  (equal (fn-hpf-irc-sn-prepare-identity s event carry) (fn-irc-sn-prepare-identity s event carry)))
 :hints (("Goal" :in-theory '(fn-hpf-irc-sn-prepare-identity fn-irc-sn-prepare-identity fn-hpf-stage-record-is-reference))))
(verify-guards fn-hpf-irc-sn-prepare-identity
 :hints (("Goal" :use ((:guard-theorem fn-irc-sn-prepare-identity))
 :in-theory (disable fn-sn-statep fn-sf-statep fn-prc-carryp
 fn-node-statep fn-store-event-p fn-hpf-stage-record fn-pcar-stage-record))))
(in-theory (disable fn-hpf-irc-sn-prepare-identity))

(defun fn-hpf-ppc-spc-prepare (s record dup carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-prc-carryp carry) (fn-ppc-dup-okp s record dup))
                  :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (null (fn-node-stage (fn-sn-node s)))
           (fn-held-p record)
           (equal (fn-hc-generation (fn-held-context record)) (fn-sn-keyring-generation s))
           (eq (car (fn-rcon-cpe-projection-step (fn-sn-consumer s) record (fn-sn-identity-next s)))
               :ok))
      (let* ((node (fn-ppc-sn-prepare-node (fn-sn-node s) record dup carry))
             (files (fn-hpf-stage-record (fn-sn-files s) record)))
        (if (and (fn-rcon-sn-record-bindsp node record) (equal (fn-sf-phase files) :record-staged))
            (fn-sn-update s files node)
          s))
    s))

(defthm fn-hpf-ppc-spc-prepare-is-reference
 (implies (fn-cst-relation s)
  (equal (fn-hpf-ppc-spc-prepare s record dup carry) (fn-ppc-spc-prepare s record dup carry)))
 :hints (("Goal" :in-theory '(fn-hpf-ppc-spc-prepare fn-ppc-spc-prepare fn-hpf-stage-record-is-reference))))
(verify-guards fn-hpf-ppc-spc-prepare
 :hints (("Goal" :use ((:guard-theorem fn-ppc-spc-prepare))
 :in-theory (disable fn-sn-statep fn-sf-statep fn-prc-carryp
 fn-node-statep fn-store-event-p fn-hpf-stage-record fn-pcar-stage-record))))
(in-theory (disable fn-hpf-ppc-spc-prepare))
