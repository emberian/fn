; Full selected-recovery assertions retained from f98412d19.
; The actual pre-crash producer is shared with the narrower LIVE gate.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "recovery-release-producer-support")
(include-book "recovery-release-image-support")

(defun fn2-rrc-body (fault fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((mv producer fn2-core fn2-sim fn2-own)
       (fn2-rrc-producer fn2-core fn2-sim fn2-own))
      ((unless (and (eq (car producer) :persisted) (= (len producer) 8)))
       (mv producer fn2-core fn2-sim fn2-own))
      (target (nth 1 producer)) (ep (nth 2 producer)) (allocation (nth 3 producer))
      (prefix (nth 4 producer)) (suffix (nth 5 producer))
      (batch (nth 6 producer)) (event (nth 7 producer))
      ((mv restarted fn2-core fn2-sim fn2-own)
       (fn2-ccp-restart *fn2-rrc-profile* *fn2-ccp-image-size* fn2-core fn2-sim fn2-own))
      ((unless (eq restarted :ok)) (mv (list :restart restarted) fn2-core fn2-sim fn2-own))
      ((mv selected id fn2-core fn2-sim fn2-own)
       (fn2-rrc-selected-release 600000 batch event fn2-core fn2-sim fn2-own))
      ((unless (eq selected :release)) (mv (list :selected selected) fn2-core fn2-sim fn2-own))
      (target-current
       (stobj-let ((fn2-allocation-release (fn2-core-allocation-release fn2-core))) (same)
        (and (= (fn2-allocation-release-extent 0 fn2-allocation-release) target)
             (= (fn2-allocation-release-epoch 0 fn2-allocation-release) ep)
             (= (fn2-allocation-release-allocation 0 fn2-allocation-release) allocation)) same))
      ((unless target-current) (mv '(:target-identity) fn2-core fn2-sim fn2-own))
      ((mv result fn2-core) (fn2-rrd-image-packet 20000 id fault fn2-core fn2-sim)))
  (mv result fn2-core fn2-sim fn2-own)))

(defun fn2-rrc-test (fault)
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-core fn2-sim fn2-own)
  (fn2-rrc-body fault fn2-core fn2-sim fn2-own)))

; Each assertion constructs and crashes its own actual persisted history.
; Missing publication, RELEASE handoff, selected source or auth is a failure.
(assert-event (fn2-rrd-result-p :clean (fn2-rrc-test :clean)))
(assert-event (fn2-rrd-result-p :wrong-opgen (fn2-rrc-test :wrong-opgen)))
(assert-event (fn2-rrd-result-p :short (fn2-rrc-test :short)))
(assert-event (fn2-rrd-result-p :stale-source (fn2-rrc-test :stale-source)))
