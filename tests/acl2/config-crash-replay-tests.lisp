; Teeth for books/config-crash-replay.lisp: the crash headline over the
; replay `fn-owner-recover' calls.  The reachable witness is the live arm of
; tests/acl2/config-owner-publish-tests.lisp: an owner recovered over two
; configuration records and two Store events, a group create staged by
; connection 1, connection 1 closed, the record made durable and published.
; The journals are cut at every instant the headline quantifies over and
; each cut is replayed by `fn-cpr-replay'.  Then one must-fail per keystone
; hypothesis, and the journal that separates the two replays.
(in-package "ACL2")
(include-book "../../books/config-crash-replay")
(include-book "std/testing/must-fail" :dir :system)
(include-book "config-owner-publish-tests")

(defconst *ccr-store* (fn-own-store (fn-ocfg-owner *ocp-admin*)))
(defconst *ccr-h* (fn-sn-config-history *ccr-store*))
(defconst *ccr-e* (fn-sf-records (fn-sn-files *ccr-store*)))
(defconst *ccr-record* (fn-ocfg-staged *ocp-closed*))
(defconst *ccr-durable* (append *ccr-h* (list *ccr-record*)))

; The witness is the headline's own instance: OC is the recovered owner,
; the arm is (:reconfigure 1 deltas) then (:close 1), publication at
; generation 3.  Two configuration records and two Store events, so the
; replay interleaves both journals.
(assert-event (fn-ocl-config-historyp *ocp-admin*))
(assert-event (equal *ocp-closed*
                     (fn-ocfg-step (fn-ocfg-step *ocp-admin*
                                                 (list :reconfigure 1 *ocp-deltas*))
                                   (list :close 1))))
(assert-event (equal (len *ccr-h*) 2))
(assert-event (equal (len *ccr-e*) 2))
(assert-event (fn-cfg-recordp *ccr-record*))
(assert-event (equal (fn-cfg-record-generation *ccr-record*) 3))

(defun fn-ccr-recovered (configs events)
  ; What `fn-owner-recover' installs: :fault, or the replayed configuration.
  (let ((replayed (fn-cpr-replay configs events)))
    (if (equal (fn-replay-result-kind replayed) :ok)
        (fn-cnode-config (fn-replay-result-node replayed))
      :fault)))

; Cut 1: after staging, before the close.  The store and so both journals
; are the recovered ones; they replay to the live generation, 2.
(defconst *ccr-staged-only* *ocp-staged*)
(assert-event (equal (fn-own-store (fn-ocfg-owner *ccr-staged-only*)) *ccr-store*))
(assert-event (equal (fn-ccr-recovered *ccr-h* *ccr-e*)
                     (fn-ocfg-config *ccr-staged-only*)))
(assert-event (equal (fn-cfg-generation (fn-ccr-recovered *ccr-h* *ccr-e*)) 2))

; Cut 2: after the close, before the durable write.  Same journals, same
; recovered configuration, and it is the live one.
(assert-event (equal (fn-own-store (fn-ocfg-owner *ocp-closed*)) *ccr-store*))
(assert-event (equal (fn-ccr-recovered *ccr-h* *ccr-e*)
                     (fn-ocfg-config *ocp-closed*)))
(assert-event (equal (fn-ocfg-config *ocp-closed*) (fn-ocfg-config *ocp-admin*)))

; Cut 3: the record is durable, publication has not run.  The replay of the
; appended configuration journal is :ok and recovers the whole record
; applied: the model's publication, generation 3, the new group served.
(assert-event (equal (fn-replay-result-kind (fn-cpr-replay *ccr-durable* *ccr-e*)) :ok))
(assert-event (equal (fn-ccr-recovered *ccr-durable* *ccr-e*)
                     (fn-ocfg-config (fn-ocfg-step *ocp-closed* (list :complete)))))
(assert-event (equal (fn-ccr-recovered *ccr-durable* *ccr-e*)
                     (fn-cfg-apply-record (fn-ocfg-config *ocp-admin*) *ccr-record*)))
(assert-event (equal (fn-cfg-generation (fn-ccr-recovered *ccr-durable* *ccr-e*)) 3))
(assert-event (member-equal "fn.live"
                            (fn-cnode-served-of (fn-ccr-recovered *ccr-durable* *ccr-e*))))
(assert-event (not (member-equal "fn.live"
                                 (fn-cnode-served-of (fn-ccr-recovered *ccr-h* *ccr-e*)))))

; Cut 4: after the :durable publication.  The installed store carries exactly
; the appended journal and the old Store journal; recovery from it gives the
; published configuration; the hypothesis holds again.
(defconst *ccr-pst* (fn-own-store (fn-ocfg-owner *ocp-published*)))
(assert-event (equal (car *ocp-pub*) :durable))
(assert-event (equal (fn-sn-config-history *ccr-pst*) *ccr-durable*))
(assert-event (equal (fn-sf-records (fn-sn-files *ccr-pst*)) *ccr-e*))
(assert-event (equal (fn-ccr-recovered (fn-sn-config-history *ccr-pst*)
                                       (fn-sf-records (fn-sn-files *ccr-pst*)))
                     (fn-ocfg-config *ocp-published*)))
(assert-event (not (fn-ocfg-staged *ocp-published*)))
(assert-event (fn-ocl-config-historyp *ocp-published*))

; A journal carrying a record that is not the next whole generation (a
; generation skipped) is not :ok: the host answers :fault, it never installs
; a configuration between the two.
(defconst *ccr-skipped*
  (fn-cfg-record-make 2 8 4 (fn-cfg-record-change *ccr-record*)
                      (fn-cfg-record-stamp *ccr-record*)))
(assert-event (equal (fn-ccr-recovered (append *ccr-h* (list *ccr-skipped*)) *ccr-e*)
                     :fault))

; Each cut agrees with the configuration-only replay the model headline is
; stated over (`fn-ocl-cpr-replay-ok-is-config-replay-ok').
(assert-event (equal (fn-replay-result-kind (fn-cnode-config-replay *ccr-h*)) :ok))
(assert-event (equal (fn-cnode-config (fn-replay-result-node (fn-cnode-config-replay *ccr-h*)))
                     (fn-ccr-recovered *ccr-h* *ccr-e*)))
(assert-event (equal (fn-cnode-config
                      (fn-replay-result-node (fn-cnode-config-replay *ccr-durable*)))
                     (fn-ccr-recovered *ccr-durable* *ccr-e*)))

; -----------------------------------------------------------------------------
; fn-ocl-crash-at-any-instant-recovers-the-live-generation, its one
; hypothesis `fn-ocl-config-historyp'.  An owner claiming the initial
; configuration over the same store: the journals recover generation 2, not
; its claim, at the first cut.
(defconst *ccr-forged*
  (fn-ocfg-make (fn-ocfg-owner *ocp-admin*) (fn-cfg-initial)
                (fn-ocfg-pins *ocp-admin*) nil))
(defconst *ccr-forged-staged*
  (fn-ocfg-step (fn-ocfg-step *ccr-forged* (list :reconfigure 1 *ocp-deltas*))
                (list :close 1)))
(assert-event (not (fn-ocl-config-historyp *ccr-forged*)))
(assert-event (not (equal (fn-ccr-recovered *ccr-h* *ccr-e*)
                          (fn-ocfg-config *ccr-forged-staged*))))
(local
 (must-fail
  (defthm fn-ocl-crash-recovers-the-live-generation-without-history
    (let ((staged (fn-ocfg-step (fn-ocfg-step oc (list :reconfigure id deltas))
                                (list :close id))))
      (equal (fn-cnode-config
              (fn-replay-result-node
               (fn-cpr-replay (fn-sn-config-history
                               (fn-own-store (fn-ocfg-owner staged)))
                              (fn-sf-records
                               (fn-sn-files (fn-own-store (fn-ocfg-owner staged)))))))
             (fn-ocfg-config staged)))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t
             :in-theory (disable fn-cpr-replay fn-ocfg-step))))))

; -----------------------------------------------------------------------------
; fn-ocl-cpr-replay-ok-is-config-replay-ok, its one hypothesis, the called
; replay's :ok.  A configuration journal holding a non-record: neither
; replay is :ok.
(assert-event (equal (fn-ccr-recovered (list 7) nil) :fault))
(assert-event (not (equal (fn-replay-result-kind (fn-cnode-config-replay (list 7))) :ok)))
(local
 (must-fail
  (defthm fn-ocl-config-replay-ok-without-the-called-ok
    (equal (fn-replay-result-kind (fn-cnode-config-replay configs)) :ok)
    :rule-classes nil
    :hints (("Goal" :do-not-induct t
             :in-theory (disable fn-cnode-config-replay))))))

; The refinement is strict.  The recovered journal with its two records'
; transaction ids made to go down: the configuration-only replay, which
; never reads a transaction id, accepts it; the called replay refuses it
; (:config-txid).  `fn-cpo-configure-durable' writes a record only at the
; Store frontier and only when the called replay of the result is :ok, so
; the called path does not produce this journal.
(defconst *ccr-descending*
  (list (fn-cfg-record-make 0 9 (fn-cfg-record-generation (car *ccr-h*))
                            (fn-cfg-record-change (car *ccr-h*))
                            (fn-cfg-record-stamp (car *ccr-h*)))
        (fn-cfg-record-make 1 7 (fn-cfg-record-generation (cadr *ccr-h*))
                            (fn-cfg-record-change (cadr *ccr-h*))
                            (fn-cfg-record-stamp (cadr *ccr-h*)))))
(assert-event (equal (fn-replay-result-kind (fn-cnode-config-replay *ccr-descending*)) :ok))
(assert-event (equal (fn-replay-result-kind (fn-cpr-replay *ccr-descending* nil)) :fault))
(assert-event (equal (fn-replay-result-reason (fn-cpr-replay *ccr-descending* nil))
                     :config-txid))
(local
 (must-fail
  (defthm fn-ocl-config-replay-ok-is-cpr-replay-ok-is-false
    (implies (equal (fn-replay-result-kind (fn-cnode-config-replay configs)) :ok)
             (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok))
    :rule-classes nil
    :hints (("Goal" :do-not-induct t
             :in-theory (disable fn-cnode-config-replay fn-cpr-replay))))))
