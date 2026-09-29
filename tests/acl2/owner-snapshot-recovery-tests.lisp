; PRF-1068 reachable witnesses name complete literal antecedents/conclusions.
(in-package "ACL2")
(include-book "../../books/owner-snapshot-recovery")
(include-book "config-observed-tests")
(include-book "consumer-store-invariants-tests")

; Startup uses the actual configured observed opener on a historical capacity
; decrease that cannot be replayed under only the final capacity.
(assert-event
 (and (true-listp *cpo-t-configs*)
      (fn-sn-open-okp (fn-cpo-open-observed *cpo-t-configs* 8 *cpo-t-events*))
      (fn-osr-livep
       (fn-sn-open-state
        (fn-cpo-open-observed *cpo-t-configs* 8 *cpo-t-events*)))))

; All three recovery barriers and two real live configuration publications.
(assert-event
 (and (fn-osr-livep *cpo-t-ready*)
      (equal (fn-sf-phase (fn-sn-files *cpo-t-ready*)) :ready)
      (fn-sn-open-okp
       (fn-cpo-open-observed
        (fn-sn-config-history (fn-osr-capture *cpo-t-ready*))
        (fn-sf-frontier (fn-sn-files (fn-osr-capture *cpo-t-ready*)))
        (fn-sf-records (fn-sn-files (fn-osr-capture *cpo-t-ready*)))))))
(assert-event
 (and (fn-osr-livep *cpo-t-ready*)
      (fn-osr-livep (fn-cpo-configure-durable *cpo-t-ready* *cpo-t-increase*))
      (equal (fn-sn-capacity *cpo-t-live*) 20)))
(assert-event
 (and (fn-osr-livep *cpo-t-live*)
      (fn-osr-livep (fn-cpo-configure-durable *cpo-t-live* *cpo-t-create*))
      (member-equal "fn.live" (fn-sn-groups *cpo-t-live-domain*))))

; A genuine bootstrap, registration and acknowledgement use actual Store
; transitions. No theorem is tested only at an unchanged/no-op state.
(assert-event
 (and (fn-osr-independent-livep *csnt-initial*)
      (fn-csi-no-crash-eventsp *csit-boot-trace*)
      (fn-osr-independent-livep (fn-snrt-run *csnt-initial* *csit-boot-trace*))
      (equal (fn-snrt-run *csnt-initial* *csit-boot-trace*) *csnt-after-boot*)))
(assert-event
 (and (fn-osr-identity-prefixp *csnt-staged-ack*)
      (fn-csi-livep *csnt-staged-ack*)
      (fn-osr-identity-prefixp (fn-sn-finish *csnt-staged-ack*))))
(assert-event
 (and (fn-osr-identity-prefixp (csnt-publish *csnt-staged-ack*))
      (fn-csi-livep (csnt-publish *csnt-staged-ack*))
      (fn-sn-completion-enabledp (csnt-publish *csnt-staged-ack*))
      (fn-osr-identity-prefixp
       (fn-sn-finish (csnt-publish *csnt-staged-ack*)))
      (equal (fn-sn-finish (csnt-publish *csnt-staged-ack*)) *csnt-after-ack*)))

; Corrupted-state teeth: each carried projection detects an actual mutation.
; These are not represented as hypothesis-removal counterexamples.
(defconst *osr-wrong-identity-bound* (update-nth 9 3 *cpo-t-ready*))
(assert-event
 (and (fn-sn-statep *osr-wrong-identity-bound*)
      (not (fn-osr-identity-prefixp *osr-wrong-identity-bound*))
      (not (fn-osr-livep *osr-wrong-identity-bound*))))
(assert-event
 (and (fn-sn-statep *csit-corrupt-projection*)
      (not (fn-csi-livep *csit-corrupt-projection*))
      (not (fn-osr-independent-livep *csit-corrupt-projection*))))
(defconst *osr-wrong-topic*
  (fn-sn-with-topic *cpo-t-ready*
                    (fn-th-prefix-state :ok 9 nil nil nil nil nil)))
(assert-event
 (and (fn-sn-statep *osr-wrong-topic*)
      (fn-csi-livep *osr-wrong-topic*)
      (fn-osr-identity-prefixp *osr-wrong-topic*)
      (not (fn-sti-livep *osr-wrong-topic*))
      (not (fn-osr-livep *osr-wrong-topic*))))

(defconst *osr-captured-open*
  (fn-sn-open-state
   (fn-cpo-open-observed (fn-sn-config-history (fn-osr-capture *cpo-t-live-domain*))
                        (fn-sf-frontier (fn-sn-files (fn-osr-capture *cpo-t-live-domain*)))
                        (fn-sf-records (fn-sn-files (fn-osr-capture *cpo-t-live-domain*))))))
(assert-event
 (and (fn-osr-livep *cpo-t-live-domain*)
      (equal (fn-sf-phase (fn-sn-files *cpo-t-live-domain*)) :ready)
      (equal (fn-sn-node *osr-captured-open*) (fn-sn-node *cpo-t-live-domain*))
      (equal (fn-sn-groups *osr-captured-open*) (fn-sn-groups *cpo-t-live-domain*))
      (equal (fn-sn-capacity *osr-captured-open*) (fn-sn-capacity *cpo-t-live-domain*))
      (equal (fn-sn-config-history *osr-captured-open*) (fn-sn-config-history *cpo-t-live-domain*))
      (equal (fn-sf-frontier (fn-sn-files *osr-captured-open*))
             (fn-sf-frontier (fn-sn-files *cpo-t-live-domain*)))
      (equal (fn-sf-records (fn-sn-files *osr-captured-open*))
             (fn-sf-records (fn-sn-files *cpo-t-live-domain*)))
      (equal (fn-sn-identity-next *osr-captured-open*) (fn-sn-identity-next *cpo-t-live-domain*))
      (equal (fn-sn-keyring-snapshots *osr-captured-open*) (fn-sn-keyring-snapshots *cpo-t-live-domain*))
      (equal (fn-sn-consumer *osr-captured-open*) (fn-sn-consumer *cpo-t-live-domain*))
      (equal (fn-sn-topic *osr-captured-open*) (fn-sn-topic *cpo-t-live-domain*))))

; Hypothesis removal: retain the exact ready premise, omit the complete live
; carry; the actual capture then fails configured open (no initialized config).
(defconst *osr-unconfigured* (fn-sn-initial nil 4))
(assert-event
 (and (equal (fn-sf-phase (fn-sn-files *osr-unconfigured*)) :ready)
      (not (fn-osr-livep *osr-unconfigured*))
      (not (fn-sn-open-okp
            (fn-cpo-open-observed
             (fn-sn-config-history (fn-osr-capture *osr-unconfigured*))
             (fn-sf-frontier (fn-sn-files (fn-osr-capture *osr-unconfigured*)))
             (fn-sf-records (fn-sn-files (fn-osr-capture *osr-unconfigured*))))))))

; Hypothesis removal for mixed trace preservation: omit only no-crash.
(assert-event
 (and (fn-osr-independent-livep *csnt-after-boot*)
      (not (fn-csi-no-crash-eventsp '((:crash :old :absent))))
      (not (fn-osr-independent-livep
            (fn-snrt-run *csnt-after-boot* '((:crash :old :absent)))))))
; Its other antecedent is independently material (corrupted-state removal).
(assert-event
 (and (fn-csi-no-crash-eventsp '((:io :unknown nil)))
      (not (fn-osr-independent-livep *csit-corrupt-projection*))
      (not (fn-osr-independent-livep
            (fn-snrt-run *csit-corrupt-projection* '((:io :unknown nil)))))))

; Identity-prefix removal retains the actual consumer-live antecedent.
(defconst *osr-wrong-snapshots*
  (update-nth 8 (list (fn-stxk-make 0 0 0 1 '(111) '(1))) *cpo-t-ready*))
(assert-event
 (and (fn-csi-livep *osr-wrong-snapshots*)
      (not (fn-osr-identity-prefixp *osr-wrong-snapshots*))
      (not (fn-osr-identity-prefixp (fn-sn-finish *osr-wrong-snapshots*)))))

; Full-carry completion witness starts at actual configured recovery, traverses
; all recovery barriers, reserves and publishes a consumer acknowledgement.
(defconst *osr-ack-base-open*
  (fn-cpo-open-observed (list *fn-cfg-default-record* *csnt-tied-config*)
                       2 (list *csnt-boot* *csnt-reg*)))
(defconst *osr-ack-base*
  (fn-snrt-run (fn-sn-open-state *osr-ack-base-open*)
               '((:io :recovery-barrier :ok)
                 (:io :recovery-barrier :ok)
                 (:io :recovery-barrier :ok))))
(defconst *osr-ack-completing*
  (csnt-publish (fn-sn-prepare-consumer (csnt-reserve *osr-ack-base*) *csnt-ack*)))
(assert-event
 (and (fn-sn-open-okp *osr-ack-base-open*)
      (fn-osr-livep *osr-ack-base*)
      (fn-osr-livep *osr-ack-completing*)
      (fn-sn-completion-enabledp *osr-ack-completing*)
      (fn-osr-livep (fn-sn-finish *osr-ack-completing*))
      (equal (fn-sf-phase (fn-sn-files (fn-sn-finish *osr-ack-completing*))) :ready)
      (equal (fn-sn-consumer (fn-sn-finish *osr-ack-completing*))
             (fn-sn-consumer *csnt-after-ack*))))

; The weakened opening theorem works during a real in-flight completion.
(assert-event
 (and (fn-osr-livep *osr-ack-completing*)
      (equal (fn-sf-phase (fn-sn-files *osr-ack-completing*)) :completing)
      (fn-sn-open-okp
       (fn-cpo-open-observed
        (fn-sn-config-history (fn-osr-capture *osr-ack-completing*))
        (fn-sf-frontier (fn-sn-files (fn-osr-capture *osr-ack-completing*)))
        (fn-sf-records (fn-sn-files (fn-osr-capture *osr-ack-completing*)))))))

; Hypothesis removal for source/target projection equality: retain live carry,
; omit readiness. Reservation burns a frontier position while the source node
; stays before it; recovery advances that coordinate and equality fails.
(defconst *osr-ack-reserved* (csnt-reserve *osr-ack-base*))
(defconst *osr-ack-reserved-open*
  (fn-sn-open-state
   (fn-cpo-open-observed
    (fn-sn-config-history (fn-osr-capture *osr-ack-reserved*))
    (fn-sf-frontier (fn-sn-files (fn-osr-capture *osr-ack-reserved*)))
    (fn-sf-records (fn-sn-files (fn-osr-capture *osr-ack-reserved*))))))
(assert-event
 (and (fn-osr-livep *osr-ack-reserved*)
      (not (equal (fn-sf-phase (fn-sn-files *osr-ack-reserved*)) :ready))
      (not (equal (fn-sn-node *osr-ack-reserved-open*)
                  (fn-sn-node *osr-ack-reserved*)))))
