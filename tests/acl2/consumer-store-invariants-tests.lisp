; Reachable E2 Store prefix witnesses through the actual decoded dispatcher,
; including a linked-but-unfinished acknowledgement and both crash images.
(in-package "ACL2")
(include-book "../../books/consumer-store-invariants")
(include-book "consumer-store-node-tests")
(include-book "std/testing/must-fail" :dir :system)

(assert-event (fn-csi-completed-prefixp *csnt-initial*))
(assert-event (fn-csi-completed-prefixp *csnt-after-boot*))
(assert-event (fn-csi-completed-prefixp *csnt-after-reg*))
(assert-event (fn-csi-completed-prefixp *csnt-staged-ack*))
(assert-event (fn-csi-completed-prefixp
               (csnt-publish *csnt-staged-ack*)))
(assert-event (fn-csi-completed-prefixp *csnt-after-ack*))
(assert-event (fn-csi-livep *csnt-after-ack*))
(assert-event (fn-csi-full-relationp *csnt-initial*))
(assert-event (fn-csi-full-relationp *csnt-after-ack*))
(assert-event (fn-csi-livep (csnt-publish *csnt-staged-ack*)))
(assert-event
 (fn-csi-completion-lastp (csnt-publish *csnt-staged-ack*)))
(assert-event (fn-csi-completed-prefixp
               (fn-sn-recover
                (fn-sn-crash *csnt-after-ack* :old :absent))))

; The named dispatcher, rather than a sibling helper, executes a reachable
; bootstrap publication through every file boundary and durable finish.
(defconst *csit-boot-trace*
  (list '(:io :start-frontier nil)
        '(:io :frontier-file :ok)
        '(:io :frontier-replace :ok)
        '(:io :frontier-directory :ok)
        (list :prepare-consumer *csnt-boot*)
        '(:io :record-file :ok)
        '(:io :record-link :ok)
        '(:io :record-directory :ok)
        '(:finish)))
(assert-event (fn-csi-no-crash-eventsp *csit-boot-trace*))
(assert-event (equal (fn-snrt-run *csnt-initial* *csit-boot-trace*)
                     *csnt-after-boot*))
(assert-event (fn-csi-livep
               (fn-snrt-run *csnt-initial* *csit-boot-trace*)))
(assert-event
 (equal (fn-cpe-projection-replay
         nil (fn-sf-records
              (fn-sn-files
               (fn-snrt-run *csnt-initial* *csit-boot-trace*))) 0)
        (list :ok
              (fn-sn-consumer
               (fn-snrt-run *csnt-initial* *csit-boot-trace*)))))

(defconst *csit-linked-ack*
  (fn-snrt-run *csnt-staged-ack*
               '((:io :record-file :ok) (:io :record-link :ok))))
(assert-event (fn-csi-full-relationp *csit-linked-ack*))
(defconst *csit-linked-absent*
  (fn-snrt-run *csit-linked-ack*
               '((:crash :old :absent) (:recover))))
(defconst *csit-linked-present*
  (fn-snrt-run *csit-linked-ack*
               '((:crash :new :present) (:recover))))
(assert-event (fn-csi-full-relationp *csit-linked-absent*))
(assert-event (fn-csi-full-relationp *csit-linked-present*))
(assert-event (equal (fn-sn-consumer *csit-linked-absent*)
                     (fn-sn-consumer *csnt-after-reg*)))
(assert-event (equal (fn-sn-consumer *csit-linked-present*)
                     (fn-sn-consumer *csnt-after-ack*)))

; Replacing the carried projection after a published registration leaves a
; well-shaped Store node but makes the completed prefix unequal to replay.
(defconst *csit-corrupt-projection*
  (fn-sn-with-consumer *csnt-after-reg* nil))
(assert-event (fn-sn-statep *csit-corrupt-projection*))
(assert-event (not (fn-csi-completed-prefixp *csit-corrupt-projection*)))
(assert-event (not (fn-csi-livep *csit-corrupt-projection*)))
(assert-event (not (fn-csi-full-relationp *csit-corrupt-projection*)))
(must-fail (assert-event
            (fn-csi-completed-prefixp *csit-corrupt-projection*)))
(must-fail
 (assert-event
  (fn-csi-full-relationp
   (fn-snrt-step *csit-corrupt-projection* '(:io :unknown nil)))))
(must-fail
 (assert-event
  (fn-csi-livep
   (fn-snrt-step *csnt-after-boot* '(:crash :old :absent)))))

; A linked acknowledgement with a lost consumer projection has no enabled
; completion.  It cannot append a success while retaining stale progress.
(assert-event (not (fn-csi-completed-prefixp *csnt-bad-completion*)))
(assert-event (equal (fn-sn-finish *csnt-bad-completion*)
                     *csnt-bad-completion*))

; K4's recovery-image bridge includes the linked record, the current prefix,
; and the one-record rollback during recovery.  The old registration below
; is structurally framed at sequence zero but has no bootstrap; the file
; predicate alone therefore cannot establish the strict consumer replay.
(assert-event
 (fn-sn-observed-consumer-okp
  (fn-sf-records (fn-sn-files *csnt-after-reg*))))
(assert-event
 (fn-sn-observed-consumer-okp
  (fn-sf-but-last (fn-sf-records (fn-sn-files *csnt-after-reg*)))))
(assert-event
 (fn-sf-recovery-crash-imagep
  (fn-sn-files *csit-linked-ack*)
  (fn-sf-frontier (fn-sn-files *csit-linked-ack*))
  (fn-sf-records (fn-sn-files *csit-linked-ack*))))
(assert-event
 (fn-sn-observed-consumer-okp
  (fn-sf-records (fn-sn-files *csit-linked-ack*))))
(defconst *csit-register-before-bootstrap*
  (fn-cpe-make 0 0 0 '(:register (3) (4) (5) 1 1 1)))
(defconst *csit-invalid-consumer-history*
  (update-nth
   2 (fn-sf-make :ready 1 nil
                 (list *csit-register-before-bootstrap*)
                 nil nil nil *fn-sf-recovery-barrier-count*)
   *csnt-after-boot*))
(assert-event
 (fn-sf-recovery-crash-imagep
  (fn-sn-files *csit-invalid-consumer-history*) 1
  (list *csit-register-before-bootstrap*)))
(assert-event (not (fn-csi-full-relationp *csit-invalid-consumer-history*)))
(assert-event
 (not (fn-sn-observed-consumer-okp
       (list *csit-register-before-bootstrap*))))
(must-fail
 (assert-event
  (fn-sn-observed-consumer-okp
   (list *csit-register-before-bootstrap*))))
