; Teeth for the maintained Store journal sequence relation.
(in-package "ACL2")
(include-book "../../books/store-identity-sequence-invariants")
(include-book "store-identity-traces-tests")
(include-book "std/testing/must-fail" :dir :system)

; Nondegenerate reached states cover ordinary ready history, the actual
; record-directory off-by-one window, a burned allocator txid, and completion.
(defconst *sis-before-enrollment* (fn-sn-initial *sit-groups* 32))
(defconst *sis-reserved* (fn-sit-reserve *sis-before-enrollment*))
(defconst *sis-staged*
  (fn-sn-prepare-identity *sis-reserved* *sit-enrollment*))
(defconst *sis-completing* (fn-sit-publish *sis-staged*))

(assert-event (fn-sn-identity-sequencep *sis-before-enrollment*))
(assert-event (fn-sn-identity-sequencep *sis-reserved*))
(assert-event (fn-sn-identity-sequencep *sis-completing*))

; The reached staged enrollment has a typed candidate at the carried next
; sequence.  Each premise matters: a moved cursor, an invalid candidate, or
; a merely reserved Store state cannot support that conclusion.
(assert-event (fn-sn-statep *sis-staged*))
(assert-event (fn-sn-identity-sequencep *sis-staged*))
(assert-event (fn-sf-record-phasep (fn-sf-phase (fn-sn-files *sis-staged*))))
(assert-event
 (and (fn-store-event-p (fn-sf-record-candidate (fn-sn-files *sis-staged*)))
      (equal (fn-store-event-sequence
              (fn-sf-record-candidate (fn-sn-files *sis-staged*)))
             (fn-sn-identity-next *sis-staged*))))
(defconst *sis-candidate-bad-next*
  (update-nth 9 (1+ (fn-sn-identity-next *sis-staged*)) *sis-staged*))
(assert-event (fn-sn-statep *sis-candidate-bad-next*))
(assert-event (not (fn-sn-identity-sequencep *sis-candidate-bad-next*)))
(must-fail
 (assert-event
  (equal (fn-store-event-sequence
          (fn-sf-record-candidate (fn-sn-files *sis-candidate-bad-next*)))
         (fn-sn-identity-next *sis-candidate-bad-next*))))
(defconst *sis-candidate-malformed*
  (update-nth 2
              (update-nth 5 nil (fn-sn-files *sis-staged*))
              *sis-staged*))
(assert-event (not (fn-sn-statep *sis-candidate-malformed*)))
(assert-event
 (equal (len (fn-sf-records (fn-sn-files *sis-candidate-malformed*)))
        (fn-sn-identity-next *sis-candidate-malformed*)))
(must-fail
 (assert-event
  (fn-store-event-p
   (fn-sf-record-candidate (fn-sn-files *sis-candidate-malformed*)))))
(assert-event (fn-sn-statep *sis-reserved*))
(assert-event (fn-sn-identity-sequencep *sis-reserved*))
(must-fail
 (assert-event
  (fn-store-event-p (fn-sf-record-candidate (fn-sn-files *sis-reserved*)))))
(assert-event
 (equal (len (fn-sf-records (fn-sn-files *sis-completing*)))
        (1+ (fn-sn-identity-next *sis-completing*))))
(assert-event (fn-sn-identity-sequencep *sit-after-enrollment*))
(assert-event (fn-sn-identity-sequencep *sit-refused*))
(assert-event (> (fn-sf-frontier (fn-sn-files *sit-refused*))
                 (fn-sn-identity-next *sit-refused*)))
(assert-event (fn-sn-identity-sequencep *sit-finished*))
(assert-event (fn-sn-identity-sequencep *sit-recovered*))

; The relation hypothesis has teeth.  Keep every field of the reachable
; completing state but move its carried cursor forward: finish still runs, yet
; the post-state record count and cursor disagree.
(defconst *sis-bad-completing*
  (fn-sn-make-v2
   (fn-sn-groups *sis-completing*) (fn-sn-capacity *sis-completing*)
   (fn-sn-files *sis-completing*) (fn-sn-node *sis-completing*)
   (fn-sn-keyring *sis-completing*) (fn-sn-index *sis-completing*)
   (fn-sn-keyring-generation *sis-completing*)
   (fn-sn-verdicts *sis-completing*)
   (fn-sn-keyring-snapshots *sis-completing*)
   (1+ (fn-sn-identity-next *sis-completing*))))

(assert-event (fn-sn-statep *sis-bad-completing*))
(assert-event (not (fn-sn-identity-sequencep *sis-bad-completing*)))
(assert-event
 (not (fn-sn-identity-sequencep
       (fn-sn-refuse-reservation *sis-bad-completing* 0))))
(assert-event
 (not (fn-sn-identity-sequencep
       (fn-sn-prepare *sis-bad-completing* *sit-signed-record*))))
(assert-event
 (not (fn-sn-identity-sequencep
       (fn-sn-prepare-retention *sis-bad-completing* *sit-retention*))))
(assert-event
 (not (fn-sn-identity-sequencep
       (fn-sn-prepare-identity *sis-bad-completing* *sit-enrollment*))))
(assert-event
 (not (fn-sn-identity-sequencep (fn-sn-known-abort *sis-bad-completing*))))
(assert-event
 (not (fn-sn-identity-sequencep
       (fn-sn-io *sis-bad-completing* :record-file :ok))))
(assert-event
 (not (fn-sn-identity-sequencep (fn-sn-recover *sis-bad-completing*))))
(assert-event
 (not (fn-sn-identity-sequencep (fn-sn-finish *sis-bad-completing*))))

; Dropping the input sequence relation from the finish theorem is false even
; for a well-shaped state whose completing event is still consumed.
(must-fail
 (assert-event
  (fn-sn-identity-sequencep (fn-sn-finish *sis-bad-completing*))))
