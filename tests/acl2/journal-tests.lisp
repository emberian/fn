; Executable crash and recovery scenarios for the isolated-slot journal.
(in-package "ACL2")
(include-book "../../books/journal")

; Transaction 0 stages two identified objects, barriers them, appends its
; complete marker, then barriers the marker.  Only after this point can a host
; record a durable acknowledgement anchor and emit success.
(defconst *journal-staged*
  (fn-journal-stage-object
   (fn-journal-stage-object nil 0 11) 0 12))
(assert-event (fn-journal-live-listp *journal-staged*))

(defconst *journal-objects-durable* (fn-journal-barrier *journal-staged*))
(assert-event (fn-journal-durable-referencesp 0 '(11 12)
                                                *journal-objects-durable*))

(defconst *journal-marker-staged*
  (fn-journal-stage-commit *journal-objects-durable* 0 '(11 12)))
(assert-event (equal (fn-journal-live-durability
                      (car (last *journal-marker-staged*)))
                     :volatile))

(defconst *journal-acked-live* (fn-journal-barrier *journal-marker-staged*))
(assert-event (fn-journal-durable-commitp 0 *journal-acked-live*))
(assert-event (equal (fn-journal-completion-action *journal-acked-live* 0 :durable)
                     :acknowledge))
(assert-event (equal (fn-journal-completion-action *journal-marker-staged* 0 :durable)
                     :ignore))
(assert-event (equal (fn-journal-completion-action *journal-marker-staged* 0 :aborted)
                     :known-abort))
(assert-event (equal (fn-journal-completion-action *journal-marker-staged* 0 :indeterminate)
                     :recover))

; There are no outstanding writes after the second barrier.  Any supplied
; volatile-choice list is irrelevant, and recovery uses only the physical image
; plus anchor 0.  The acknowledged whole transaction survives.
(defconst *journal-acked-image* (fn-journal-crash *journal-acked-live* nil))
(assert-event
 (equal (fn-journal-recover *journal-acked-image* 0)
        (fn-journal-result-ok '(0))))

; A complete marker can reach media during a failed/indeterminate final barrier
; before its success reply.  Recovery may accept this unacknowledged transaction.
(defconst *journal-unacked-image*
  (fn-journal-crash *journal-marker-staged* '(:intact)))
(assert-event
 (equal (fn-journal-recover *journal-unacked-image* :none)
        (fn-journal-result-ok '(0))))

; Every subset of the two outstanding object writes is explored.  No marker is
; present, so incomplete work never publishes even when slots survive reordered.
(defconst *journal-incomplete-matrix*
  (fn-journal-recover-matrix (fn-journal-crash-matrix *journal-staged*) :none))
(assert-event (equal (len *journal-incomplete-matrix*) 4))
(assert-event (fn-journal-no-published-txsp *journal-incomplete-matrix*))

; A later commit after a lost/torn dependency cannot be accepted: the scanner
; either sees the missing dependency or the transaction-number gap and faults.
(assert-event
 (equal (fn-journal-recover
         (list (fn-journal-make-physical-object 0 11 :torn)
               (fn-journal-make-physical-commit 0 '(11) :intact))
         :none)
        (fn-journal-result-fault :missing-dependency)))
(assert-event
 (equal (fn-journal-recover
         (list (fn-journal-make-physical-commit 1 nil :intact))
         :none)
        (fn-journal-result-fault :commit-gap)))

; A damaged formerly acknowledged marker is not silently truncated: the durable
; anchor makes recovery report a repair/degraded path.
(assert-event
 (equal (fn-journal-recover
         (list (fn-journal-make-physical-object 0 11 :intact)
               (fn-journal-make-physical-object 0 12 :intact)
               (fn-journal-make-physical-commit 0 '(11 12) :torn))
         0)
        (fn-journal-result-fault :ack-gap)))

; Duplicate intact object bindings are detectable corruption, not a silently
; chosen "latest" value.
(assert-event
 (equal (fn-journal-recover
         (list (fn-journal-make-physical-object 0 11 :intact)
               (fn-journal-make-physical-object 0 11 :intact))
         :none)
        (fn-journal-result-fault :object-conflict)))
