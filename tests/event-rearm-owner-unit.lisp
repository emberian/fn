; UNEXECUTED actual-accessor source controls for the requester/publisher bridge.
; Completed writer/publication rows below are explicitly typed test state, not
; a full publication, physical completion, fence or rearm-success witness.
; This book requires the real assembly's writer + event-rearm materialization.
(in-package "ACL2")
(include-book "c-snapshot-unit")
(include-book "../books/event-rearm")

(defun fn2-event-rearm-owner-body (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-csu-profile* fn2-core))
      (writer-id (fn2-machine-kind-base *fn2-checkpoint-writer-kind* fn2-core))
      (requester (fn2-machine-kind-base *fn2-scribe-kind* fn2-core))
      ((unless (and (fn2-machine-idp writer-id fn2-core) (fn2-machine-idp requester fn2-core)
                     (not (equal writer-id requester)))) (mv nil fn2-core))
      (requestgen (fn2-machine-generation requester fn2-core)))
  (stobj-let ((fn2-checkpoint-writer (fn2-checkpoint-writer-table fn2-core))
              (fn2-checkpoint-publication (fn2-core-checkpoint-publication fn2-core))
              (fn2-machines (fn2-core-machines fn2-core)))
   (answer fn2-checkpoint-writer fn2-checkpoint-publication)
   (b* ((generation (fn2-checkpoint-writer-generation 0 fn2-checkpoint-writer))
        (fn2-checkpoint-writer (fn2-checkpoint-writer-put 0
         (phase *fn2-checkpoint-writer-state-done*) (pending 0) (stopped 0)
         (candidate 0) (request-token 5) (requester-kind *fn2-scribe-kind*)
         (requester-slot requester) (requester-gen requestgen)))
        (fn2-checkpoint-publication (fn2-checkpoint-publication-put 0
         (candidate 0) (owner-kind *fn2-checkpoint-writer-kind*)
         (owner-slot writer-id) (owner-gen generation)))
        (distinct-positive (and (not (equal *fn2-scribe-kind* *fn2-checkpoint-writer-kind*))
          (fn2-event-producer-writer-request-p 0 5 *fn2-scribe-kind* requester requestgen fn2-checkpoint-writer fn2-checkpoint-publication fn2-machines)))
        (stale-token (not (fn2-event-producer-writer-request-p 0 6 *fn2-scribe-kind* requester requestgen fn2-checkpoint-writer fn2-checkpoint-publication fn2-machines)))
        (stale-requester (not (fn2-event-producer-writer-request-p 0 5 *fn2-scribe-kind* requester (+ 1 requestgen) fn2-checkpoint-writer fn2-checkpoint-publication fn2-machines)))
        (fn2-checkpoint-publication (fn2-checkpoint-publication-set-owner-gen 0 (+ 1 generation) fn2-checkpoint-publication))
        (stale-physical (not (fn2-event-producer-writer-request-p 0 5 *fn2-scribe-kind* requester requestgen fn2-checkpoint-writer fn2-checkpoint-publication fn2-machines)))
        (fn2-checkpoint-publication (fn2-checkpoint-publication-put 0
         (owner-kind *fn2-scribe-kind*) (owner-slot requester) (owner-gen requestgen)))
        (conflated-refused (not (fn2-event-producer-writer-request-p 0 5 *fn2-scribe-kind* requester requestgen fn2-checkpoint-writer fn2-checkpoint-publication fn2-machines))))
    (mv (and distinct-positive stale-token stale-requester stale-physical conflated-refused)
        fn2-checkpoint-writer fn2-checkpoint-publication))
   (mv answer fn2-core))))
(defun fn2-event-rearm-owner-test ()
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core) (fn2-event-rearm-owner-body fn2-core) answer)))
(assert-event (fn2-event-rearm-owner-test))
