; Teeth for books/bp-node-rotation-codec's publication keystones (PRF-1039):
; the loop the host follows (host/native/bp-service.lisp
; fnn-bps-publish-generation) run over concrete result sequences.
(in-package "ACL2")
(include-book "../../books/bp-node-rotation-codec")
(include-book "must-fail-checked")

(defun bprc-end (results)
  (fn-bpnr-publish-run :directory results))

(defun bprc-keystone-holds (results)
  (let ((end (bprc-end results)))
    (and (iff (equal (fn-bpnr-publish-outcome end) :pending)
              (not (equal (fn-bpnr-publish-action end) :done)))
         (implies (equal (fn-bpnr-publish-action end) :done)
                  (member-equal (fn-bpnr-publish-outcome end)
                                '(:durable :refused :uncertain))))))

;; KEYSTONE fn-bpnr-publish-outcome-is-pending-exactly-while-the-loop-runs.
;; Reachable positive witnesses, the complete antecedent and conclusion: four
;; :ok results from :directory stop the loop at :idle and report :durable (so
;; does a transient :error at the stage, retried in place); a refused
;; directory, or a :known-fail at the stage, stops it at :refused; an :error
;; at the replace stops it at :fenced-marker and reports :uncertain; two :ok
;; results leave the loop running (:marker-attempted, action
;; :directory-barrier) and the outcome :pending.
(assert-event
 (and (equal (bprc-end '(:ok :ok :ok :ok)) :idle)
      (equal (fn-bpnr-publish-action :idle) :done)
      (equal (fn-bpnr-publish-outcome :idle) :durable)
      (bprc-keystone-holds '(:ok :ok :ok :ok))
      (equal (bprc-end '(:ok :error :ok :ok :ok)) :idle)
      (bprc-keystone-holds '(:ok :error :ok :ok :ok))
      (equal (bprc-end '(:error)) :refused)
      (equal (fn-bpnr-publish-outcome :refused) :refused)
      (bprc-keystone-holds '(:error))
      (equal (bprc-end '(:ok :known-fail)) :refused)
      (bprc-keystone-holds '(:ok :known-fail))
      (equal (bprc-end '(:ok :ok :error)) :fenced-marker)
      (equal (fn-bpnr-publish-outcome :fenced-marker) :uncertain)
      (bprc-keystone-holds '(:ok :ok :error))
      (equal (bprc-end '(:ok :ok)) :marker-attempted)
      (equal (fn-bpnr-publish-action :marker-attempted) :directory-barrier)
      (equal (fn-bpnr-publish-outcome :marker-attempted) :pending)
      (bprc-keystone-holds '(:ok :ok))))

;; Tooth, hypothesis "the loop starts at :directory" (the run's fixed start,
;; the only hypothesis): a loop started at a phase the machine never holds
;; has stopped (its action is :done) yet reports :pending; the first side
;; fails.
(assert-event
 (and (not (fn-bpnr-publish-phasep :bogus))
      (equal (fn-bpnr-publish-action (fn-bpnr-publish-run :bogus '(:ok))) :done)
      (equal (fn-bpnr-publish-outcome (fn-bpnr-publish-run :bogus '(:ok)))
             :pending)))
(must-fail-checked
 (assert-event
  (let ((end (fn-bpnr-publish-run :bogus '(:ok))))
    (iff (equal (fn-bpnr-publish-outcome end) :pending)
         (not (equal (fn-bpnr-publish-action end) :done))))))

;; KEYSTONE fn-bpnr-publish-outcome-names-the-stopped-phase.  Reachable
;; positive witness: the three stopped runs report three distinct outcomes,
;; and two runs that stop at :idle by different result sequences report the
;; same one.
(assert-event
 (let ((durable (bprc-end '(:ok :ok :ok :ok)))
       (refused (bprc-end '(:error)))
       (uncertain (bprc-end '(:ok :ok :error)))
       (durable2 (bprc-end '(:ok :error :ok :ok :ok))))
   (and (equal (fn-bpnr-publish-action durable) :done)
        (equal (fn-bpnr-publish-action refused) :done)
        (equal (fn-bpnr-publish-action uncertain) :done)
        (equal (fn-bpnr-publish-action durable2) :done)
        (not (equal (fn-bpnr-publish-outcome durable)
                    (fn-bpnr-publish-outcome refused)))
        (not (equal (fn-bpnr-publish-outcome durable)
                    (fn-bpnr-publish-outcome uncertain)))
        (not (equal (fn-bpnr-publish-outcome refused)
                    (fn-bpnr-publish-outcome uncertain)))
        (equal durable durable2)
        (equal (fn-bpnr-publish-outcome durable)
               (fn-bpnr-publish-outcome durable2)))))

;; Tooth, hypothesis "both loops stopped": two loops from :directory still
;; running at different phases (:marker-staged after one :ok, :marker-attempted
;; after two) share the outcome :pending; the iff fails.
(assert-event
 (and (equal (bprc-end '(:ok)) :marker-staged)
      (equal (bprc-end '(:ok :ok)) :marker-attempted)
      (not (equal (fn-bpnr-publish-action (bprc-end '(:ok))) :done))
      (not (equal (fn-bpnr-publish-action (bprc-end '(:ok :ok))) :done))))
(must-fail-checked
 (assert-event
  (let ((end1 (bprc-end '(:ok)))
        (end2 (bprc-end '(:ok :ok))))
    (iff (equal (fn-bpnr-publish-outcome end1) (fn-bpnr-publish-outcome end2))
         (equal end1 end2)))))
