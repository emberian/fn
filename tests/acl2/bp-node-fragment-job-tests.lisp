; Teeth for books/bp-node-fragment-job.lisp (PRF-250 hosted, Q4a): the
; reassembly job stepped across scheduling steps reads as the foundation's
; whole reassembly, and the profile's limit refuses an image by name.
(in-package "ACL2")
(include-book "../../books/bp-node-fragment-job")
(include-book "../../books/bp-node-profile")
(include-book "bp-node-fragment-plan-tests")
(include-book "bp-fragment-resume-tests")

; The job started from the family the plan tests call :ready.
(defconst *bpfjt-job0* (fn-bpfj-start *bpnff-state* *bpnff-p3*))
(assert-event (fn-bpfj-wf *bpnff-state* *bpnff-p3* *bpfjt-job0*))
(assert-event (not (fn-bpfj-finishedp *bpfjt-job0*)))
; An unfinished job is named, never planned.
(assert-event (equal (fn-bpfj-query *bpnff-state* *bpnff-p3* *bpfjt-job0*)
                     '(:pending :job)))
(assert-event (equal (fn-bpfj-plan *bpnff-state* *bpnff-p3* *bpfjt-job0*
                                   *fn-bpnf-max-held-image*)
                     '(:pending :job)))

; One step of quantum 1 consumes one position and keeps the invariant
; (fn-bpfj-step-is-bounded, fn-bpfj-step-preserves-wf).
(defconst *bpfjt-job1* (fn-bpfj-step *bpfjt-job0* 1))
(assert-event (fn-bpfj-wf *bpnff-state* *bpnff-p3* *bpfjt-job1*))
(assert-event (equal (nth 3 (fn-bpfj-job-sweep *bpfjt-job1*))
                     (- (nth 3 (fn-bpfj-job-sweep *bpfjt-job0*)) 1)))
(assert-event (not (fn-bpfj-finishedp *bpfjt-job1*)))

; Steps of quantum 4 from there, to completion (the host's schedule).
(defconst *bpfjt-done*
  (fn-bpfj-job (fn-bpfj-job-cells *bpfjt-job1*) (fn-bpfj-job-total *bpfjt-job1*)
               (fn-bpfr-run (fn-bpfj-job-sweep *bpfjt-job1*) 4)))
(assert-event (fn-bpfj-finishedp *bpfjt-done*))
(assert-event (fn-bpfj-wf *bpnff-state* *bpnff-p3* *bpfjt-done*))

; KEYSTONE fn-bpfj-query-is-the-query, the reachable positive witness: both
; hypotheses hold and the reading is the whole reassembly, which is :ok.
(assert-event (and (fn-bpfj-wf *bpnff-state* *bpnff-p3* *bpfjt-done*)
                   (fn-bpfj-finishedp *bpfjt-done*)
                   (equal (fn-bpfj-query *bpnff-state* *bpnff-p3* *bpfjt-done*)
                          (fn-bpnf-fragment-query *bpnff-state* *bpnff-p3*))
                   (equal (car (fn-bpnf-fragment-query *bpnff-state* *bpnff-p3*))
                          :ok)))
; Hypothesis removal, finished: the job after one step is well-formed and
; unfinished, and its reading is not the reassembly.
(assert-event (and (fn-bpfj-wf *bpnff-state* *bpnff-p3* *bpfjt-job1*)
                   (not (fn-bpfj-finishedp *bpfjt-job1*))
                   (not (equal (fn-bpfj-query *bpnff-state* *bpnff-p3* *bpfjt-job1*)
                               (fn-bpnf-fragment-query *bpnff-state* *bpnff-p3*)))))
; Hypothesis removal, wf (the sweep half): the family's inputs over the
; resume tests' gap family's finished sweep is current, finished, not
; well-formed, and reads as the gap, not the family.
(defconst *bpfjt-foreign*
  (fn-bpfj-job (fn-bpfj-job-cells *bpfjt-job0*) (fn-bpfj-job-total *bpfjt-job0*)
               (fn-bpfr-run (fn-bpfr-start *bpfr-gap-fs* *bpfr-total*) 4)))
(assert-event (and (fn-bpfj-currentp *bpnff-state* *bpnff-p3* *bpfjt-foreign*)
                   (fn-bpfj-finishedp *bpfjt-foreign*)
                   (not (fn-bpfj-wf *bpnff-state* *bpnff-p3* *bpfjt-foreign*))
                   (not (equal (fn-bpfj-query *bpnff-state* *bpnff-p3* *bpfjt-foreign*)
                               (fn-bpnf-fragment-query *bpnff-state* *bpnff-p3*)))))
; Hypothesis removal, wf (the current half): the finished job read against
; the conflict state, whose family holds one more row, is stale by name.
(assert-event (and (not (fn-bpfj-currentp *bpnff-conflict-state* *bpnff-p3* *bpfjt-done*))
                   (equal (fn-bpfj-query *bpnff-conflict-state* *bpnff-p3* *bpfjt-done*)
                          '(:stale :job))))

; KEYSTONE fn-bpfj-plan-is-the-plan-within-the-limit: under the codec's
; width the job's plan is the plan tests' :ready plan.
(defconst *bpfjt-image* (fn-bpfj-image-octets *bpnff-state* *bpnff-p3*))
(assert-event (and (natp *bpfjt-image*)
                   (<= *bpfjt-image* *fn-bpnf-max-held-image*)
                   (equal (fn-bpfj-plan *bpnff-state* *bpnff-p3* *bpfjt-done*
                                        *fn-bpnf-max-held-image*)
                          *bpnfp-plan*)
                   (equal (car *bpnfp-plan*) :ready)))
; Exactly at the image's octets the plan stands.
(assert-event (equal (fn-bpfj-plan *bpnff-state* *bpnff-p3* *bpfjt-done*
                                   *bpfjt-image*)
                     *bpnfp-plan*))
; KEYSTONE fn-bpfj-plan-refuses-past-the-limit-by-name (D27): one octet
; under the image, the same state and job are refused by the limit's name,
; before any record; the codec width would have called it :ready.
(assert-event (equal (fn-bpfj-plan *bpnff-state* *bpnff-p3* *bpfjt-done*
                                   (- *bpfjt-image* 1))
                     '(:refused :bundle-beyond-profile)))
; A non-natural limit refuses too.
(assert-event (equal (fn-bpfj-plan *bpnff-state* *bpnff-p3* *bpfjt-done* nil)
                     '(:refused :bundle-beyond-profile)))
; The capacity refusal is untouched within the limit (the plan tests' tight
; state holds the same rows).
(assert-event (equal (fn-bpfj-plan *bpnfp-tight-state* *bpnff-p3* *bpfjt-done*
                                   *fn-bpnf-max-held-image*)
                     '(:capacity)))

; SCN-077 regression: received fragments fit the wire limit, while their
; whole image exceeds it and fits the held budget. The host supplies the
; latter to both the family proposal and its persistence completion.
(defconst *bpfjt-profile* '(8 1048576 1024 256))
(defconst *bpfjt-large-b0*
  (fn-bpnfft-bundle *bpnff-base-primary* 0 (make-list 128 :initial-element 65) 256))
(defconst *bpfjt-large-b1*
  (fn-bpnfft-bundle *bpnff-base-primary* 128 (make-list 128 :initial-element 65) 256))
(defconst *bpfjt-large-h0*
  (fn-bpnfft-held '(112) 0 *bpfjt-large-b0* '(:dispatch-pending) nil))
(defconst *bpfjt-large-h1*
  (fn-bpnfft-held '(112) 1 *bpfjt-large-b1* '(:dispatch-pending) nil))
(defconst *bpfjt-large-state*
  (fn-bpnf-state (fn-bpn-initial-machine-state *bpnff-config* 8 1048576)
                (list *bpfjt-large-h0* *bpfjt-large-h1*)
                nil nil nil nil nil 3 0))
(defconst *bpfjt-large-job0* (fn-bpfj-start *bpfjt-large-state* *bpfjt-large-h0*))
(defconst *bpfjt-large-done*
  (fn-bpfj-job (fn-bpfj-job-cells *bpfjt-large-job0*)
              (fn-bpfj-job-total *bpfjt-large-job0*)
              (fn-bpfr-run (fn-bpfj-job-sweep *bpfjt-large-job0*) 64)))
(assert-event
 (and (fn-bpnpf-profilep *bpfjt-profile*)
      (fn-bpn-machine-statep (fn-bpnf-base *bpfjt-large-state*))
      (fn-bpfj-wf *bpfjt-large-state* *bpfjt-large-h0* *bpfjt-large-done*)
      (fn-bpfj-finishedp *bpfjt-large-done*)
      (<= (len (fn-bpb-encode *bpfjt-large-b0*)) (fn-bpnpf-bundle-octets *bpfjt-profile*))
      (<= (len (fn-bpb-encode *bpfjt-large-b1*)) (fn-bpnpf-bundle-octets *bpfjt-profile*))
      (< (fn-bpnpf-bundle-octets *bpfjt-profile*)
         (fn-bpfj-image-octets *bpfjt-large-state* *bpfjt-large-h0*))
      (<= (fn-bpfj-image-octets *bpfjt-large-state* *bpfjt-large-h0*)
          (fn-bpnpf-held-octets *bpfjt-profile*))
      (equal (car (fn-bpfj-plan *bpfjt-large-state* *bpfjt-large-h0*
                                *bpfjt-large-done* (fn-bpnpf-held-octets *bpfjt-profile*)))
             :ready)
      (equal (fn-bpfj-plan *bpfjt-large-state* *bpfjt-large-h0*
                           *bpfjt-large-done* (fn-bpnpf-bundle-octets *bpfjt-profile*))
             '(:refused :bundle-beyond-profile))))
