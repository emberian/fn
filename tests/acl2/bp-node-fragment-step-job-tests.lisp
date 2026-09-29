; Teeth for PRF-1008 / PRF-1009 (books/bp-node-fragment-step.lisp, Q4a
; increment B): the family proposal and its kind-18 result over the
; host-carried reassembly job equal the whole-family steps within the
; profile's limit; the dispatcher routes the job forms to the twins; the
; candidate selector names the family without reassembling.
(in-package "ACL2")
(include-book "bp-node-fragment-step-tests")
(include-book "bp-node-fragment-job-tests")

; The family the plan tests call :ready (*bpnff-p3* is its anchor row) and
; the job the job tests finished over it (*bpfjt-done*).
(defconst *bpfsj-arrival* (fn-bpn-nth 3 *bpnff-p3*))
(defconst *bpfsj-anchor*
  (fn-bpnf-find-arrival *bpfsj-arrival* (fn-bpnf-held-list *bpnff-state*)))
(assert-event (equal *bpfsj-anchor* *bpnff-p3*))
(defconst *bpfsj-limit* *bpfjt-image*)

; The shape the boundary checks of a carried job (bp-fragment-job-shape):
; the job the tests started and the one they finished are readable; a job
; whose cells are not a true list is not (the guard, not the logic).
(assert-event
 (and (fn-bpfj-jobp *bpfjt-job0*)
      (fn-bpfj-readable-jobp *bpfjt-job0*)
      (fn-bpfj-jobp *bpfjt-done*)
      (fn-bpfj-readable-jobp *bpfjt-done*)
      (not (fn-bpfj-readable-jobp
            (fn-bpfj-job (fn-bpfj-job-cells *bpfjt-done*)
                         (fn-bpfj-job-total *bpfjt-done*)
                         (fn-bpfr-state nil nil 0 0 (cons :cell 1)))))
      (not (fn-bpfj-jobp nil))))

; -----------------------------------------------------------------------------
; PRF-1008 fn-bpfj-propose-step-is-the-propose-step: the complete antecedent.
(assert-event
 (and (fn-bpfj-wf *bpnff-state* *bpfsj-anchor* *bpfjt-done*)
      (fn-bpfj-finishedp *bpfjt-done*)
      (natp *bpfsj-limit*)
      (<= *bpfsj-limit* *fn-bpnf-max-held-image*)
      (<= (fn-bpfj-image-octets *bpnff-state* *bpfsj-anchor*) *bpfsj-limit*)))

(defun bpfsj-job-proposal ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpfj-propose-step *bpnff-state* *bpfsj-arrival* *bpnfs-live-observation*
                        *bpfjt-done* *bpfsj-limit*))

; The conclusion, and that the proposal is real: it issues the publication.
(assert-event
 (equal (bpfsj-job-proposal)
        (fn-bpnf-family-propose-step *bpnff-state* *bpfsj-arrival*
                                     *bpnfs-live-observation*)))
(assert-event
 (equal (car (car (fn-bpnf-answer-effects (bpfsj-job-proposal))))
        :persist-family))

; The dispatcher: the job form reaches the twin, the plain form the family
; step; the boundary admits both forms.
(assert-event
 (equal (fn-bpnf-fragment-step
         *bpnff-state*
         (list :family *bpfsj-arrival* *bpnfs-live-observation*
               *bpfjt-done* *bpfsj-limit*))
        (bpfsj-job-proposal)))
(assert-event
 (equal (fn-bpnf-fragment-step
         *bpnff-state* (list :family *bpfsj-arrival* *bpnfs-live-observation*))
        (fn-bpnf-family-propose-step *bpnff-state* *bpfsj-arrival*
                                     *bpnfs-live-observation*)))
(assert-event
 (and (fn-bpnf-host-eventp
       (list :family *bpfsj-arrival* *bpnfs-live-observation*
             *bpfjt-done* *bpfsj-limit*))
      (fn-bpnf-host-eventp
       (list :family *bpfsj-arrival* *bpnfs-live-observation*))
      (not (fn-bpnf-host-eventp
            (list :family *bpfsj-arrival* *bpnfs-live-observation*
                  *bpfjt-done* :no-limit)))))

; Hypothesis removal (fn-bpfj-finishedp): the unfinished job *bpfjt-job0*;
; every retained hypothesis holds, the omitted one fails, the conclusion
; fails: the step issues nothing.
(assert-event
 (and (fn-bpfj-wf *bpnff-state* *bpfsj-anchor* *bpfjt-job0*)
      (not (fn-bpfj-finishedp *bpfjt-job0*))
      (natp *bpfsj-limit*)
      (<= *bpfsj-limit* *fn-bpnf-max-held-image*)
      (<= (fn-bpfj-image-octets *bpnff-state* *bpfsj-anchor*) *bpfsj-limit*)
      (equal (fn-bpnf-answer-effects
              (fn-bpfj-propose-step *bpnff-state* *bpfsj-arrival*
                                    *bpnfs-live-observation*
                                    *bpfjt-job0* *bpfsj-limit*))
             nil)
      (not (equal (fn-bpfj-propose-step *bpnff-state* *bpfsj-arrival*
                                        *bpnfs-live-observation*
                                        *bpfjt-job0* *bpfsj-limit*)
                  (fn-bpnf-family-propose-step *bpnff-state* *bpfsj-arrival*
                                               *bpnfs-live-observation*)))))

; Hypothesis removal (the image within the limit): one octet under the
; image the job plan refuses by name (PRF-989) and the step issues nothing.
(assert-event
 (and (fn-bpfj-wf *bpnff-state* *bpfsj-anchor* *bpfjt-done*)
      (fn-bpfj-finishedp *bpfjt-done*)
      (natp (1- *bpfsj-limit*))
      (<= (1- *bpfsj-limit*) *fn-bpnf-max-held-image*)
      (not (<= (fn-bpfj-image-octets *bpnff-state* *bpfsj-anchor*)
               (1- *bpfsj-limit*)))
      (equal (fn-bpfj-plan-at *bpnff-state* *bpfsj-anchor*
                              *bpnfs-live-observation* *bpfjt-done*
                              (1- *bpfsj-limit*))
             '(:refused :bundle-beyond-profile))
      (equal (fn-bpnf-answer-effects
              (fn-bpfj-propose-step *bpnff-state* *bpfsj-arrival*
                                    *bpnfs-live-observation*
                                    *bpfjt-done* (1- *bpfsj-limit*)))
             nil)
      (not (equal (fn-bpfj-propose-step *bpnff-state* *bpfsj-arrival*
                                        *bpnfs-live-observation*
                                        *bpfjt-done* (1- *bpfsj-limit*))
                  (fn-bpnf-family-propose-step *bpnff-state* *bpfsj-arrival*
                                               *bpnfs-live-observation*)))))

; -----------------------------------------------------------------------------
; PRF-1009 fn-bpfj-persist-step-is-the-persist-step, from the proposed state.
; (Functions, not constants: the proposal's record carries a frame digest
; through the fn-frame-digest attachment, which a defconst cannot evaluate.)
(defun bpfsj-pending ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-answer-state (bpfsj-job-proposal)))
(defun bpfsj-epoch ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-nth 1 (fn-bpnf-issued (bpfsj-pending))))
(defun bpfsj-op ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-nth 2 (fn-bpnf-issued (bpfsj-pending))))
(defun bpfsj-record-anchor ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpfj-record-anchor (bpfsj-pending)
                         (fn-bpn-nth 4 (fn-bpnf-issued (bpfsj-pending)))))

; fn-bpfj-record-anchor-of-family-record-at, concretely.
(assert-event (equal (bpfsj-record-anchor) *bpfsj-anchor*))

; The complete antecedent at the issued record's anchor.
(assert-event
 (and (fn-bpfj-wf (bpfsj-pending) (bpfsj-record-anchor) *bpfjt-done*)
      (fn-bpfj-finishedp *bpfjt-done*)
      (natp *bpfsj-limit*)
      (<= *bpfsj-limit* *fn-bpnf-max-held-image*)
      (<= (fn-bpfj-image-octets (bpfsj-pending) (bpfsj-record-anchor))
          *bpfsj-limit*)))

(defun bpfsj-durable ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpfj-persist-step (bpfsj-pending) (bpfsj-epoch) (bpfsj-op) :durable
                        *bpfjt-done* *bpfsj-limit*))

; The conclusion, and that the result is real: the family is ready.
(assert-event
 (equal (bpfsj-durable)
        (fn-bpnf-family-persist-step (bpfsj-pending) (bpfsj-epoch) (bpfsj-op)
                                     :durable)))
(assert-event
 (equal (car (car (fn-bpnf-answer-effects (bpfsj-durable)))) :family-ready))

; The dispatcher and the boundary for the result's job form.
(assert-event
 (equal (fn-bpnf-fragment-step
         (bpfsj-pending)
         (list :persist-result (bpfsj-epoch) (bpfsj-op) :durable
               *bpfjt-done* *bpfsj-limit*))
        (bpfsj-durable)))
(assert-event
 (and (fn-bpnf-host-eventp
       (list :persist-result (bpfsj-epoch) (bpfsj-op) :durable
             *bpfjt-done* *bpfsj-limit*))
      (fn-bpnf-host-eventp
       (list :persist-result (bpfsj-epoch) (bpfsj-op) :durable))))

; A refused or uncertain result answers as the family step does, whatever
; the job.
(assert-event
 (and (equal (fn-bpfj-persist-step (bpfsj-pending) (bpfsj-epoch) (bpfsj-op)
                                   :refused *bpfjt-done* *bpfsj-limit*)
             (fn-bpnf-family-persist-step (bpfsj-pending) (bpfsj-epoch)
                                          (bpfsj-op) :refused))
      (equal (fn-bpfj-persist-step (bpfsj-pending) (bpfsj-epoch) (bpfsj-op)
                                   :uncertain *bpfjt-job0* *bpfsj-limit*)
             (fn-bpnf-family-persist-step (bpfsj-pending) (bpfsj-epoch)
                                          (bpfsj-op) :uncertain))))

; -----------------------------------------------------------------------------
; The candidate selector (no reassembly): the ready family is the candidate;
; once tried, there is none.
(defconst *bpfsj-key* (fn-bpnf-fragment-family-key *bpnff-p3*))
(assert-event
 (equal (fn-bpfj-next-candidate *bpnff-state* *bpnfs-live-observation* nil)
        (list :ready *bpfsj-arrival* *bpfsj-key*)))
(assert-event
 (equal (fn-bpfj-next-candidate *bpnff-state* *bpnfs-live-observation*
                                (list *bpfsj-key*))
        nil))
; With a proposal pending nothing is selected.
(assert-event
 (equal (fn-bpfj-next-candidate (bpfsj-pending) *bpnfs-live-observation* nil)
        nil))
