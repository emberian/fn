; Teeth for PRF-1008 / PRF-1009 (books/bp-node-fragment-step.lisp, Q4a
; increment B): the family proposal and its kind-18 result over the
; host-carried reassembly job equal the whole-family steps within the
; profile's limit; the dispatcher routes the job forms to the twins; the
; candidate selector names the family without reassembling.
(in-package "ACL2")
(include-book "bp-node-fragment-step-tests")
(include-book "../../books/defkeystone")
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

; S008, the coverage gate (fn-bpfj-family-coveredp): a family is a candidate
; only once the payload octets its rows hold reach the total ADU length its
; offset-zero row declares.  The short family holds only the offset-zero
; fragment (5 payload octets of a declared 8): every other test of
; fn-bpfj-candidate passes for it (the family has an offset-zero row, the row
; is active, unique at its arrival, live and not tried), and still no
; candidate is offered, so no sweep walks the declared canvas.  The whole
; family adds the second fragment (10 payload octets; the two overlap) and is
; offered at once, so the difference is the held octets and nothing else.
(defconst *bpfsj-short-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*) (list *bpnff-p0*)
                 nil nil nil nil nil 3 0))
(defconst *bpfsj-whole-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*) (list *bpnff-p3* *bpnff-p0*)
                 nil nil nil nil nil 3 0))
(assert-event
 (and (equal (fn-bpfj-rows-payload-octets
              (fn-bpnf-active-set *bpfsj-short-state* *bpnff-p0*) 0)
             5)
      (equal (fn-bpfj-rows-payload-octets
              (fn-bpnf-active-set *bpfsj-whole-state* *bpnff-p3*) 0)
             10)
      (equal (fn-bpp-total-adu-length
              (fn-bpb-bundle-primary (fn-bpnf-held-bundle *bpnff-p0*)))
             8)))
(assert-event
 (and (member-equal (fn-bpnf-fragment-family-key *bpnff-p0*)
                    (fn-bpnf-zero-family-keys
                     (fn-bpnf-held-list *bpfsj-short-state*)))
      (fn-bpnf-active-fragmentp *bpnff-p0*)
      (equal (fn-bpnf-arrival-count
              (fn-bpn-nth 3 *bpnff-p0*)
              (fn-bpnf-held-list *bpfsj-short-state*))
             1)
      (fn-bpnf-family-rows-livep
       (fn-bpnf-active-set *bpfsj-short-state* *bpnff-p0*)
       *bpnfs-live-observation*)))
(assert-event
 (and (not (fn-bpfj-family-coveredp *bpfsj-short-state* *bpnff-p0*))
      (fn-bpfj-family-coveredp *bpfsj-whole-state* *bpnff-p0*)))
(assert-event
 (equal (fn-bpfj-next-candidate *bpfsj-short-state* *bpnfs-live-observation*
                                nil)
        nil))
(assert-event
 (equal (fn-bpfj-next-candidate *bpfsj-whole-state* *bpnfs-live-observation*
                                nil)
        (list :ready *bpfsj-arrival* *bpfsj-key*)))
(must-fail-checked
 (assert-event
  (equal (car (fn-bpfj-next-candidate *bpfsj-short-state*
                                      *bpnfs-live-observation* nil))
         :ready)))

; -----------------------------------------------------------------------------
; KEYSTONE teeth (PRF-1051, fn-bpfj-next-candidate-is-a-ready-family-
; representative).  Reachable positive witness, the complete antecedent and
; conclusion: *bpnff-state* has no issued family, no wait and a framed next
; arrival; its one zero-sourced family has p3 as representative, ready; the
; answer is that family's (:ready ARRIVAL KEY).
(assert-event
 (let* ((st *bpnff-state*) (obs *bpnfs-live-observation*)
        (held (fn-bpnf-held-list st))
        (zero (fn-bpnf-zero-family-keys held))
        (r (fn-bpfj-next-candidate st obs nil))
        (h (fn-bpfj-family-rep (fn-bpn-nth 2 r) held)))
   (and (not (fn-bpnf-issued st))
        (not (fn-bpnf-waits st))
        (fn-frame-natp (fn-bpnf-next-arrival st))
        (fn-bpfj-any-ready-rep zero st held obs nil)
        (equal r (list :ready *bpfsj-arrival* *bpfsj-key*))
        (member-equal *bpfsj-key* zero)
        (equal h *bpnff-p3*)
        (equal (fn-bpn-nth 3 h) (fn-bpn-nth 1 r))
        (fn-bpfj-row-readyp st h obs))))
; The nil side, hypothesis removed one at a time.  The coverage gate: the short
; family's representative is not ready and the answer is nil.
(assert-event
 (let* ((st *bpfsj-short-state*) (obs *bpnfs-live-observation*)
        (held (fn-bpnf-held-list st)))
   (and (not (fn-bpnf-issued st)) (not (fn-bpnf-waits st))
        (fn-frame-natp (fn-bpnf-next-arrival st))
        (not (fn-bpfj-row-readyp
              st (fn-bpfj-family-rep *bpfsj-key* held) obs))
        (not (fn-bpfj-any-ready-rep (fn-bpnf-zero-family-keys held) st held obs nil))
        (null (fn-bpfj-next-candidate st obs nil)))))
; TRIED: the ready family is excluded once tried.
(assert-event
 (let* ((st *bpnff-state*) (obs *bpnfs-live-observation*)
        (held (fn-bpnf-held-list st)))
   (and (fn-bpfj-row-readyp st (fn-bpfj-family-rep *bpfsj-key* held) obs)
        (not (fn-bpfj-any-ready-rep (fn-bpnf-zero-family-keys held) st held obs
                                    (list *bpfsj-key*)))
        (null (fn-bpfj-next-candidate st obs (list *bpfsj-key*))))))
; The gate "no family issued": the same rows hold a ready representative under
; an issued family, yet the answer is nil, so a ready representative alone
; does not decide the answer.
(defconst *bpfsj-issued-state* (update-nth 6 '(:issued) *bpnff-state*))
(assert-event
 (let* ((st *bpfsj-issued-state*) (obs *bpnfs-live-observation*)
        (held (fn-bpnf-held-list st)))
   (and (fn-bpnf-issued st)
        (fn-bpfj-any-ready-rep (fn-bpnf-zero-family-keys held) st held obs nil)
        (null (fn-bpfj-next-candidate st obs nil)))))
(must-fail-checked
 (assert-event
  (let* ((st *bpfsj-issued-state*) (obs *bpnfs-live-observation*)
         (held (fn-bpnf-held-list st)))
    (iff (fn-bpfj-next-candidate st obs nil)
         (fn-bpfj-any-ready-rep (fn-bpnf-zero-family-keys held) st held obs nil)))))

;; The generated keystone's teeth (TEETH CONTRACT v1).  The theorem has no
;; hypothesis, so no removal is owed; its antecedent-shaped conjuncts are the
;; gates inside the conclusion, which the witnesses above pull apart one at a
;; time.
(defteeth fn-bpfj-next-candidate-is-a-ready-family-representative
  :claim (() (let* ((held (fn-bpnf-held-list st))
         (zero (fn-bpnf-zero-family-keys held))
         (r (fn-bpfj-next-candidate st observation tried)))
    (and (iff r (and (not (fn-bpnf-issued st))
                     (not (fn-bpnf-waits st))
                     (fn-frame-natp (fn-bpnf-next-arrival st))
                     (fn-bpfj-any-ready-rep zero st held observation tried)))
         (implies r
                  (let* ((k (fn-bpn-nth 2 r))
                         (h (fn-bpfj-family-rep k held)))
                    (and (equal (car r) :ready)
                         (member-equal k zero)
                         (not (member-equal k tried))
                         h
                         (equal (fn-bpn-nth 3 h) (fn-bpn-nth 1 r))
                         (fn-bpfj-row-readyp st h observation)))))))
  :subject fn-bpfj-next-candidate
  :witness ((st *bpnff-state*) (observation *bpnfs-live-observation*) (tried nil))
  :breaks nil
  :mutations ((answers-without-a-ready-representative
               (:conclusion (let* ((held (fn-bpnf-held-list st))
         (zero (fn-bpnf-zero-family-keys held))
         (r (fn-bpfj-next-candidate st observation tried)))
    (and (iff r (and (not (fn-bpnf-issued st))
                     (not (fn-bpnf-waits st))
                     (fn-frame-natp (fn-bpnf-next-arrival st))
                     (not (fn-bpfj-any-ready-rep zero st held observation tried))))
         (implies r
                  (let* ((k (fn-bpn-nth 2 r))
                         (h (fn-bpfj-family-rep k held)))
                    (and (equal (car r) :ready)
                         (member-equal k zero)
                         (not (member-equal k tried))
                         h
                         (equal (fn-bpn-nth 3 h) (fn-bpn-nth 1 r))
                         (fn-bpfj-row-readyp st h observation)))))))
               ((st *bpnff-state*) (observation *bpnfs-live-observation*) (tried nil))
               :fault "a selector that answers although no zero-sourced family has a ready representative")
              (wrong-arrival
               (:conclusion (let* ((held (fn-bpnf-held-list st))
         (zero (fn-bpnf-zero-family-keys held))
         (r (fn-bpfj-next-candidate st observation tried)))
    (and (iff r (and (not (fn-bpnf-issued st))
                     (not (fn-bpnf-waits st))
                     (fn-frame-natp (fn-bpnf-next-arrival st))
                     (fn-bpfj-any-ready-rep zero st held observation tried)))
         (implies r
                  (let* ((k (fn-bpn-nth 2 r))
                         (h (fn-bpfj-family-rep k held)))
                    (and (equal (car r) :ready)
                         (member-equal k zero)
                         (not (member-equal k tried))
                         h
                         (equal (fn-bpn-nth 3 h) (+ 1 (fn-bpn-nth 1 r)))
                         (fn-bpfj-row-readyp st h observation)))))))
               ((st *bpnff-state*) (observation *bpnfs-live-observation*) (tried nil))
               :fault "an answer whose arrival is not the representative's")))

;; The owed rows of this world are held met here, as (defteeth-check) does, less
;; the two def-keyset-check bridges of books/store-files.lisp
;; (fn-sf-success-listp) and books/retention.lisp (fn-retain-ks-disjointp),
;; whose defteeth are in tests/acl2/store-files-teeth-tests.lisp and
;; tests/acl2/retention-tests.lisp, each of which holds its rows met.
(make-event
 (let ((problem (fn-dt-owed-problem
                 (remove1-assoc-eq 'fn-sf-success-listp-ks-is-logic
                  (remove1-assoc-eq 'fn-sf-success-listp-walk-is-logic
                   (remove1-assoc-eq 'fn-retain-ks-disjointp-ks-is-logic
                    (remove1-assoc-eq 'fn-retain-ks-disjointp-walk-is-logic
                                      (table-alist 'fn-teeth-owed (w state))))))
                 (table-alist 'fn-teeth (w state))
                 (w state))))
   (if problem
       (er soft 'defteeth-check "~@0." problem)
     (value '(value-triple :teeth-complete)))))
