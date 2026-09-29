; PRF-250 hosted (Q4a; PKT-646): the node's family reassembly as a JOB the
; host carries across scheduling steps, in the :family / :persist-result
; events, never in the fn-bpnf machine state (the coordinator's ruling,
; 2026-09-29: the event log is the state of record and the machine state is
; derived from it; the fnbs codec is not touched).
;
; A job is (CELLS TOTAL SWEEP): the family's fragment cells and total ADU
; length when it started, and bp-fragment-resume's sweep state.
; `fn-bpfj-start' makes one from the machine state; `fn-bpfj-step' runs at
; most QUANTUM positions of it (the per-step work bound, D27: bound work per
; scheduling step, never data); `fn-bpfj-finishedp' says when the sweep is
; done.  `fn-bpfj-wf' is the invariant: the job's inputs are the family's
; current inputs (`fn-bpfj-currentp', the executable check the readings make
; -- a job that outlived its family answers (:stale :job), never a plan) and
; its sweep resumes to the sweep from the start (established by
; fn-bpfj-start-is-wf, preserved by fn-bpfj-step-preserves-wf through
; fn-bpfr-step-resumes).  A job lives in host memory only: a process death
; loses bounded work, never a decision, because every reading below is a
; function of the durable rows the job was started from.
;
; Under the invariant, every reading of a finished job is the reading the
; foundation makes by reassembling the whole family inside one step:
; KEYSTONE fn-bpfj-query-is-the-query, and the plan, the expiry-gated plan,
; the kind-18 application and the proposal and persistence steps built on
; it equal their fn-bpnf originals (the -is-the-* theorems).  The originals
; stay the logical reference every existing theorem is about.
;
; The plan takes a LIMIT, the profile's bundle octets
; (fn-bpnpf-bundle-octets), in place of the plan's *fn-bpnf-max-held-image*
; data cap (D27): a reassembled image past the limit is refused by name,
; (:refused :bundle-beyond-profile), before any record is built
; (fn-bpfj-plan-refuses-past-the-limit-by-name); within the limit, with the
; limit within the codec's width as profile admission guarantees
; (fn-bpnpf-profile-within-codec-widths), it is the plan
; (fn-bpfj-plan-is-the-plan-within-the-limit).
;
; NOT bounded here: the whole-bundle encode (fn-bpb-encode of the
; reassembled bundle) is still one step's work, once per plan, until the
; arena by extents (PKT-585).
(in-package "ACL2")
(include-book "bp-fnbs-family-replay")
(include-book "bp-fragment-resume")

(set-verify-guards-eagerness 0)

; -----------------------------------------------------------------------------
; The job

(defun fn-bpfj-cells (st anchor)
  (declare (xargs :guard t))
  (fn-bpnf-fragment-cells (fn-bpnf-active-set st anchor)))

(defun fn-bpfj-total (anchor)
  (declare (xargs :guard t))
  (fn-bpp-total-adu-length
   (fn-bpb-bundle-primary (fn-bpnf-held-bundle anchor))))

(defun fn-bpfj-job (cells total sweep)
  (declare (xargs :guard t))
  (list cells total sweep))
(defun fn-bpfj-job-cells (job) (declare (xargs :guard t)) (fn-bpn-nth 0 job))
(defun fn-bpfj-job-total (job) (declare (xargs :guard t)) (fn-bpn-nth 1 job))
(defun fn-bpfj-job-sweep (job) (declare (xargs :guard t)) (fn-bpn-nth 2 job))

(defun fn-bpfj-start (st anchor)
  (declare (xargs :guard t))
  (let ((cells (fn-bpfj-cells st anchor))
        (total (fn-bpfj-total anchor)))
    (fn-bpfj-job cells total (fn-bpfr-start cells total))))

; The per-step work bound: at most QUANTUM positions of the sweep
; (fn-bpfj-step-is-bounded), whatever the family holds.  The sweep is read
; with nth, as bp-fragment-resume reads it.
(defun fn-bpfj-step (job quantum)
  (declare (xargs :guard t))
  (let ((s (fn-bpfj-job-sweep job)))
    (fn-bpfj-job (fn-bpfj-job-cells job) (fn-bpfj-job-total job)
                 (fn-bpfr-step (nth 0 s) (nth 1 s) (nth 2 s) (nth 3 s)
                               (nth 4 s) quantum))))

(defun fn-bpfj-finishedp (job)
  (declare (xargs :guard t))
  (zp (nth 3 (fn-bpfj-job-sweep job))))

; The executable half of the invariant: the job was started from exactly
; the rows the family holds now.
(defun fn-bpfj-currentp (st anchor job)
  (declare (xargs :guard t))
  (and (equal (fn-bpfj-job-cells job) (fn-bpfj-cells st anchor))
       (equal (fn-bpfj-job-total job) (fn-bpfj-total anchor))))

(defun fn-bpfj-wf (st anchor job)
  (declare (xargs :guard t))
  (and (fn-bpfj-currentp st anchor job)
       (equal (fn-bpfr-resume (fn-bpfj-job-sweep job))
              (fn-bpfw-sweep-acc nil (fn-bpfw-sort (fn-bpfj-job-cells job))
                                 0 (fn-bpfj-job-total job) nil))))

; The accessors over the constructor; the accessors stay closed below.
(defthm fn-bpfj-job-cells-of-job
  (equal (fn-bpfj-job-cells (fn-bpfj-job cells total sweep)) cells)
  :hints (("Goal" :in-theory (enable fn-bpfj-job fn-bpfj-job-cells
                                     fn-bpn-nth fn-cbor-ag-car))))
(defthm fn-bpfj-job-total-of-job
  (equal (fn-bpfj-job-total (fn-bpfj-job cells total sweep)) total)
  :hints (("Goal" :in-theory (enable fn-bpfj-job fn-bpfj-job-total
                                     fn-bpn-nth fn-cbor-ag-car))))
(defthm fn-bpfj-job-sweep-of-job
  (equal (fn-bpfj-job-sweep (fn-bpfj-job cells total sweep)) sweep)
  :hints (("Goal" :in-theory (enable fn-bpfj-job fn-bpfj-job-sweep
                                     fn-bpn-nth fn-cbor-ag-car))))
(in-theory (disable fn-bpfj-job fn-bpfj-job-cells fn-bpfj-job-total
                    fn-bpfj-job-sweep))

(defthm fn-bpfr-resume-of-start
  (equal (fn-bpfr-resume (fn-bpfr-start fs total))
         (fn-bpfw-sweep-acc nil (fn-bpfw-sort fs) 0 total nil))
  :hints (("Goal" :in-theory (enable fn-bpfr-resume fn-bpfr-start
                                     fn-bpfr-state))))

(defthm fn-bpfj-start-is-wf
  (fn-bpfj-wf st anchor (fn-bpfj-start st anchor))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpfj-wf fn-bpfj-currentp fn-bpfj-start
                                fn-bpfj-job-cells-of-job
                                fn-bpfj-job-total-of-job
                                fn-bpfj-job-sweep-of-job
                                fn-bpfr-resume-of-start)
                              (theory 'minimal-theory)))))

(defthm fn-bpfj-step-preserves-wf
  (implies (fn-bpfj-wf st anchor job)
           (fn-bpfj-wf st anchor (fn-bpfj-step job quantum)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpfj-wf fn-bpfj-currentp fn-bpfj-step
                                fn-bpfj-job-cells-of-job
                                fn-bpfj-job-total-of-job
                                fn-bpfj-job-sweep-of-job
                                fn-bpfr-step-resumes fn-bpfr-resume)
                              (theory 'minimal-theory)))))

; The work bound: one step consumes exactly min(QUANTUM, left) positions.
(defthm fn-bpfj-step-is-bounded
  (implies (and (natp (nth 3 (fn-bpfj-job-sweep job)))
                (natp quantum))
           (equal (nth 3 (fn-bpfj-job-sweep (fn-bpfj-step job quantum)))
                  (- (nth 3 (fn-bpfj-job-sweep job))
                     (min (nth 3 (fn-bpfj-job-sweep job)) quantum))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpfj-step fn-bpfj-job-sweep-of-job)
                              (theory 'minimal-theory))
           :use ((:instance fn-bpfr-step-is-bounded
                            (active (nth 0 (fn-bpfj-job-sweep job)))
                            (queue (nth 1 (fn-bpfj-job-sweep job)))
                            (i (nth 2 (fn-bpfj-job-sweep job)))
                            (n (nth 3 (fn-bpfj-job-sweep job)))
                            (acc (nth 4 (fn-bpfj-job-sweep job))))))))

; -----------------------------------------------------------------------------
; The readings of a job

; The family query read off the job: the foundation's fn-bpnf-fragment-query
; without the sweep.  A stale job and an unfinished one are named, never
; planned.
(defun fn-bpfj-query (st anchor job)
  (declare (xargs :guard t))
  (cond ((not (and (fn-bpnf-active-fragmentp anchor)
                   (fn-bpnf-family-member anchor (fn-bpnf-held-list st))))
         (list :invalid :bounds))
        ((not (fn-bpfj-currentp st anchor job)) (list :stale :job))
        ((not (fn-bpfj-finishedp job)) (list :pending :job))
        (t (fn-bpfr-finish (fn-bpfj-job-cells job) (fn-bpfj-job-total job)
                           (fn-bpfj-job-sweep job)))))

;; KEYSTONE.  A finished well-formed job reads as the whole reassembly.
(defthm fn-bpfj-query-is-the-query
  (implies (and (fn-bpfj-wf st anchor job)
                (fn-bpfj-finishedp job))
           (equal (fn-bpfj-query st anchor job)
                  (fn-bpnf-fragment-query st anchor)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpfj-query fn-bpfj-wf fn-bpfj-currentp
                                fn-bpfj-cells fn-bpfj-total
                                fn-bpnf-fragment-query fn-bpfr-finish
                                fn-bpfw-reassemble)
                              (theory 'minimal-theory)))))

(defun fn-bpfj-image-octets (st anchor)
  (declare (xargs :guard t))
  (len (fn-bpb-encode
        (fn-bpnf-family-whole-bundle
         (fn-bpnf-offset-zero-source (fn-bpnf-active-set st anchor))
         (cadr (fn-bpnf-fragment-query st anchor))))))

; fn-bpnf-family-plan over the job, under LIMIT (the profile's bundle
; octets) in place of the codec-width cap.
(defun fn-bpfj-plan (st anchor job limit)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))))
  (let* ((rows (fn-bpnf-active-set st anchor))
         (query (fn-bpfj-query st anchor job)))
    (if (not (equal (car query) :ok))
        query
      (let* ((zero (fn-bpnf-offset-zero-source rows))
             (whole (fn-bpnf-family-whole-bundle zero (cadr query))))
        (if (not (and zero (fn-bpb-bundlep whole)))
            (list :invalid :whole)
          (let* ((wire (fn-bpb-encode whole))
                 (held (fn-bpnf-held-list st))
                 (new-slots (+ (- (len held) (len rows)) 1))
                 (new-octets (+ (- (fn-bpnf-held-octets held)
                                   (fn-bpnf-held-octets rows))
                                (len wire))))
            (cond ((not (and (natp limit) (<= (len wire) limit)))
                   (list :refused :bundle-beyond-profile))
                  ((or (not (fn-cbor-octet-listp wire))
                       (< new-slots 0)
                       (< new-octets 0)
                       (> new-slots (fn-bpn-machine-state-max-jobs
                                     (fn-bpnf-base st)))
                       (> new-octets (fn-bpn-machine-state-max-octets
                                      (fn-bpnf-base st))))
                   (list :capacity))
                  (t (list :ready whole wire
                           (fn-bpnf-family-consumed-ids rows) zero)))))))))

;; KEYSTONE (D27).  Past the profile's limit the image is refused by name,
;; before any record: whatever the capacity checks would have said.
(defthm fn-bpfj-plan-refuses-past-the-limit-by-name
  (implies (and (fn-bpfj-wf st anchor job)
                (fn-bpfj-finishedp job)
                (equal (car (fn-bpnf-fragment-query st anchor)) :ok)
                (fn-bpnf-offset-zero-source (fn-bpnf-active-set st anchor))
                (fn-bpb-bundlep
                 (fn-bpnf-family-whole-bundle
                  (fn-bpnf-offset-zero-source (fn-bpnf-active-set st anchor))
                  (cadr (fn-bpnf-fragment-query st anchor))))
                (not (and (natp limit)
                          (<= (fn-bpfj-image-octets st anchor) limit))))
           (equal (fn-bpfj-plan st anchor job limit)
                  '(:refused :bundle-beyond-profile)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpfj-plan fn-bpfj-image-octets
                                fn-bpfj-query-is-the-query)
                              (theory 'minimal-theory)))))

;; KEYSTONE.  Within the limit, with the limit within the codec's width, the
;; job's plan is the foundation's plan.
(defthm fn-bpfj-plan-is-the-plan-within-the-limit
  (implies (and (fn-bpfj-wf st anchor job)
                (fn-bpfj-finishedp job)
                (natp limit)
                (<= limit *fn-bpnf-max-held-image*)
                (<= (fn-bpfj-image-octets st anchor) limit))
           (equal (fn-bpfj-plan st anchor job limit)
                  (fn-bpnf-family-plan st anchor)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpfj-plan fn-bpnf-family-plan
                                fn-bpfj-image-octets
                                fn-bpfj-query-is-the-query)
                              (theory 'minimal-theory)))))

; The expiry gate over the job's plan (books/bp-node-fragment-expiry
; fn-bpnf-family-plan-at).
(defun fn-bpfj-plan-at (st anchor observation job limit)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))))
  (let ((rows (fn-bpnf-active-set st anchor)))
    (if (and (fn-clock-observationp observation)
             (consp rows)
             (fn-bpnf-family-rows-livep rows observation))
        (fn-bpfj-plan st anchor job limit)
      (list :blocked :expiry))))

(defthm fn-bpfj-plan-at-is-the-plan-at
  (implies (and (fn-bpfj-wf st anchor job)
                (fn-bpfj-finishedp job)
                (natp limit)
                (<= limit *fn-bpnf-max-held-image*)
                (<= (fn-bpfj-image-octets st anchor) limit))
           (equal (fn-bpfj-plan-at st anchor observation job limit)
                  (fn-bpnf-family-plan-at st anchor observation)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpfj-plan-at fn-bpnf-family-plan-at
                                fn-bpfj-plan-is-the-plan-within-the-limit)
                              (theory 'minimal-theory)))))

; The kind-18 application over the job's plan
; (books/bp-node-fragment-replacement fn-bpnf-family-apply, -apply-at).
(defun fn-bpfj-apply (st record expected-arrival job limit)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))))
  (let* ((held (fn-bpnf-held-list st))
         (anchor-arrival (fn-bpn-nth 3 record))
         (anchor (fn-bpnf-find-arrival anchor-arrival held)))
    (if (not (and (or (fn-bpnf-family-recordp record)
                      (fn-bpnf-family-record-atp record))
                  (fn-frame-natp expected-arrival)
                  (equal (fn-bpn-nth 4 record) expected-arrival)
                  (equal (fn-bpnf-arrival-count anchor-arrival held) 1)
                  (fn-bpnf-active-fragmentp anchor)))
        (list :fault :family-anchor)
      (let ((plan (fn-bpfj-plan st anchor job limit)))
        (if (not (and (equal (fn-cbor-ag-car plan) :ready)
                      (equal (fn-bpn-nth 5 record) (fn-bpn-nth 2 plan))
                      (null (fn-bpnf-find-held
                             (fn-bpnf-held-key
                              (fn-bpnf-held-principal (fn-bpn-nth 4 plan))
                              (fn-bpb-bundle-id (fn-bpn-nth 1 plan)))
                             held))))
            (list :fault :family-image)
          (let* ((zero (fn-bpn-nth 4 plan))
                 (consumed (fn-bpnf-active-set st anchor))
                 (whole (fn-bpn-nth 1 plan))
                 (wire (fn-bpn-nth 2 plan))
                 (row (fn-bpnf-held
                       (fn-bpnf-held-principal zero)
                       (fn-bpb-bundle-id whole)
                       expected-arrival
                       (fn-bpn-nth 4 zero)
                       nil (list :reassembled (fn-bpn-nth 3 plan))
                       whole wire (fn-bpn-nth 9 zero)
                       nil nil '(:dispatch-pending) nil nil
                       expected-arrival)))
            (if (not (fn-bpnf-heldp row))
                (list :fault :family-row)
              (list :ready
                    (cons row (fn-bpnf-family-retain-other-rows held consumed))
                    row consumed))))))))

(defun fn-bpfj-record-anchor (st record)
  (declare (xargs :guard t))
  (fn-bpnf-find-arrival (fn-bpn-nth 3 record) (fn-bpnf-held-list st)))

(defthm fn-bpfj-apply-is-the-apply
  (implies (and (fn-bpfj-wf st (fn-bpfj-record-anchor st record) job)
                (fn-bpfj-finishedp job)
                (natp limit)
                (<= limit *fn-bpnf-max-held-image*)
                (<= (fn-bpfj-image-octets st (fn-bpfj-record-anchor st record))
                    limit))
           (equal (fn-bpfj-apply st record expected-arrival job limit)
                  (fn-bpnf-family-apply st record expected-arrival)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpfj-apply fn-bpnf-family-apply
                                fn-bpfj-record-anchor
                                fn-bpfj-plan-is-the-plan-within-the-limit)
                              (theory 'minimal-theory)))))

(defun fn-bpfj-apply-at (st record expected-arrival job limit)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))))
  (if (not (fn-bpnf-family-record-atp record))
      (list :fault :legacy-family-expiry)
    (let* ((observation (fn-bpn-nth 7 record))
           (anchor (fn-bpnf-find-arrival
                    (fn-bpn-nth 3 record) (fn-bpnf-held-list st)))
           (plan (fn-bpfj-plan-at st anchor observation job limit)))
      (if (not (equal (car plan) :ready))
          (list :fault :family-expiry)
        (fn-bpfj-apply st record expected-arrival job limit)))))

(defthm fn-bpfj-apply-at-is-the-apply-at
  (implies (and (fn-bpfj-wf st (fn-bpfj-record-anchor st record) job)
                (fn-bpfj-finishedp job)
                (natp limit)
                (<= limit *fn-bpnf-max-held-image*)
                (<= (fn-bpfj-image-octets st (fn-bpfj-record-anchor st record))
                    limit))
           (equal (fn-bpfj-apply-at st record expected-arrival job limit)
                  (fn-bpnf-family-apply-at st record expected-arrival)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpfj-apply-at fn-bpnf-family-apply-at
                                fn-bpfj-record-anchor
                                fn-bpfj-plan-at-is-the-plan-at
                                fn-bpfj-apply-is-the-apply)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-bpfj-cells fn-bpfj-total fn-bpfj-start
                    fn-bpfj-step fn-bpfj-finishedp fn-bpfj-currentp fn-bpfj-wf
                    fn-bpfj-query fn-bpfj-image-octets fn-bpfj-plan
                    fn-bpfj-plan-at fn-bpfj-apply fn-bpfj-record-anchor
                    fn-bpfj-apply-at))
