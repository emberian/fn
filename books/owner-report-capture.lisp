; Internal registered report custody.  No public issuer or retirement receipt
; is supplied by this leaf: callers must enter after genuine report admission.
(in-package "ACL2")
(include-book "state-globals")

(defun fn-orc-job (state)
  (declare (xargs :stobjs state :guard t))
  (let ((job (if (boundp-global 'fn-owner-report-job state)
                 (f-get-global 'fn-owner-report-job state) nil)))
    (if (and (true-listp job) (equal (len job) 10)) job nil)))

(defun fn-orc-source (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-report-source-phase state)
      (f-get-global 'fn-owner-report-source-phase state) :unavailable))

(defun fn-orc-job-currentp (token state)
  (declare (xargs :stobjs state :guard t))
  (let ((job (fn-orc-job state)))
    (and (consp job) (equal (car job) :owner-report)
         (equal token (nth 1 job)))))

(defun fn-orc-job-readablep (token state)
  (declare (xargs :stobjs state :guard t))
  (and (equal (fn-orc-source state) :stable)
       (fn-orc-job-currentp token state)
       (equal (nth 7 (fn-orc-job state)) :valid)))

; Immutable capture is a retained producer reference, not a live owner getter.
; The internal issuer supplies TOKEN and original claim only after PRS debit.
(defun fn-orc-register-internal (token kind request cache capture cursor claim state)
  (declare (xargs :stobjs state :guard t))
  (cond ((fn-orc-job state) (mv :report-busy state))
        ((not (equal (fn-orc-source state) :stable))
         (mv :report-source-unavailable state))
        (t (let ((state (f-put-global 'fn-owner-report-job
                 (list :owner-report token kind request cache capture cursor
                       :valid nil claim) state)))
             (mv :report-registered state)))))

; Every tick gets the registered job.  It never accepts a caller's cursor.
(defun fn-orc-current (token state)
  (declare (xargs :stobjs state :guard t))
  (cond ((not (fn-orc-job-currentp token state)) (mv :report-stale nil))
        ((not (fn-orc-job-readablep token state))
         (mv :snapshot-changed nil))
        (t (mv :report-current (fn-orc-job state)))))

(defun fn-orc-keep-progress-internal (token cursor state)
  (declare (xargs :stobjs state :guard t))
  (if (fn-orc-job-readablep token state)
      (let ((state (f-put-global 'fn-owner-report-job
            (update-nth 6 cursor (fn-orc-job state)) state)))
        (mv :report-progress state))
    (mv :snapshot-changed state)))

; Invalidate before any borrowed Cat/arena write.  The original job and all
; captured references remain registered until a genuine terminal retirement.
(defun fn-orc-writer-enter (state)
  (declare (xargs :stobjs state :guard t))
  (let* ((job (fn-orc-job state))
         (state (if (and job (not (equal (nth 7 job) :complete)))
                    (f-put-global 'fn-owner-report-job
                      (update-nth 7 :invalid job) state)
                  state))
         (depth (if (boundp-global 'fn-owner-report-write-depth state)
                    (nfix (f-get-global 'fn-owner-report-write-depth state)) 0))
         (state (f-put-global 'fn-owner-report-write-depth (+ 1 depth) state)))
    (f-put-global 'fn-owner-report-source-phase
      (if (equal (fn-orc-source state) :fault) :fault :mutating) state)))

(defun fn-orc-writer-leave (state)
  (declare (xargs :stobjs state :guard t))
  (let* ((depth (if (boundp-global 'fn-owner-report-write-depth state)
                    (nfix (f-get-global 'fn-owner-report-write-depth state)) 0))
         (next (if (zp depth) 0 (1- depth)))
         (state (f-put-global 'fn-owner-report-write-depth next state)))
    (f-put-global 'fn-owner-report-source-phase
      (cond ((equal (fn-orc-source state) :fault) :fault)
            ((zp depth) :fault)
            ((zp next) :stable)
            (t :mutating)) state)))

(defun fn-orc-writer-fault (state)
  (declare (xargs :stobjs state :guard t))
  (let* ((job (fn-orc-job state))
         (state (if (and job (not (equal (nth 7 job) :complete)))
                    (f-put-global 'fn-owner-report-job
                      (update-nth 7 :invalid job) state)
                  state)))
    (f-put-global 'fn-owner-report-source-phase :fault state)))

; Final publication checks the same registered source one last time.  The
; complete immutable buffer no longer borrows mutable Cat/arena columns.
(defun fn-orc-complete-internal (token buffer state)
  (declare (xargs :stobjs state :guard t))
  (if (fn-orc-job-readablep token state)
      (let* ((job (update-nth 8 buffer (fn-orc-job state)))
             (job (update-nth 7 :complete job)))
        (let ((state (f-put-global 'fn-owner-report-job job state)))
          (mv :report-complete state)))
    (mv :snapshot-changed state)))

(defthm fn-orc-writer-enter-denies-report-read
  (not (fn-orc-job-readablep token (fn-orc-writer-enter state)))
  :hints (("Goal" :in-theory (enable fn-orc-writer-enter
                                    fn-orc-job-readablep fn-orc-source)))
  :rule-classes nil)

; Completed pages no longer depend on mutable source stability.  This getter
; still requires the exact original registered job token, not request equality.
(defun fn-orc-completed (token state)
  (declare (xargs :stobjs state :guard t))
  (if (and (fn-orc-job-currentp token state)
           (equal (nth 7 (fn-orc-job state)) :complete))
      (mv :report-complete (nth 8 (fn-orc-job state)))
    (mv :report-unavailable nil)))
