; The reassembly job's shape (Q4a increment B, D27): the constructor and
; accessors of the job the host carries between fn-bpfj-step calls and
; offers in the (:family ... JOB LIMIT) and (:persist-result ... JOB LIMIT)
; events, and the two recognizers the receive boundary and the guards check
; of it.  fn-bpfj-jobp is what a step needs: the sweep state's shape
; (bp-fragment-resume fn-bpfr-statep), never its cells, so a 10 MiB canvas
; is not re-walked per quantum.  fn-bpfj-readable-jobp adds the cells'
; shape for the readings (bp-node-fragment-job fn-bpfj-query and above),
; which consume the cells once anyway.
;
; The job's semantics (fn-bpfj-wf, the readings, the keystones) are
; books/bp-node-fragment-job; the boundary (books/bp-node-receive-boundary)
; includes this book alone.
(in-package "ACL2")
(include-book "bp-node-machine")
(include-book "bp-fragment-resume")

(defun fn-bpfj-job (cells total sweep)
  (declare (xargs :guard t))
  (list cells total sweep))
(defun fn-bpfj-job-cells (job) (declare (xargs :guard t)) (fn-bpn-nth 0 job))
(defun fn-bpfj-job-total (job) (declare (xargs :guard t)) (fn-bpn-nth 1 job))
(defun fn-bpfj-job-sweep (job) (declare (xargs :guard t)) (fn-bpn-nth 2 job))

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

; What one step needs of a job: linear in the fragments, never in the
; canvas.
(defun fn-bpfj-jobp (job)
  (declare (xargs :guard t))
  (and (fn-bpfw-fragment-listp (fn-bpfj-job-cells job))
       (natp (fn-bpfj-job-total job))
       (fn-bpfr-statep (fn-bpfj-job-sweep job))))

; What a reading needs: the cells a true list too (checked once, where the
; reading consumes them).
(defun fn-bpfj-readable-jobp (job)
  (declare (xargs :guard t))
  (and (fn-bpfj-jobp job)
       (true-listp (nth 4 (fn-bpfj-job-sweep job)))))
