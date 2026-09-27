; The contact drain, measured (PRF-226; lane bp-cursors).  Load in an ACL2
; whose cbd is a tree with books/bp-node-job-cursor certified:
;   (ld "tools/bench/bp-drain-bench.lisp") then (bn-run N) for N ready jobs.
; A machine state holds N base jobs queued for one peer on the routed hop
; (built by the lower machine's own :enqueue and durable :persist-result
; events).  One contact is drained twice from it, asking before every offer:
;   head    fn-bpnj-contact-next  (dev: restarts at the head of the list)
;   cursor  fn-bpnjc-contact-next (this lane: resumes at the contact cursor)
; each in two modes: SEL drives the offer's outcome as the job's :forwarded
; replacement only (the selector's work), FULL drives the offer's real
; events through fn-bpnj-step (:contact-job, the durable :attempting, the
; accepted transfer, the durable :finished).  Printed per run: offers, the
; records the asks examined (a separate uncounted pass), and time$'s wall,
; run time and allocation.
(include-book "../../books/bp-node-job-cursor")
(include-book "../../books/bp-node-receive-boundary")

(defconst *bn-local* (cons :dtn '(47 47 102 110 45 97 47)))
(defconst *bn-peer* (cons :dtn '(47 47 102 110 45 98 47)))
(defconst *bn-config* (fn-bpn-config *bn-local* 3600000 2 32 1048576))
(defconst *bn-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bn-node* '(100 116 110 58 47 47 102 110 45 97 47))
(defconst *bn-table* (list (fn-bprt-route 100 "dtn://fn-b/" "relay" "dtn://relay/" 4556)))
(defconst *bn-route* (fn-bprt-job-route "dtn://fn-b/" *bn-table* *bn-node* 10 1024 1048576))
(defconst *bn-routing* (list :table *bn-table*))

(defun bn-codes (cs)
  (declare (xargs :mode :program))
  (if (endp cs) nil (cons (char-code (car cs)) (bn-codes (cdr cs)))))
(defun bn-work (i)
  (declare (xargs :mode :program))
  (cons 119 (bn-codes (explode-atom i 10))))

(defun bn-enqueue-all (base i n)
  (declare (xargs :mode :program))
  (if (>= i n)
      base
    (let* ((ev (list :enqueue (bn-work i) '(97 49) 0 (+ 7 i) *bn-route* *bn-peer* '(104 105) *bn-obs*))
           (b1 (fn-bpn-answer-state (fn-bpn-step base ev)))
           (tok (fn-bpn-machine-state-next-token b1))
           (b2 (fn-bpn-answer-state (fn-bpn-step b1 (list :persist-result tok :durable)))))
      (bn-enqueue-all b2 (+ 1 i) n))))

; The machine's own events: N :enqueue records.  The lower machine numbers
; at most *fn-bpn-machine-max-records* (4096) lifecycle records, so N plus
; two records per offer must stay below it (N <= 1,365 for a FULL drain).
(defun bn-state (n)
  (declare (xargs :mode :program))
  (let ((base (bn-enqueue-all (fn-bpn-initial-machine-state *bn-config* (+ n 16) 16777216) 0 n)))
    (fn-bpnf-with-base (fn-bpnf-initial-state *bn-config* (+ n 16) 16777216) base)))

; Above that ceiling (SEL only): one job the machine queued, copied under N
; distinct work identities into the job list (the shape N enqueues would
; leave, which the record ceiling does not let the machine reach).
(defun bn-copies (job i n acc)
  (declare (xargs :mode :program))
  (if (<= n i)
      (reverse acc)
    (bn-copies job (+ 1 i) n
               (cons (fn-bpn-make-job (bn-work i) (fn-bpn-job-attempt-id job)
                                      (fn-bpn-job-generation job) (+ 7 i)
                                      (fn-bpn-job-age-anchor job) (fn-bpn-job-peer job)
                                      (fn-bpn-job-route job) (fn-bpn-job-bundle job)
                                      (fn-bpn-job-wire job) :queued
                                      (fn-bpn-job-last-token job))
                     acc))))

(defun bn-state-copies (n)
  (declare (xargs :mode :program))
  (let* ((st1 (bn-state 1))
         (base (fn-bpnf-base st1))
         (job (car (fn-bpn-machine-state-jobs base))))
    (fn-bpnf-with-base
     st1
     (fn-bpn-state-with base (bn-copies job 0 n nil)
                        (fn-bpn-machine-state-contacts base)
                        (fn-bpn-machine-state-pending base)
                        (fn-bpn-machine-state-fenced base)
                        (fn-bpn-machine-state-next-token base)))))

; SEL: the offer's outcome as the :forwarded replacement of its job.
(defun bn-forward (st key)
  (declare (xargs :mode :program))
  (let* ((base (fn-bpnf-base st))
         (jobs (fn-bpn-machine-state-jobs base))
         (job (fn-bpn-find-job key jobs)))
    (fn-bpnf-with-base
     st
     (fn-bpn-state-with base
                        (fn-bpn-replace-job key (fn-bpn-job-with-status job :forwarded 0) jobs)
                        (fn-bpn-machine-state-contacts base)
                        (fn-bpn-machine-state-pending base)
                        (fn-bpn-machine-state-fenced base)
                        (fn-bpn-machine-state-next-token base)))))

; FULL: the offer's own events through the step the host calls.
(defun bn-drive (st key)
  (declare (xargs :mode :program))
  (let* ((p (fn-bpnf-answer-state (fn-bpnj-step st (list :contact-job *bn-peer* key))))
         (tok (fn-bpn-pending-token (fn-bpn-machine-state-pending (fn-bpnf-base p))))
         (a (fn-bpnf-answer-state (fn-bpnj-step p (list :base (list :persist-result tok :durable)))))
         (f (fn-bpnf-answer-state (fn-bpnj-step a (list :job-result key tok :accepted))))
         (tok2 (fn-bpn-pending-token (fn-bpn-machine-state-pending (fn-bpnf-base f)))))
    (fn-bpnf-answer-state (fn-bpnj-step f (list :base (list :persist-result tok2 :durable))))))

(defun bn-step (st key full)
  (declare (xargs :mode :program))
  (if full (bn-drive st key) (bn-forward st key)))

(defun bn-drain-head (st offered full count)
  (declare (xargs :mode :program))
  (let ((d (fn-bpnj-contact-next st *bn-peer* *bn-routing* offered)))
    (if (equal (car d) :offer)
        (bn-drain-head (bn-step st (caddr (cadr d)) full) (caddr d) full (+ 1 count))
      (mv count st))))

(defun bn-drain-cursor (st offered cursor full count)
  (declare (xargs :mode :program))
  (let* ((r (fn-bpnjc-contact-next st *bn-peer* *bn-routing* offered cursor))
         (d (car r)))
    (if (equal (car d) :offer)
        (bn-drain-cursor (bn-step st (caddr (cadr d)) full) (caddr d) (cdr r) full (+ 1 count))
      (mv count st))))

; Records examined, counted in a separate pass: the head ask reads the job
; list for the gate's ready-peer set (every job), then scans to the job it
; answers and reads it back by key from the head (fn-bpnj-own-entryp); the
; cursor ask reads the jobs from its position to one past its answer.
(defun bn-index (key jobs i)
  (declare (xargs :mode :program))
  (cond ((endp jobs) i)
        ((equal (fn-bpn-job-key (car jobs)) key) i)
        (t (bn-index key (cdr jobs) (+ 1 i)))))

(defun bn-count-head (st offered visits)
  (declare (xargs :mode :program))
  (let* ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
         (n (len jobs))
         (d (fn-bpnj-contact-next st *bn-peer* *bn-routing* offered)))
    (if (equal (car d) :offer)
        (let ((idx (bn-index (caddr (cadr d)) jobs 0)))
          (bn-count-head (bn-forward st (caddr (cadr d))) (caddr d) (+ visits n (* 2 (+ 1 idx)))))
      (+ visits n (if (fn-bpnp-receipt-contact-event st *bn-peer*) n 0)))))

(defun bn-count-cursor (st offered cursor visits)
  (declare (xargs :mode :program))
  (let* ((r (fn-bpnjc-contact-next st *bn-peer* *bn-routing* offered cursor))
         (d (car r))
         (here (- (nfix (cadr (cdr r))) (nfix (cadr cursor)))))
    (if (equal (car d) :offer)
        (bn-count-cursor (bn-forward st (caddr (cadr d))) (caddr d) (cdr r) (+ visits here))
      (+ visits here))))

; The same transitions without the asks (the jobs are offered in list order,
; job I at position I, as both drains offer them): the drain's wall less
; this one is the selector's share.
(defun bn-keys (i n acc)
  (declare (xargs :mode :program))
  (if (<= n i)
      (reverse acc)
    (bn-keys (+ 1 i) n (cons (list (bn-work i) '(97 49) 0) acc))))

(defun bn-transitions (st keys full count)
  (declare (xargs :mode :program))
  (if (endp keys)
      (mv count st)
    (bn-transitions (bn-step st (car keys) full) (cdr keys) full (+ 1 count))))
