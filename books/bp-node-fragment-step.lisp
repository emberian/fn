; The native service's one foundation-step extension for durable kind-18
; replacement. All ordinary events delegate to fn-bpnf-step on the same state.
(in-package "ACL2")
(include-book "bp-fnbs-family-replay")
(include-book "bp-node-fragment-job")

(set-verify-guards-eagerness 0)

(defun fn-bpnf-family-issuedp (st)
  (declare (xargs :guard t))
  (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :family))

(defun fn-bpnf-family-propose-step (st anchor-arrival observation)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (if (or (fn-bpnf-issued st)
          (fn-bpnf-waits st)
          (not (fn-frame-natp (fn-bpnf-epoch st)))
          (not (fn-frame-natp (fn-bpnf-next-op st)))
          (>= (fn-bpnf-next-op st) *fn-frame-max-nat*)
          (not (fn-frame-natp (fn-bpnf-next-arrival st)))
          (not (equal (fn-bpnf-arrival-count
                       anchor-arrival (fn-bpnf-held-list st)) 1)))
      (fn-bpnf-answer st nil)
    (let* ((anchor (fn-bpnf-find-arrival
                    anchor-arrival (fn-bpnf-held-list st)))
           (plan (fn-bpnf-family-plan-at st anchor observation))
           (record (fn-bpnf-family-record-at
                    (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                    anchor-arrival (fn-bpnf-next-arrival st)
                    (fn-bpn-nth 2 plan) observation)))
      (if (not (and (equal (car plan) :ready)
                    (fn-bpnf-family-record-atp record)
                    (not (equal (fn-bpnf-family-v1-frame record) :bad))
                    (equal (car (fn-bpnf-family-apply-at
                                 st record (fn-bpnf-next-arrival st)))
                           :ready)))
          (fn-bpnf-answer st nil)
        (fn-bpnf-answer
         (fn-bpnf-state-with-arrival
          (fn-bpnf-base st) (fn-bpnf-held-list st)
          (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
          (fn-bpnf-correlation st)
          (fn-bpnf-operation (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                             :family record :pending)
          (fn-bpnf-waits st) (fn-bpnf-epoch st)
          (1+ (fn-bpnf-next-op st))
          (1+ (fn-bpnf-next-arrival st)))
         (list (list :persist-family (fn-bpnf-epoch st)
                     (fn-bpnf-next-op st) record)))))))

(defun fn-bpnf-family-persist-step (st epoch op result)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (let ((issued (fn-bpnf-issued st)))
    (if (not (and (fn-bpnf-family-issuedp st)
                  (equal (fn-bpn-nth 5 issued) :pending)
                  (fn-bpnf-operation-matchp issued epoch op)))
        (fn-bpnf-answer st nil)
      (cond
       ((equal result :durable)
        (let* ((record (fn-bpn-nth 4 issued))
               (arrival (fn-bpn-nth 4 record))
               (applied
                (if (equal (fn-bpnf-next-arrival st) (1+ (fix arrival)))
                    (fn-bpnf-family-apply-at st record arrival)
                  (list :fault :family-frontier))))
          (if (not (equal (fn-cbor-ag-car applied) :ready))
              (fn-bpnf-answer
               (fn-bpnf-with-issued
                st (fn-bpnf-operation epoch op :family record :uncertain))
               (list (list :family-answer :uncertain)))
            (fn-bpnf-answer
             (fn-bpnf-state-with-arrival
              (fn-bpnf-base st) (fn-bpn-nth 1 applied)
              (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
              (fn-bpnf-correlation st) nil (fn-bpnf-waits st)
              (fn-bpnf-epoch st) (fn-bpnf-next-op st)
              (fn-bpnf-next-arrival st))
             (list (list :family-ready
                         (fn-bpnf-held-key
                          (fn-bpnf-held-principal (fn-bpn-nth 2 applied))
                          (fn-bpnf-held-id (fn-bpn-nth 2 applied)))))))))
       ((equal result :refused)
        (fn-bpnf-answer (fn-bpnf-with-issued st nil)
                        (list (list :family-answer :refused))))
       (t
        (fn-bpnf-answer
         (fn-bpnf-with-issued
          st (fn-bpnf-operation epoch op :family
                                (fn-bpn-nth 4 issued) :uncertain))
         (list (list :family-answer :uncertain))))))))

;; ---------------------------------------------------------------------------
;; Q4a increment B: the two steps above over the host-carried reassembly job
;; (books/bp-node-fragment-job).  fn-bpfj-plan-at / fn-bpfj-apply-at read the
;; whole image out of a finished job and refuse an image past LIMIT (the
;; profile's bundle octets) by name.  The twins equal the steps above whenever
;; the job is well-formed and finished and the image is within the limit
;; (fn-bpfj-plan-at-is-the-plan-at, fn-bpfj-apply-at-is-the-apply-at); a stale
;; or unfinished job plans as (:stale :job) / (:pending :job), which is no
;; effect and no fault: the host starts the job again.  Both stay enabled so
;; every proof over fn-bpnf-fragment-step sees the same shapes as before.

(defun fn-bpfj-propose-step (st anchor-arrival observation job limit)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (fn-bpfj-readable-jobp job))
                  :verify-guards nil))
  (if (or (fn-bpnf-issued st)
          (fn-bpnf-waits st)
          (not (fn-frame-natp (fn-bpnf-epoch st)))
          (not (fn-frame-natp (fn-bpnf-next-op st)))
          (>= (fn-bpnf-next-op st) *fn-frame-max-nat*)
          (not (fn-frame-natp (fn-bpnf-next-arrival st)))
          (not (equal (fn-bpnf-arrival-count
                       anchor-arrival (fn-bpnf-held-list st)) 1)))
      (fn-bpnf-answer st nil)
    (let* ((anchor (fn-bpnf-find-arrival
                    anchor-arrival (fn-bpnf-held-list st)))
           (plan (fn-bpfj-plan-at st anchor observation job limit))
           (record (fn-bpnf-family-record-at
                    (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                    anchor-arrival (fn-bpnf-next-arrival st)
                    (fn-bpn-nth 2 plan) observation)))
      (if (not (and (equal (car plan) :ready)
                    (fn-bpnf-family-record-atp record)
                    (not (equal (fn-bpnf-family-v1-frame record) :bad))
                    (equal (car (fn-bpfj-apply-at
                                 st record (fn-bpnf-next-arrival st) job limit))
                           :ready)))
          (fn-bpnf-answer st nil)
        (fn-bpnf-answer
         (fn-bpnf-state-with-arrival
          (fn-bpnf-base st) (fn-bpnf-held-list st)
          (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
          (fn-bpnf-correlation st)
          (fn-bpnf-operation (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                             :family record :pending)
          (fn-bpnf-waits st) (fn-bpnf-epoch st)
          (1+ (fn-bpnf-next-op st))
          (1+ (fn-bpnf-next-arrival st)))
         (list (list :persist-family (fn-bpnf-epoch st)
                     (fn-bpnf-next-op st) record)))))))

(defun fn-bpfj-persist-step (st epoch op result job limit)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (fn-bpfj-readable-jobp job))
                  :verify-guards nil))
  (let ((issued (fn-bpnf-issued st)))
    (if (not (and (fn-bpnf-family-issuedp st)
                  (equal (fn-bpn-nth 5 issued) :pending)
                  (fn-bpnf-operation-matchp issued epoch op)))
        (fn-bpnf-answer st nil)
      (cond
       ((equal result :durable)
        (let* ((record (fn-bpn-nth 4 issued))
               (arrival (fn-bpn-nth 4 record))
               (applied
                (if (equal (fn-bpnf-next-arrival st) (1+ (fix arrival)))
                    (fn-bpfj-apply-at st record arrival job limit)
                  (list :fault :family-frontier))))
          (if (not (equal (fn-cbor-ag-car applied) :ready))
              (fn-bpnf-answer
               (fn-bpnf-with-issued
                st (fn-bpnf-operation epoch op :family record :uncertain))
               (list (list :family-answer :uncertain)))
            (fn-bpnf-answer
             (fn-bpnf-state-with-arrival
              (fn-bpnf-base st) (fn-bpn-nth 1 applied)
              (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
              (fn-bpnf-correlation st) nil (fn-bpnf-waits st)
              (fn-bpnf-epoch st) (fn-bpnf-next-op st)
              (fn-bpnf-next-arrival st))
             (list (list :family-ready
                         (fn-bpnf-held-key
                          (fn-bpnf-held-principal (fn-bpn-nth 2 applied))
                          (fn-bpnf-held-id (fn-bpn-nth 2 applied)))))))))
       ((equal result :refused)
        (fn-bpnf-answer (fn-bpnf-with-issued st nil)
                        (list (list :family-answer :refused))))
       (t
        (fn-bpnf-answer
         (fn-bpnf-with-issued
          st (fn-bpnf-operation epoch op :family
                                (fn-bpn-nth 4 issued) :uncertain))
         (list (list :family-answer :uncertain))))))))

;; The record's anchor is the anchor the proposal was made for.
(defthm fn-bpfj-record-anchor-of-family-record-at
  (equal (fn-bpfj-record-anchor
          st (fn-bpnf-family-record-at epoch op anchor-arrival
                                       whole-arrival wire observation))
         (fn-bpnf-find-arrival anchor-arrival (fn-bpnf-held-list st)))
  :hints (("Goal" :in-theory (enable fn-bpfj-record-anchor
                                     fn-bpnf-family-record-at fn-bpn-nth))))

;; KEYSTONE (Q4a increment B).  Within the limit, a finished well-formed job
;; proposes exactly what the whole-family step proposes.
(defthm fn-bpfj-propose-step-is-the-propose-step
  (implies (and (fn-bpfj-wf st (fn-bpnf-find-arrival
                                anchor-arrival (fn-bpnf-held-list st))
                            job)
                (fn-bpfj-finishedp job)
                (natp limit)
                (<= limit *fn-bpnf-max-held-image*)
                (<= (fn-bpfj-image-octets
                     st (fn-bpnf-find-arrival anchor-arrival (fn-bpnf-held-list st)))
                    limit))
           (equal (fn-bpfj-propose-step st anchor-arrival observation job limit)
                  (fn-bpnf-family-propose-step st anchor-arrival observation)))
  :hints (("Goal" :in-theory (e/d (fn-bpfj-propose-step
                                   fn-bpnf-family-propose-step
                                   fn-bpfj-plan-at-is-the-plan-at
                                   fn-bpfj-apply-at-is-the-apply-at
                                   fn-bpfj-record-anchor-of-family-record-at)
                                  (fn-bpnf-family-plan-at
                                   fn-bpnf-family-apply-at
                                   fn-bpnf-family-record-at
                                   fn-bpnf-family-record-atp
                                   fn-bpnf-family-v1-frame
                                   fn-bpnf-state-with-arrival
                                   fn-bpnf-answer fn-bpnf-operation)))))

;; KEYSTONE (Q4a increment B).  The same for the persist step.
(defthm fn-bpfj-persist-step-is-the-persist-step
  (implies (and (fn-bpfj-wf st (fn-bpfj-record-anchor
                                st (fn-bpn-nth 4 (fn-bpnf-issued st)))
                            job)
                (fn-bpfj-finishedp job)
                (natp limit)
                (<= limit *fn-bpnf-max-held-image*)
                (<= (fn-bpfj-image-octets
                     st (fn-bpfj-record-anchor
                         st (fn-bpn-nth 4 (fn-bpnf-issued st))))
                    limit))
           (equal (fn-bpfj-persist-step st epoch op result job limit)
                  (fn-bpnf-family-persist-step st epoch op result)))
  :hints (("Goal" :in-theory (e/d (fn-bpfj-persist-step
                                   fn-bpnf-family-persist-step
                                   fn-bpfj-apply-at-is-the-apply-at)
                                  (fn-bpnf-family-apply-at
                                   fn-bpnf-state-with-arrival
                                   fn-bpnf-with-issued
                                   fn-bpnf-answer fn-bpnf-operation
                                   fn-bpnf-operation-matchp
                                   fn-bpnf-family-issuedp)))))

;; A ready job plan, like a ready family plan, binds live source rows.
(defthm fn-bpfj-plan-at-ready-binds-live-source-rows
  (implies (equal (car (fn-bpfj-plan-at st anchor observation job limit))
                  :ready)
           (fn-bpnf-family-rows-livep
            (fn-bpnf-active-set st anchor) observation))
  :hints (("Goal" :in-theory (enable fn-bpfj-plan-at))))

(defun fn-bpnf-fragment-step (st event)
  (declare (xargs :guard
                  (and (fn-bpn-machine-statep (fn-bpnf-base st))
                       (or (not (equal (fn-cbor-ag-car event) :base))
                           (fn-bpn-machine-eventp (fn-bpn-nth 1 event)))
                       (or (not (equal (fn-cbor-ag-car event) :recover-fnbs))
                           (and (true-listp (fn-bpn-nth 2 event))
                                (<= (len (fn-bpn-nth 2 event))
                                    *fn-bpn-machine-max-records*)))
                       ;; A carried job is readable (the boundary's check,
                       ;; books/bp-node-receive-boundary fn-bpnf-host-eventp).
                       (or (not (equal (fn-cbor-ag-car event) :family))
                           (not (fn-bpn-nth 3 event))
                           (fn-bpfj-readable-jobp (fn-bpn-nth 3 event)))
                       (or (not (equal (fn-cbor-ag-car event) :persist-result))
                           (not (fn-bpn-nth 4 event))
                           (fn-bpfj-readable-jobp (fn-bpn-nth 4 event))))
                  :verify-guards nil))
  (cond
   ((equal (fn-cbor-ag-car event) :recover-fnbs)
    (fn-bpnf-step st event))
   ((and (fn-bpnf-family-issuedp st)
         (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain))
    (fn-bpnf-answer st nil))
   ((and (fn-bpnf-family-issuedp st)
         (equal (fn-cbor-ag-car event) :persist-result))
    ;; (:persist-result EPOCH OP RESULT JOB LIMIT) carries the host's job.
    (if (fn-bpn-nth 4 event)
        (fn-bpfj-persist-step
         st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event) (fn-bpn-nth 3 event)
         (fn-bpn-nth 4 event) (fn-bpn-nth 5 event))
      (fn-bpnf-family-persist-step
       st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event) (fn-bpn-nth 3 event))))
   ((equal (fn-cbor-ag-car event) :family)
    ;; (:family ANCHOR-ARRIVAL OBSERVATION JOB LIMIT) carries the host's job.
    (if (fn-bpn-nth 3 event)
        (fn-bpfj-propose-step
         st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
         (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))
      (fn-bpnf-family-propose-step
       st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event))))
   (t (fn-bpnf-step st event))))

;; Every member of one family selects the same rows, so it has the same plan.
(defthm fn-bpnf-same-family-agrees
  (implies (fn-bpnf-same-fragment-family-p a b)
           (equal (fn-bpnf-same-fragment-family-p x a)
                  (fn-bpnf-same-fragment-family-p x b)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-same-fragment-family-p)
                              (theory 'minimal-theory)))))

(defthm fn-bpnf-same-family-selects-same-rows
  (implies (fn-bpnf-same-fragment-family-p a b)
           (equal (fn-bpnf-active-set-rows held a)
                  (fn-bpnf-active-set-rows held b)))
  :hints (("Goal" :induct (fn-bpnf-active-set-rows held a)
           :in-theory (disable fn-bpnf-same-fragment-family-p))))

(defthm fn-bpnf-same-family-same-total
  (implies (fn-bpnf-same-fragment-family-p a b)
           (equal (fn-bpp-total-adu-length
                   (fn-bpb-bundle-primary (fn-bpnf-held-bundle a)))
                  (fn-bpp-total-adu-length
                   (fn-bpb-bundle-primary (fn-bpnf-held-bundle b)))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-same-fragment-family-p
                                fn-bpnf-fragment-coherence-key car-cons)
                              (theory 'minimal-theory)))))

(defthm fn-bpnf-same-family-members-are-active
  (implies (fn-bpnf-same-fragment-family-p a b)
           (and (fn-bpnf-active-fragmentp a) (fn-bpnf-active-fragmentp b)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-same-fragment-family-p)
                              (theory 'minimal-theory))))
  :rule-classes :forward-chaining)

(defthm fn-bpnf-active-set-of-member
  (implies (and (fn-bpnf-same-fragment-family-p a b)
                (member-equal a (fn-bpnf-held-list st))
                (member-equal b (fn-bpnf-held-list st)))
           (equal (fn-bpnf-active-set st a) (fn-bpnf-active-set st b)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-active-set fn-bpnf-family-member)
                              (theory 'minimal-theory))
           :use ((:instance fn-bpnf-same-family-selects-same-rows
                            (held (fn-bpnf-held-list st)))
                 (:instance fn-bpnf-same-family-members-are-active)))))

(defthm fn-bpnf-fragment-query-of-member
  (implies (and (fn-bpnf-same-fragment-family-p a b)
                (member-equal a (fn-bpnf-held-list st))
                (member-equal b (fn-bpnf-held-list st)))
           (equal (fn-bpnf-fragment-query st a) (fn-bpnf-fragment-query st b)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-fragment-query fn-bpnf-family-member)
                              (theory 'minimal-theory))
           :use ((:instance fn-bpnf-active-set-of-member)
                 (:instance fn-bpnf-same-family-same-total)
                 (:instance fn-bpnf-same-family-members-are-active)))))

(defthm fn-bpnf-family-plan-at-of-member
  (implies (and (fn-bpnf-same-fragment-family-p a b)
                (member-equal a (fn-bpnf-held-list st))
                (member-equal b (fn-bpnf-held-list st)))
           (equal (fn-bpnf-family-plan-at st a observation)
                  (fn-bpnf-family-plan-at st b observation)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-family-plan-at fn-bpnf-family-plan)
                              (theory 'minimal-theory))
           :use ((:instance fn-bpnf-active-set-of-member)
                 (:instance fn-bpnf-fragment-query-of-member)))))

(in-theory (disable fn-bpnf-same-family-agrees
                    fn-bpnf-same-family-selects-same-rows
                    fn-bpnf-same-family-same-total
                    fn-bpnf-same-family-members-are-active
                    fn-bpnf-active-set-of-member
                    fn-bpnf-fragment-query-of-member
                    fn-bpnf-family-plan-at-of-member))

;; A plan is ready only with the family's offset-zero row
;; (fn-bpnf-family-ready-has-valid-whole).
(defthm fn-bpnf-family-without-offset-zero-is-not-ready
  (implies (not (fn-bpnf-offset-zero-source (fn-bpnf-active-set st h)))
           (not (equal (fn-cbor-ag-car (fn-bpnf-family-plan-at st h observation))
                       :ready)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-family-ready-has-valid-whole
                            (anchor h)))
           :in-theory (union-theories
                       '(fn-bpnf-family-plan-at fn-cbor-ag-car car-cons)
                       (theory 'minimal-theory)))))

(in-theory (disable fn-bpnf-family-without-offset-zero-is-not-ready))

;; PRF-136: the served selector reads each row's primary block only and plans
;; (and so re-encodes) nothing: a row is a candidate only when its family holds
;; an offset-zero fragment, because a family without one is never ready
;; (fn-bpnf-family-without-offset-zero-is-not-ready).  Which families hold one
;; is one pass over the headers (fn-bpnf-zero-family-keys).

;; A row that may be an active fragment, read from its primary block alone:
;; every active fragment is one (fn-bpnf-active-fragment-is-candidate).
(defun fn-bpnf-fragment-candidatep (h)
  (declare (xargs :guard t))
  (let ((primary (fn-bpb-bundle-primary (fn-bpnf-held-bundle h))))
    (and (true-listp h)
         (fn-bpp-blockp primary)
         (fn-bpp-fragmentp (fn-bpp-flags primary))
         (not (nth 14 h))
         (not (equal (nth 12 h) :reassembly-consumed)))))

;; The fields fn-bpnf-same-fragment-family-p compares.
(defun fn-bpnf-fragment-family-key (h)
  (declare (xargs :guard (fn-bpp-blockp
                          (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
                  :verify-guards nil))
  (let ((primary (fn-bpb-bundle-primary (fn-bpnf-held-bundle h))))
    (list (fn-bpnf-held-principal h)
          (fn-bpp-adu-key primary)
          (fn-bpnf-fragment-coherence-key primary))))

; Executes by a loop (lane depth-debt, PRF-919): the recursion took one
; control-stack frame per element of the held rows (data, not a bound).  The :logic is
; the recursion, unchanged; the :exec is a loop, equal by fn-bpnf-zero-family-keys-loop-is-rev-onto.
(defun fn-bpnf-zero-family-keys-loop (held acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp held)
      (let ((h (car held)))
        (fn-bpnf-zero-family-keys-loop
         (cdr held)
         (if (and (fn-bpnf-fragment-candidatep h)
                  (equal (fn-bpp-fragment-offset
                          (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
                         0))
             (cons (fn-bpnf-fragment-family-key h) acc)
           acc)))
    (fn-ag-rev-onto acc nil)))

(defun fn-bpnf-zero-family-keys (held)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp held)
                  (let ((h (car held)))
                    (if (and (fn-bpnf-fragment-candidatep h)
                             (equal (fn-bpp-fragment-offset
                                     (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
                                    0))
                        (cons (fn-bpnf-fragment-family-key h)
                              (fn-bpnf-zero-family-keys (cdr held)))
                      (fn-bpnf-zero-family-keys (cdr held))))
                nil)
       :exec (fn-bpnf-zero-family-keys-loop held nil)))

(defthm fn-bpnf-zero-family-keys-loop-is-rev-onto
  (equal (fn-bpnf-zero-family-keys-loop held acc)
         (fn-ag-rev-onto acc (fn-bpnf-zero-family-keys held)))
  :hints (("Goal" :induct (fn-bpnf-zero-family-keys-loop held acc)
                  :in-theory (union-theories
                              '(fn-bpnf-zero-family-keys-loop fn-bpnf-zero-family-keys fn-ag-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(local
 (defthm fn-bpnf-heldp-row-shape
   (implies (fn-bpnf-heldp h)
            (and (true-listp h)
                 (fn-bpp-blockp (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))))
   :hints (("Goal" :in-theory (e/d (fn-bpnf-heldp fn-bpb-bundlep)
                                   (fn-bpp-blockp fn-bpb-encode))))
   :rule-classes nil))

(defthm fn-bpnf-active-fragment-is-candidate
  (implies (fn-bpnf-active-fragmentp h)
           (fn-bpnf-fragment-candidatep h))
  :hints (("Goal" :in-theory (e/d (fn-bpnf-active-fragmentp
                                   fn-bpnf-fragment-candidatep)
                                  (fn-bpnf-heldp fn-bpp-blockp
                                   fn-bpp-fragmentp fn-bpnf-held-bundle))
           :use ((:instance fn-bpnf-heldp-row-shape)))))

(defthm fn-bpnf-same-family-is-key-equality
  (equal (fn-bpnf-same-fragment-family-p a b)
         (and (fn-bpnf-active-fragmentp a)
              (fn-bpnf-active-fragmentp b)
              (equal (fn-bpnf-fragment-family-key a)
                     (fn-bpnf-fragment-family-key b))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-same-fragment-family-p
                                fn-bpnf-fragment-family-key
                                cons-equal)
                              (theory 'minimal-theory))))
  :rule-classes nil)

(local
 (defthm fn-bpnf-zero-key-covers-offset-zero-source
   (implies (and (fn-bpnf-active-fragmentp h)
                 (not (member-equal (fn-bpnf-fragment-family-key h)
                                    (fn-bpnf-zero-family-keys rows))))
            (not (fn-bpnf-offset-zero-source
                  (fn-bpnf-active-set-rows rows h))))
   :hints (("Goal" :induct (fn-bpnf-zero-family-keys rows)
            :in-theory (union-theories
                        '(fn-bpnf-active-set-rows fn-bpnf-offset-zero-source
                          fn-bpnf-zero-family-keys member-equal
                          car-cons cdr-cons)
                        (theory 'minimal-theory)))
           ("Subgoal *1/2" :use ((:instance fn-bpnf-same-family-is-key-equality
                                            (a (car rows)) (b h))
                                 (:instance fn-bpnf-active-fragment-is-candidate
                                            (h (car rows)))))
           ("Subgoal *1/1" :use ((:instance fn-bpnf-same-family-is-key-equality
                                            (a (car rows)) (b h))
                                 (:instance fn-bpnf-active-fragment-is-candidate
                                            (h (car rows))))))))

;; A held active row whose family holds no offset-zero candidate is not ready.
(defthm fn-bpnf-family-without-zero-key-is-not-ready
  (implies (and (fn-bpnf-active-fragmentp h)
                (member-equal h (fn-bpnf-held-list st))
                (not (member-equal (fn-bpnf-fragment-family-key h)
                                   (fn-bpnf-zero-family-keys
                                    (fn-bpnf-held-list st)))))
           (not (equal (fn-cbor-ag-car
                        (fn-bpnf-family-plan-at st h observation))
                       :ready)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-family-without-offset-zero-is-not-ready)
                 (:instance fn-bpnf-zero-key-covers-offset-zero-source
                            (rows (fn-bpnf-held-list st))))
           :in-theory (union-theories
                       '(fn-bpnf-active-set fn-bpnf-family-member)
                       (theory 'minimal-theory)))))

(defthm fn-bpnf-zero-family-keys-bound
  (<= (len (fn-bpnf-zero-family-keys held)) (len held))
  :hints (("Goal" :induct (fn-bpnf-zero-family-keys held)
           :in-theory (union-theories '(fn-bpnf-zero-family-keys len
                                        car-cons cdr-cons)
                                      (theory 'minimal-theory))))
  :rule-classes :linear)

(in-theory (disable fn-bpnf-family-without-zero-key-is-not-ready))

;; ---------------------------------------------------------------------------
;; Q4a increment B: the candidate a job is started for.  The selector
;; reassembles nothing: the first family not in TRIED that is active, unique at its
;; arrival, live, and holds an offset-zero source.  Its plan is read from the
;; finished job by fn-bpfj-propose-step; a family whose plan is not ready is
;; added to TRIED by the host and the selector is asked again.

;; Inspection sweep 2026-10-03 S008: a family is a candidate only once the
;; payload octets its rows hold reach the total ADU length its offset-zero
;; row declares.  The reassembly sweep walks every position of that declared
;; total; before this gate it ran after every accepted bundle for every
;; incomplete family, so the work was the DECLARED total per family per
;; arrival (a 10 MiB ADU in 4 KiB fragments: about 2.6e10 positions; one-
;; octet families declaring 2^24: 16M positions each, per arrival).  With
;; it, a family is swept only when it can be complete, and that sweep walks
;; no more positions than the octets the family holds.
(defun fn-bpfj-rows-payload-octets (rows acc)
  (declare (xargs :guard (and (natp acc) (fn-bpnf-all-heldp rows))))
  (if (consp rows)
      (fn-bpfj-rows-payload-octets
       (cdr rows)
       (+ acc (len (fn-bpb-payload (fn-bpnf-held-bundle (car rows))))))
    acc))

(defun fn-bpfj-family-coveredp (st anchor)
  (declare (xargs :guard (fn-bpnf-fragment-candidatep anchor)))
  (<= (nfix (fn-bpp-total-adu-length
             (fn-bpb-bundle-primary (fn-bpnf-held-bundle anchor))))
      (fn-bpfj-rows-payload-octets (fn-bpnf-active-set st anchor) 0)))

(defun fn-bpfj-candidate (st held observation tried zero)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (true-listp tried) (true-listp zero))
                  :measure (acl2-count held)
                  :verify-guards nil))
  (if (consp held)
      (let ((h (car held)))
        (if (not (fn-bpnf-fragment-candidatep h))
            (fn-bpfj-candidate st (cdr held) observation tried zero)
          (let ((key (fn-bpnf-fragment-family-key h)))
            (if (or (not (member-equal key zero))
                    (member-equal key tried))
                (fn-bpfj-candidate st (cdr held) observation tried zero)
              (if (and (fn-bpnf-active-fragmentp h)
                       (equal (fn-bpnf-arrival-count
                               (fn-bpn-nth 3 h) (fn-bpnf-held-list st)) 1)
                       (fn-bpnf-family-rows-livep
                        (fn-bpnf-active-set st h) observation)
                       (fn-bpfj-family-coveredp st h))
                  (list :ready (fn-bpn-nth 3 h) key)
                (fn-bpfj-candidate st (cdr held) observation
                                   (cons key tried) zero))))))
    nil))

(defun fn-bpfj-next-candidate (st observation tried)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (true-listp tried))
                  :verify-guards nil))
  (if (or (fn-bpnf-issued st) (fn-bpnf-waits st)
          (not (fn-frame-natp (fn-bpnf-next-arrival st))))
      nil
    (fn-bpfj-candidate st (fn-bpnf-held-list st) observation tried
                       (fn-bpnf-zero-family-keys (fn-bpnf-held-list st)))))

; The row the selector tests for a family: the family's first candidate row.
(defun fn-bpfj-family-rep (key rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (if (and (fn-bpnf-fragment-candidatep (car rows))
               (equal (fn-bpnf-fragment-family-key (car rows)) key))
          (car rows)
        (fn-bpfj-family-rep key (cdr rows)))
    nil))

; A row a job can be started for: an active fragment, unique at its arrival,
; whose family's source rows are live and cover the declared total.
(defun fn-bpfj-row-readyp (st h observation)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bpnf-active-fragmentp h)
       (equal (fn-bpnf-arrival-count (fn-bpn-nth 3 h) (fn-bpnf-held-list st)) 1)
       (fn-bpnf-family-rows-livep (fn-bpnf-active-set st h) observation)
       (fn-bpfj-family-coveredp st h)))

; Some family in KEYS, not in TRIED, has a ready representative among ROWS.
(defun fn-bpfj-any-ready-rep (keys st rows observation tried)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp keys)
      (or (and (not (member-equal (car keys) tried))
               (let ((h (fn-bpfj-family-rep (car keys) rows)))
                 (and h (fn-bpfj-row-readyp st h observation))))
          (fn-bpfj-any-ready-rep (cdr keys) st rows observation tried))
    nil))


; Proof support for the keystone below.

(local
 (defthm bpfj-rep-of-cons
   (equal (fn-bpfj-family-rep key (cons h rest))
          (if (and (fn-bpnf-fragment-candidatep h)
                   (equal (fn-bpnf-fragment-family-key h) key))
              h
            (fn-bpfj-family-rep key rest)))))

(local
 (defthm bpfj-any-ready-rep-skip
   ; The head is not the representative of any family still asked about.
   (implies (and (fn-bpnf-fragment-candidatep h)
                 (or (not (member-equal (fn-bpnf-fragment-family-key h) keys))
                     (member-equal (fn-bpnf-fragment-family-key h) tried)))
            (equal (fn-bpfj-any-ready-rep keys st (cons h rest) observation tried)
                   (fn-bpfj-any-ready-rep keys st rest observation tried)))
   :hints (("Goal" :induct (fn-bpfj-any-ready-rep keys st rest observation tried)
            :in-theory (e/d (fn-bpfj-any-ready-rep) (fn-bpfj-row-readyp fn-bpnf-fragment-candidatep fn-bpnf-fragment-family-key))))))

(local
 (defthm bpfj-any-ready-rep-non-candidate
   (implies (not (fn-bpnf-fragment-candidatep h))
            (equal (fn-bpfj-any-ready-rep keys st (cons h rest) observation tried)
                   (fn-bpfj-any-ready-rep keys st rest observation tried)))
   :hints (("Goal" :induct (fn-bpfj-any-ready-rep keys st rest observation tried)
            :in-theory (e/d (fn-bpfj-any-ready-rep) (fn-bpfj-row-readyp fn-bpnf-fragment-candidatep fn-bpnf-fragment-family-key))))))

(local
 (defthm bpfj-any-ready-rep-ready-head
   (implies (and (fn-bpnf-fragment-candidatep h)
                 (member-equal (fn-bpnf-fragment-family-key h) keys)
                 (not (member-equal (fn-bpnf-fragment-family-key h) tried))
                 (fn-bpfj-row-readyp st h observation))
            (fn-bpfj-any-ready-rep keys st (cons h rest) observation tried))
   :hints (("Goal" :induct (fn-bpfj-any-ready-rep keys st rest observation tried)
            :in-theory (e/d (fn-bpfj-any-ready-rep) (fn-bpfj-row-readyp fn-bpnf-fragment-candidatep fn-bpnf-fragment-family-key))))))


(local
 (defun bpfj-keys-ind (keys)
   (declare (xargs :guard t))
   (if (consp keys) (bpfj-keys-ind (cdr keys)) nil)))

(local
 (defthm bpfj-any-ready-rep-unready-head
   (implies (and (fn-bpnf-fragment-candidatep h)
                 (equal k (fn-bpnf-fragment-family-key h))
                 (not (fn-bpfj-row-readyp st h observation)))
            (equal (fn-bpfj-any-ready-rep keys st (cons h rest) observation tried)
                   (fn-bpfj-any-ready-rep keys st rest observation (cons k tried))))
   :hints (("Goal" :induct (bpfj-keys-ind keys)
            :in-theory (e/d (fn-bpfj-any-ready-rep)
                            (fn-bpfj-row-readyp fn-bpnf-fragment-candidatep fn-bpnf-fragment-family-key))))))


(local
 (defthm bpfj-any-ready-rep-of-atom-rows
   (implies (not (consp rows))
            (not (fn-bpfj-any-ready-rep keys st rows observation tried)))
   :hints (("Goal" :induct (bpfj-keys-ind keys)
            :in-theory (e/d (fn-bpfj-any-ready-rep fn-bpfj-family-rep) (fn-bpfj-row-readyp))))))


(local
 (defthm bpfj-candidate-iff-any-ready-rep
   (iff (fn-bpfj-candidate st held observation tried zero)
        (fn-bpfj-any-ready-rep zero st held observation tried))
   :hints (("Goal" :induct (fn-bpfj-candidate st held observation tried zero)
            :in-theory (e/d () (fn-bpfj-candidate fn-bpnf-fragment-candidatep
                                fn-bpnf-fragment-family-key fn-bpfj-any-ready-rep
                                fn-bpfj-family-rep fn-bpfj-family-coveredp fn-bpnf-active-fragmentp fn-bpnf-active-set fn-bpnf-held-list fn-bpnf-arrival-count fn-bpnf-family-rows-livep fn-bpnf-heldp ) ((:induction fn-bpfj-candidate)))
            :expand ((fn-bpfj-candidate st held observation tried zero))))))


(local
 (defthm bpfj-candidate-sound
   (implies (fn-bpfj-candidate st held observation tried zero)
            (let* ((r (fn-bpfj-candidate st held observation tried zero))
                   (k (fn-bpn-nth 2 r))
                   (h (fn-bpfj-family-rep k held)))
              (and (equal (car r) :ready)
                   (member-equal k zero)
                   (not (member-equal k tried))
                   h
                   (equal (fn-bpn-nth 3 h) (fn-bpn-nth 1 r))
                   (fn-bpfj-row-readyp st h observation))))
   :hints (("Goal" :induct (fn-bpfj-candidate st held observation tried zero)
            :in-theory (e/d () (fn-bpfj-candidate fn-bpnf-fragment-candidatep
                                fn-bpnf-fragment-family-key fn-bpfj-any-ready-rep
                                fn-bpfj-family-rep fn-bpfj-family-coveredp fn-bpnf-active-fragmentp fn-bpnf-active-set fn-bpnf-held-list fn-bpnf-arrival-count fn-bpnf-family-rows-livep fn-bpnf-heldp ) ((:induction fn-bpfj-candidate)))
            :expand ((fn-bpfj-candidate st held observation tried zero))))))


; KEYSTONE (PRF-1051, with PRF-121, PRF-134, PRF-136).  The family the host
; asks for: host/native/bp-service.lisp fnn-bps-fragment-effects asks
; fn-bpfj-next-candidate.  It answers nil unless nothing is issued, the
; machine does not wait and the next arrival is in frame; then it tests each
; family in TRIED's complement that holds an offset-zero fragment at its
; REPRESENTATIVE (the family's first candidate row, read from headers alone)
; and answers (:ready ARRIVAL KEY) for the first family whose representative is
; READY: an active fragment, unique at its arrival, whose family's source rows
; are live under the observation and cover the declared total.  The answer is
; non-nil exactly when some such family exists, and a non-nil answer names a
; zero-sourced family not in TRIED and the arrival of its ready
; representative.  (Which ready family comes first is the held order; the host
; adds a family whose plan is then not ready to TRIED and asks again.)
(defthm fn-bpfj-next-candidate-is-a-ready-family-representative
  (let* ((held (fn-bpnf-held-list st))
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
                         (fn-bpfj-row-readyp st h observation))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpfj-candidate-iff-any-ready-rep
                  (held (fn-bpnf-held-list st))
                  (zero (fn-bpnf-zero-family-keys (fn-bpnf-held-list st))))
                 (:instance bpfj-candidate-sound
                  (held (fn-bpnf-held-list st))
                  (zero (fn-bpnf-zero-family-keys (fn-bpnf-held-list st)))))
           :in-theory (e/d (fn-bpfj-next-candidate)
                           (fn-bpfj-candidate fn-bpfj-any-ready-rep fn-bpfj-family-rep
                            fn-bpfj-row-readyp bpfj-candidate-iff-any-ready-rep
                            bpfj-candidate-sound fn-bpnf-held-list fn-bpnf-zero-family-keys
                            fn-bpnf-issued fn-bpnf-waits fn-bpnf-next-arrival fn-frame-natp)))))

(defthm fn-bpnf-fragment-step-delegates-ordinary-events
  (implies (and (not (fn-bpnf-family-issuedp st))
                (not (equal (fn-cbor-ag-car event) :family)))
           (equal (fn-bpnf-fragment-step st event)
                  (fn-bpnf-step st event)))
  :hints (("Goal" :in-theory (disable fn-bpnf-step)))
  :rule-classes nil)

(defthm fn-bpnf-family-proposal-retains-held
  (equal (fn-bpnf-held-list
          (fn-bpnf-answer-state
           (fn-bpnf-family-propose-step st anchor-arrival observation)))
         (fn-bpnf-held-list st))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpnf-family-plan-at
                               fn-bpnf-family-apply-at
                               fn-bpnf-family-v1-frame
                               fn-bpnf-family-record-atp)))
  :rule-classes nil)

(defthm fn-bpnf-fragment-step-family-publication-has-live-sources
  (implies (and (equal (fn-cbor-ag-car event) :family)
                (equal (fn-cbor-ag-car
                        (car (fn-bpnf-answer-effects
                              (fn-bpnf-fragment-step st event))))
                       :persist-family))
           (fn-bpnf-family-rows-livep
            (fn-bpnf-active-set
             st (fn-bpnf-find-arrival
                 (fn-bpn-nth 1 event) (fn-bpnf-held-list st)))
            (fn-bpn-nth 2 event)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance
                  fn-bpnf-family-plan-at-ready-binds-live-source-rows
                  (anchor (fn-bpnf-find-arrival
                           (fn-bpn-nth 1 event) (fn-bpnf-held-list st)))
                  (observation (fn-bpn-nth 2 event)))
                 ;; The job form (Q4a increment B) routes to
                 ;; fn-bpfj-propose-step, whose plan is fn-bpfj-plan-at.
                 (:instance
                  fn-bpfj-plan-at-ready-binds-live-source-rows
                  (anchor (fn-bpnf-find-arrival
                           (fn-bpn-nth 1 event) (fn-bpnf-held-list st)))
                  (observation (fn-bpn-nth 2 event))
                  (job (fn-bpn-nth 3 event))
                  (limit (fn-bpn-nth 4 event))))
           :in-theory (disable fn-bpnf-family-plan-at
                               fn-bpfj-plan-at fn-bpfj-apply-at
                               fn-bpnf-family-apply-at
                               fn-bpnf-family-v1-frame
                               fn-bpnf-family-record-atp
                               fn-bpnf-active-set
                               ;; The used lemma's conclusion is the goal's;
                               ;; opening it (and the held expiry under it)
                               ;; cost 3.3M steps of useless rewriting.
                               fn-bpnf-family-rows-livep
                               fn-bpah-held-expiry
                               fn-bpnf-heldp
                               fn-bpnf-ingress-principal)))
  :rule-classes nil)

