; One physical FNBS directory carries legacy outbound rows and received
; kind-5 rows.  ACL2, not the host, partitions bounded final names before
; the legacy contiguous planner and kind-5 byte replay validate each subset.
(in-package "ACL2")
(include-book "bp-fnbs-codec")

(set-verify-guards-eagerness 0)

(defun fn-bpnf-namespace-max-entries ()
  (declare (xargs :guard t))
  (+ (* 2 *fn-bpn-machine-max-records*)
     *fn-bpn-lifecycle-max-hidden-stages*))

(defun fn-bpnf-legacy-name-candidatep (name)
  (declare (xargs :guard t))
  (and (stringp name)
       (let ((chars (coerce name 'list)))
         (and (equal (len chars) 24)
              (fn-bs-txn-digit-char-listp (take 20 chars))
              (equal (nth 20 chars) #\.)
              (equal (nth 21 chars) #\f)
              (equal (nth 22 chars) #\n)
              (equal (nth 23 chars) #\b)))))

(defun fn-bpnf-kind-five-name-candidatep (name)
  (declare (xargs :guard t))
  (and (stringp name)
       (let ((chars (coerce name 'list)))
         (and (equal (len chars) 45)
              (fn-bs-txn-digit-char-listp (take 20 chars))
              (equal (nth 20 chars) #\-)
              (fn-bs-txn-digit-char-listp (take 20 (nthcdr 21 chars)))
              (equal (nth 41 chars) #\.)
              (equal (nth 42 chars) #\f)
              (equal (nth 43 chars) #\n)
              (equal (nth 44 chars) #\b)))))

(defun fn-bpnf-namespace-plan-aux (names legacy received hidden)
  (declare (xargs :guard t :measure (acl2-count names)))
  (if (atom names)
      (if (null names)
          (list :ready (fn-bpn-lifecycle-reverse legacy)
                (fn-bpn-lifecycle-reverse received)
                (fn-bpn-lifecycle-reverse hidden))
        (list :fault :improper-namespace))
    (let ((name (car names)))
      (cond
       ((fn-bpn-lifecycle-hidden-stage-namep name)
        (if (< (len hidden) *fn-bpn-lifecycle-max-hidden-stages*)
            (fn-bpnf-namespace-plan-aux
             (cdr names) legacy received (cons name hidden))
          (list :fault :hidden-stage-bound)))
       ((fn-bpnf-legacy-name-candidatep name)
        (if (< (len legacy) *fn-bpn-machine-max-records*)
            (fn-bpnf-namespace-plan-aux
             (cdr names) (cons name legacy) received hidden)
          (list :fault :legacy-record-bound)))
       ((fn-bpnf-kind-five-name-candidatep name)
        (if (< (len received) *fn-bpn-machine-max-records*)
            (fn-bpnf-namespace-plan-aux
             (cdr names) legacy (cons name received) hidden)
          (list :fault :received-record-bound)))
       (t (list :fault :fnbs-namespace))))))

(defun fn-bpnf-namespace-plan (names)
  (declare (xargs :guard t))
  (if (and (true-listp names)
           (<= (len names) (fn-bpnf-namespace-max-entries)))
      (fn-bpnf-namespace-plan-aux names nil nil nil)
    (list :fault :namespace-entry-bound)))

(defun fn-bpnf-namespace-planp (plan)
  (declare (xargs :guard t))
  (and (true-listp plan) (equal (len plan) 4)
       (equal (car plan) :ready)
       (true-listp (nth 1 plan))
       (true-listp (nth 2 plan))
       (true-listp (nth 3 plan))))

(defun fn-bpnf-namespace-legacy (plan)
  (declare (xargs :guard t)) (nth 1 plan))
(defun fn-bpnf-namespace-received (plan)
  (declare (xargs :guard t)) (nth 2 plan))
(defun fn-bpnf-namespace-hidden (plan)
  (declare (xargs :guard t)) (nth 3 plan))

; The host observes one directory only.  The new splitter does not weaken the
; legacy contiguous frontier: the old planner still judges exactly its final
; names and hidden stages, while kind-five replay judges received name/bytes.
; The result is a read-only recovery plan, not another lifecycle transition.
(defun fn-bpnf-mixed-recovery-plan (names)
  (declare (xargs :guard t))
  (let ((split (fn-bpnf-namespace-plan names)))
    (if (not (fn-bpnf-namespace-planp split))
        (list :fault :fnbs-namespace)
      (let ((legacy
             (fn-bpn-lifecycle-namespace-plan
              (append (fn-bpnf-namespace-legacy split)
                      (fn-bpnf-namespace-hidden split)))))
        (if (not (fn-bpn-lifecycle-namespace-planp legacy))
            (list :fault :legacy-namespace)
          (list :ready
                (fn-bpn-lifecycle-plan-record-names legacy)
                (fn-bpnf-namespace-received split)
                (fn-bpn-lifecycle-plan-hidden-stages legacy)
                (fn-bpn-lifecycle-plan-next-token legacy)))))))

(defun fn-bpnf-mixed-recovery-planp (plan)
  (declare (xargs :guard t))
  (and (true-listp plan) (equal (len plan) 5)
       (equal (car plan) :ready)
       (fn-string-listp (nth 1 plan))
       (fn-string-listp (nth 2 plan))
       (fn-string-listp (nth 3 plan))
       (natp (nth 4 plan))))

(defun fn-bpnf-mixed-legacy-names (plan)
  (declare (xargs :guard t)) (nth 1 plan))
(defun fn-bpnf-mixed-received-names (plan)
  (declare (xargs :guard t)) (nth 2 plan))
(defun fn-bpnf-mixed-hidden-stages (plan)
  (declare (xargs :guard t)) (nth 3 plan))
(defun fn-bpnf-mixed-legacy-observed (plan)
  (declare (xargs :guard t))
  (append (fn-bpnf-mixed-legacy-names plan)
          (fn-bpnf-mixed-hidden-stages plan)))
