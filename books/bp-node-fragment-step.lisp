; The native service's one foundation-step extension for durable kind-18
; replacement. All ordinary events delegate to fn-bpnf-step on the same state.
(in-package "ACL2")
(include-book "bp-fnbs-family-replay")
(set-verify-guards-eagerness 0)

(defun fn-bpnf-family-issuedp (st)
  (declare (xargs :guard t))
  (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :family))

(defun fn-bpnf-family-propose-step (st anchor-arrival)
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
           (plan (fn-bpnf-family-plan st anchor))
           (record (fn-bpnf-family-record
                    (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                    anchor-arrival (fn-bpnf-next-arrival st)
                    (fn-bpn-nth 2 plan))))
      (if (not (and (equal (car plan) :ready)
                    (fn-bpnf-family-recordp record)
                    (not (equal (fn-bpnf-family-frame record) :bad))
                    (equal (car (fn-bpnf-family-apply
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
                    (fn-bpnf-family-apply st record arrival)
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

(defun fn-bpnf-fragment-step (st event)
  (declare (xargs :guard
                  (and (fn-bpn-machine-statep (fn-bpnf-base st))
                       (or (not (equal (fn-cbor-ag-car event) :base))
                           (fn-bpn-machine-eventp (fn-bpn-nth 1 event)))
                       (or (not (equal (fn-cbor-ag-car event) :recover-fnbs))
                           (and (true-listp (fn-bpn-nth 2 event))
                                (<= (len (fn-bpn-nth 2 event))
                                    *fn-bpn-machine-max-records*))))
                  :verify-guards nil))
  (cond
   ((equal (fn-cbor-ag-car event) :recover-fnbs)
    (fn-bpnf-step st event))
   ((and (fn-bpnf-family-issuedp st)
         (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain))
    (fn-bpnf-answer st nil))
   ((and (fn-bpnf-family-issuedp st)
         (equal (fn-cbor-ag-car event) :persist-result))
    (fn-bpnf-family-persist-step
     st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event) (fn-bpn-nth 3 event)))
   ((equal (fn-cbor-ag-car event) :family)
    (fn-bpnf-family-propose-step st (fn-bpn-nth 1 event)))
   (t (fn-bpnf-step st event))))

(defun fn-bpnf-family-next-aux (st held)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :measure (acl2-count held)
                  :verify-guards nil))
  (if (consp held)
      (let ((h (car held)))
        (if (and (fn-bpnf-active-fragmentp h)
                 (equal (fn-bpnf-arrival-count
                         (fn-bpn-nth 3 h) (fn-bpnf-held-list st)) 1)
                 (equal (fn-cbor-ag-car (fn-bpnf-family-plan st h)) :ready))
            (list :ready (fn-bpn-nth 3 h))
          (fn-bpnf-family-next-aux st (cdr held))))
    nil))

(defun fn-bpnf-family-next (st)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (if (or (fn-bpnf-issued st) (fn-bpnf-waits st)
          (not (fn-frame-natp (fn-bpnf-next-arrival st))))
      nil
    (fn-bpnf-family-next-aux st (fn-bpnf-held-list st))))

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
           (fn-bpnf-family-propose-step st anchor-arrival)))
         (fn-bpnf-held-list st))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpnf-family-plan
                               fn-bpnf-family-apply
                               fn-bpnf-family-frame
                               fn-bpnf-family-recordp)))
  :rule-classes nil)
