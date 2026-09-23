; Outer D1b deletion transition over the one foundation/fragment owner.
; Only a durable kind-10 callback installs a tombstone and may issue a
; diagnostic report-due effect. Ordinary events delegate unchanged.
(in-package "ACL2")
(include-book "bp-node-fragment-step")
(include-book "bp-fnbs-deletion-codec")
(set-verify-guards-eagerness 0)

(defun fn-bpn-report-delete-issuedp (st)
  (declare (xargs :guard t))
  (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :delete))

(defun fn-bpn-report-delete-propose-step (st observation enabled)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (let ((held (and (fn-clock-observationp observation)
                   (fn-bpn-report-find-expired-held
                    (fn-bpnf-held-list st) observation))))
    (if (or (fn-bpnf-issued st) (fn-bpnf-waits st)
            (fn-bpn-machine-state-fenced (fn-bpnf-base st))
            (fn-bpn-machine-state-pending (fn-bpnf-base st))
            (not held)
            (not (fn-frame-natp (fn-bpnf-epoch st)))
            (not (fn-frame-natp (fn-bpnf-next-op st)))
            (>= (fn-bpnf-next-op st) *fn-frame-max-nat*))
        (fn-bpnf-answer st nil)
      (let* ((identity
              (fn-bpp-primary-identity
               (fn-bpb-bundle-primary (fn-bpnf-held-bundle held))))
             (draft
              (fn-bpn-report-delete-record
               (fn-bpnf-epoch st) (fn-bpnf-next-op st)
               (fn-bpn-nth 3 held)
               identity
               :lifetime-expired))
             (due
              (fn-bpn-report-deleted-payload
               draft (fn-bpn-report-tombstone-held held draft)
               observation enabled))
             (record
              (fn-bpn-report-delete-with-intent
               (fn-bpnf-epoch st) (fn-bpnf-next-op st)
               (fn-bpn-nth 3 held) identity :lifetime-expired
               (if due (fn-bpn-nth 2 due) '(0))))
             (frame (fn-bpnf-delete-frame record)))
        (if (or (not (fn-bpn-report-delete-recordp record))
                (equal frame :bad))
            (fn-bpnf-answer st (list (list :delete-answer :refused)))
          (fn-bpnf-answer
           (fn-bpnf-state-with-arrival
            (fn-bpnf-base st) (fn-bpnf-held-list st)
            (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
            (fn-bpnf-correlation st)
             (fn-bpnf-operation
             (fn-bpnf-epoch st) (fn-bpnf-next-op st) :delete
             (list record observation (if enabled t nil)
                   (fn-bpp-report-to
                    (fn-bpb-bundle-primary
                     (fn-bpnf-held-bundle held)))) :pending)
            (fn-bpnf-waits st) (fn-bpnf-epoch st)
            (1+ (fn-bpnf-next-op st)) (fn-bpnf-next-arrival st))
           (list (list :persist-delete
                       (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                       record))))))))

(defun fn-bpn-report-delete-persist-step (st epoch op result)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (let* ((issued (fn-bpnf-issued st))
         (detail (fn-bpn-nth 4 issued))
         (record (fn-bpn-nth 0 detail)))
    (if (not (and (fn-bpn-report-delete-issuedp st)
                  (equal (fn-bpn-nth 5 issued) :pending)
                  (fn-bpnf-operation-matchp issued epoch op)))
        (fn-bpnf-answer st nil)
      (cond
       ((equal result :durable)
        (mv-let (ok updated)
          (fn-bpn-report-apply-delete record (fn-bpnf-held-list st))
          (if (not ok)
              (fn-bpnf-answer
               (fn-bpnf-with-issued
                st (fn-bpnf-operation epoch op :delete detail :uncertain))
               (list (list :delete-answer :uncertain)))
            (let* ((settled
                    (fn-bpnf-state-with-arrival
                     (fn-bpnf-base st) updated (fn-bpnf-outcomes st)
                     (fn-bpnf-handoffs st) (fn-bpnf-correlation st)
                     nil (fn-bpnf-waits st) (fn-bpnf-epoch st)
                     (fn-bpnf-next-op st) (fn-bpnf-next-arrival st)))
                   (payload (fn-bpn-nth 6 record)))
              (fn-bpnf-answer
               settled
               (if (not (equal payload '(0)))
                   (list (list :delete-ready
                               (fn-bpn-nth 3 record))
                         (list :report-due
                               (fn-bpn-nth 3 detail)
                               payload))
                 (list (list :delete-ready
                             (fn-bpn-nth 3 record)))))))))
       ((equal result :refused)
        (fn-bpnf-answer (fn-bpnf-with-issued st nil)
                        (list (list :delete-answer :refused))))
       (t
        (fn-bpnf-answer
         (fn-bpnf-with-issued
          st (fn-bpnf-operation epoch op :delete detail :uncertain))
         (list (list :delete-answer :uncertain))))))))

(defun fn-bpn-report-step (st event)
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
    (fn-bpnf-fragment-step st event))
   ((and (fn-bpn-report-delete-issuedp st)
         (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain))
    (fn-bpnf-answer st nil))
   ((and (fn-bpn-report-delete-issuedp st)
         (equal (fn-cbor-ag-car event) :persist-result))
    (fn-bpn-report-delete-persist-step
     st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
     (fn-bpn-nth 3 event)))
   ((equal (fn-cbor-ag-car event) :expire-held)
    (fn-bpn-report-delete-propose-step
     st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)))
   (t (fn-bpnf-fragment-step st event))))

(defthm fn-bpn-report-step-delegates-ordinary-events
  (implies (and (not (fn-bpn-report-delete-issuedp st))
                (not (equal (fn-cbor-ag-car event) :expire-held)))
           (equal (fn-bpn-report-step st event)
                  (fn-bpnf-fragment-step st event)))
  :hints (("Goal" :in-theory (disable fn-bpnf-fragment-step)))
  :rule-classes nil)

(defthm fn-bpn-report-delete-proposal-retains-held
  (equal (fn-bpnf-held-list
          (fn-bpnf-answer-state
           (fn-bpn-report-delete-propose-step st obs enabled)))
         (fn-bpnf-held-list st))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-report-find-expired-held
                               fn-bpn-report-deleted-payload
                               fn-bpn-report-tombstone-held
                               fn-bpnf-delete-frame
                               fn-bpn-report-delete-recordp)))
  :rule-classes nil)
