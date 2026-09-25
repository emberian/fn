; The native service's one foundation-step extension for durable kind-18
; replacement. All ordinary events delegate to fn-bpnf-step on the same state.
(in-package "ACL2")
(include-book "bp-fnbs-family-replay")
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
    (fn-bpnf-family-propose-step
     st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)))
   (t (fn-bpnf-step st event))))

(defun fn-bpnf-family-next-aux (st held observation)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :measure (acl2-count held)
                  :verify-guards nil))
  (if (consp held)
      (let ((h (car held)))
        (if (and (fn-bpnf-active-fragmentp h)
                 (equal (fn-bpnf-arrival-count
                         (fn-bpn-nth 3 h) (fn-bpnf-held-list st)) 1)
                 (equal (fn-cbor-ag-car
                         (fn-bpnf-family-plan-at st h observation)) :ready))
            (list :ready (fn-bpn-nth 3 h))
          (fn-bpnf-family-next-aux st (cdr held) observation)))
    nil))

;; The selector above plans a family once per member: a family of n
;; fragments costs n reassemblies of the whole family each time the host asks
;; (bp-service `fnn-bps-fragment-progress`), quadratic in the family.  The executed
;; selector below plans each family at most once per call: a row whose family
;; some earlier row already planned (not ready) is skipped, because every
;; member of one family has the same plan (fn-bpnf-family-plan-at-of-member).
;; fn-bpnf-family-next-memo-is-aux equates the two, so the answer, the anchor
;; included, is the same.

(defun fn-bpnf-family-tried-p (h tried)
  (declare (xargs :guard t :measure (acl2-count tried)))
  (if (consp tried)
      (or (fn-bpnf-same-fragment-family-p h (car tried))
          (fn-bpnf-family-tried-p h (cdr tried)))
    nil))

(defun fn-bpnf-family-next-memo (st held observation tried)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :measure (acl2-count held)
                  :verify-guards nil))
  (if (consp held)
      (let ((h (car held)))
        (if (and (fn-bpnf-active-fragmentp h)
                 (equal (fn-bpnf-arrival-count
                         (fn-bpn-nth 3 h) (fn-bpnf-held-list st)) 1))
            (if (fn-bpnf-family-tried-p h tried)
                (fn-bpnf-family-next-memo st (cdr held) observation tried)
              (if (equal (fn-cbor-ag-car
                          (fn-bpnf-family-plan-at st h observation)) :ready)
                  (list :ready (fn-bpn-nth 3 h))
                (fn-bpnf-family-next-memo st (cdr held) observation
                                          (cons h tried))))
          (fn-bpnf-family-next-memo st (cdr held) observation tried)))
    nil))

;; Every member of one family selects the same rows, so it has the same plan.
(defthm fn-bpnf-same-family-selects-same-rows
  (implies (and (fn-bpnf-same-fragment-family-p a b))
           (equal (fn-bpnf-active-set-rows held a)
                  (fn-bpnf-active-set-rows held b)))
  :hints (("Goal" :induct (fn-bpnf-active-set-rows held a))))

(defthm fn-bpnf-same-family-same-total
  (implies (fn-bpnf-same-fragment-family-p a b)
           (equal (fn-bpp-total-adu-length
                   (fn-bpb-bundle-primary (fn-bpnf-held-bundle a)))
                  (fn-bpp-total-adu-length
                   (fn-bpb-bundle-primary (fn-bpnf-held-bundle b)))))
  :hints (("Goal" :in-theory (enable fn-bpnf-fragment-coherence-key))))

(defthm fn-bpnf-family-plan-at-of-member
  (implies (and (fn-bpnf-same-fragment-family-p a b)
                (member-equal a (fn-bpnf-held-list st))
                (member-equal b (fn-bpnf-held-list st)))
           (equal (fn-bpnf-family-plan-at st a observation)
                  (fn-bpnf-family-plan-at st b observation)))
  :hints (("Goal" :in-theory (e/d (fn-bpnf-family-plan-at fn-bpnf-family-plan
                                   fn-bpnf-fragment-query fn-bpnf-active-set
                                   fn-bpnf-family-member)
                                  (fn-bpnf-fragment-query-is-reference
                                   fn-bpnf-active-set-rows
                                   fn-bpnf-same-fragment-family-p
                                   fn-bpfw-reassemble fn-bpnf-offset-zero-source
                                   fn-bpnf-family-whole-bundle
                                   fn-bpnf-family-rows-livep
                                   fn-bpnf-family-consumed-ids
                                   fn-bpnf-held-octets fn-bpb-encode
                                   fn-bpb-bundlep fn-bpnf-fragment-cells))
           :use ((:instance fn-bpnf-same-family-selects-same-rows
                            (held (fn-bpnf-held-list st)))
                 (:instance fn-bpnf-same-family-same-total)))))

;; The memo's invariant: every tried row is a held active fragment whose plan
;; is not ready.
(defun fn-bpnf-family-tried-okp (st tried observation)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count tried)))
  (if (consp tried)
      (and (fn-bpnf-active-fragmentp (car tried))
           (member-equal (car tried) (fn-bpnf-held-list st))
           (not (equal (fn-cbor-ag-car
                        (fn-bpnf-family-plan-at st (car tried) observation))
                       :ready))
           (fn-bpnf-family-tried-okp st (cdr tried) observation))
    t))

(defthm fn-bpnf-family-tried-member-not-ready
  (implies (and (fn-bpnf-family-tried-okp st tried observation)
                (fn-bpnf-family-tried-p h tried)
                (member-equal h (fn-bpnf-held-list st)))
           (not (equal (fn-cbor-ag-car
                        (fn-bpnf-family-plan-at st h observation))
                       :ready)))
  :hints (("Goal" :induct (fn-bpnf-family-tried-p h tried)
           :in-theory (disable fn-bpnf-family-plan-at
                               fn-bpnf-same-fragment-family-p))
          ("Subgoal *1/2" :use ((:instance fn-bpnf-family-plan-at-of-member
                                           (a h) (b (car tried)))))))

(defthm fn-bpnf-family-next-memo-is-aux
  (implies (and (subsetp-equal held (fn-bpnf-held-list st))
                (fn-bpnf-family-tried-okp st tried observation))
           (equal (fn-bpnf-family-next-memo st held observation tried)
                  (fn-bpnf-family-next-aux st held observation)))
  :hints (("Goal" :induct (fn-bpnf-family-next-memo st held observation tried)
           :in-theory (disable fn-bpnf-family-plan-at
                               fn-bpnf-active-fragmentp
                               fn-bpnf-arrival-count
                               fn-bpnf-family-tried-p))))

(defthm fn-bpnf-subsetp-equal-reflexive
  (subsetp-equal x x))

(defun fn-bpnf-family-next (st observation)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (if (or (fn-bpnf-issued st) (fn-bpnf-waits st)
          (not (fn-frame-natp (fn-bpnf-next-arrival st))))
      nil
    (mbe :logic (fn-bpnf-family-next-aux st (fn-bpnf-held-list st) observation)
         :exec (fn-bpnf-family-next-memo st (fn-bpnf-held-list st) observation
                                         nil))))

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
                  (observation (fn-bpn-nth 2 event))))
           :in-theory (disable fn-bpnf-family-plan-at
                               fn-bpnf-family-apply-at
                               fn-bpnf-family-v1-frame
                               fn-bpnf-family-record-atp
                               fn-bpnf-active-set)))
  :rule-classes nil)
