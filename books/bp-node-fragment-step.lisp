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
              ;; A family without its offset-zero fragment is never ready
              ;; (fn-bpnf-family-without-offset-zero-is-not-ready), so its
              ;; plan -- a reassembly canvas as long as the whole ADU -- is
              ;; not built: an arrival before offset zero costs the rows, not
              ;; the ADU (PRF-134; PKT-294 for the general coverage check).
              (if (and (fn-bpnf-offset-zero-source (fn-bpnf-active-set st h))
                       (equal (fn-cbor-ag-car
                               (fn-bpnf-family-plan-at st h observation)) :ready))
                  (list :ready (fn-bpn-nth 3 h))
                (fn-bpnf-family-next-memo st (cdr held) observation
                                          (cons h tried))))
          (fn-bpnf-family-next-memo st (cdr held) observation tried)))
    nil))

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
           :in-theory (union-theories
                       '(fn-bpnf-family-tried-p fn-bpnf-family-tried-okp)
                       (theory 'minimal-theory)))
          ("Subgoal *1/1" :use ((:instance fn-bpnf-family-plan-at-of-member
                                           (a h) (b (car tried)))))
          ("Subgoal *1/2" :use ((:instance fn-bpnf-family-plan-at-of-member
                                           (a h) (b (car tried)))))
          ("Subgoal *1/3" :use ((:instance fn-bpnf-family-plan-at-of-member
                                           (a h) (b (car tried)))))))

(local
 (defthm fn-bpnf-family-tried-okp-of-cons
   (implies (and (fn-bpnf-family-tried-okp st tried observation)
                 (fn-bpnf-active-fragmentp h)
                 (member-equal h (fn-bpnf-held-list st))
                 (not (equal (fn-cbor-ag-car
                              (fn-bpnf-family-plan-at st h observation))
                             :ready)))
            (fn-bpnf-family-tried-okp st (cons h tried) observation))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-bpnf-family-tried-okp st (cons h tried) observation))
            :in-theory (union-theories '(car-cons cdr-cons)
                                       (theory 'minimal-theory))))))

(defthm fn-bpnf-family-next-memo-is-aux
  (implies (and (subsetp-equal held (fn-bpnf-held-list st))
                (fn-bpnf-family-tried-okp st tried observation))
           (equal (fn-bpnf-family-next-memo st held observation tried)
                  (fn-bpnf-family-next-aux st held observation)))
  :hints (("Goal" :induct (fn-bpnf-family-next-memo st held observation tried)
           :in-theory (union-theories
                       '(fn-bpnf-family-next-memo fn-bpnf-family-next-aux
                         fn-bpnf-family-tried-member-not-ready
                         fn-bpnf-family-without-offset-zero-is-not-ready
                         fn-bpnf-family-tried-okp-of-cons
                         subsetp-equal car-cons cdr-cons)
                       (theory 'minimal-theory)))))

(in-theory (disable fn-bpnf-family-tried-member-not-ready
                    fn-bpnf-family-without-offset-zero-is-not-ready
                    fn-bpnf-family-next-memo-is-aux))

(local
 (defthm fn-bpnf-subsetp-equal-cons
   (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))))

(defthm fn-bpnf-subsetp-equal-reflexive
  (subsetp-equal x x))

;; PRF-136: the served selector's work is bounded by the rows' headers.
;; fn-bpnf-family-next-memo (above) still re-encoded every held row's wire on
;; each call: fn-bpnf-active-fragmentp checks fn-bpnf-heldp, whose last test
;; re-encodes the bundle, and the memo asked it of every row and twice more per
;; row through fn-bpnf-same-fragment-family-p (the arrival profile of
;; bp-lifecycle-5).  The selector below reads each row's primary block only:
;; it plans (and so re-encodes) a row only when that row's family holds an
;; offset-zero fragment, because a family without one is never ready
;; (fn-bpnf-family-without-offset-zero-is-not-ready).  Which families hold one
;; is one pass over the headers (fn-bpnf-zero-family-keys); a family planned
;; and not ready is remembered by its key for the rest of the call.

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

(defun fn-bpnf-zero-family-keys (held)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp held)
      (let ((h (car held)))
        (if (and (fn-bpnf-fragment-candidatep h)
                 (equal (fn-bpp-fragment-offset
                         (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
                        0))
            (cons (fn-bpnf-fragment-family-key h)
                  (fn-bpnf-zero-family-keys (cdr held)))
          (fn-bpnf-zero-family-keys (cdr held))))
    nil))

(defun fn-bpnf-family-select (st held observation tried zero)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (true-listp tried) (true-listp zero))
                  :measure (acl2-count held)
                  :verify-guards nil))
  (if (consp held)
      (let ((h (car held)))
        (if (not (fn-bpnf-fragment-candidatep h))
            (fn-bpnf-family-select st (cdr held) observation tried zero)
          (let ((key (fn-bpnf-fragment-family-key h)))
            (if (or (not (member-equal key zero))
                    (member-equal key tried))
                (fn-bpnf-family-select st (cdr held) observation tried zero)
              (if (and (fn-bpnf-active-fragmentp h)
                       (equal (fn-bpnf-arrival-count
                               (fn-bpn-nth 3 h) (fn-bpnf-held-list st)) 1))
                  (if (equal (fn-cbor-ag-car
                              (fn-bpnf-family-plan-at st h observation))
                             :ready)
                      (list :ready (fn-bpn-nth 3 h))
                    (fn-bpnf-family-select st (cdr held) observation
                                           (cons key tried) zero))
                (fn-bpnf-family-select st (cdr held) observation
                                       tried zero))))))
    nil))

;; The select's invariant: every active row whose family key is in TRIED has
;; a plan that is not ready.
(defun fn-bpnf-family-keys-not-readyp (st rows tried observation)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count rows)))
  (if (consp rows)
      (and (or (not (fn-bpnf-active-fragmentp (car rows)))
               (not (member-equal (fn-bpnf-fragment-family-key (car rows))
                                  tried))
               (not (equal (fn-cbor-ag-car
                            (fn-bpnf-family-plan-at st (car rows) observation))
                           :ready)))
           (fn-bpnf-family-keys-not-readyp st (cdr rows) tried observation))
    t))

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

(local
 (defthm fn-bpnf-family-keys-not-readyp-member
   (implies (and (fn-bpnf-family-keys-not-readyp st rows tried observation)
                 (member-equal h rows)
                 (fn-bpnf-active-fragmentp h)
                 (member-equal (fn-bpnf-fragment-family-key h) tried))
            (not (equal (fn-cbor-ag-car
                         (fn-bpnf-family-plan-at st h observation))
                        :ready)))
   :hints (("Goal" :induct (fn-bpnf-family-keys-not-readyp
                            st rows tried observation)
            :in-theory (union-theories
                        '(fn-bpnf-family-keys-not-readyp member-equal)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnf-family-keys-not-readyp-cons
   (implies (and (fn-bpnf-family-keys-not-readyp st rows tried observation)
                 (subsetp-equal rows (fn-bpnf-held-list st))
                 (fn-bpnf-active-fragmentp h)
                 (member-equal h (fn-bpnf-held-list st))
                 (not (equal (fn-cbor-ag-car
                              (fn-bpnf-family-plan-at st h observation))
                             :ready)))
            (fn-bpnf-family-keys-not-readyp
             st rows (cons (fn-bpnf-fragment-family-key h) tried) observation))
   :hints (("Goal" :induct (fn-bpnf-family-keys-not-readyp
                            st rows tried observation)
            :in-theory (union-theories
                        '(fn-bpnf-family-keys-not-readyp member-equal
                          subsetp-equal car-cons cdr-cons)
                        (theory 'minimal-theory)))
           ("Subgoal *1/1" :use ((:instance fn-bpnf-family-plan-at-of-member
                                            (a (car rows)) (b h))
                                 (:instance fn-bpnf-same-family-is-key-equality
                                            (a (car rows)) (b h)))))))

(defthm fn-bpnf-family-keys-not-readyp-of-nil
  (fn-bpnf-family-keys-not-readyp st rows nil observation)
  :hints (("Goal" :induct (fn-bpnf-family-keys-not-readyp
                           st rows nil observation)
           :in-theory (union-theories
                       '(fn-bpnf-family-keys-not-readyp member-equal
                         (:executable-counterpart member-equal))
                       (theory 'minimal-theory)))))

;; PRF-136 keystone: the header-bounded selector answers what the reference
;; selector answers, the anchor included.
(defthm fn-bpnf-family-select-is-aux
  (implies (and (subsetp-equal held (fn-bpnf-held-list st))
                (fn-bpnf-family-keys-not-readyp
                 st (fn-bpnf-held-list st) tried observation)
                (equal zero (fn-bpnf-zero-family-keys (fn-bpnf-held-list st))))
           (equal (fn-bpnf-family-select st held observation tried zero)
                  (fn-bpnf-family-next-aux st held observation)))
  :hints (("Goal" :induct (fn-bpnf-family-select st held observation tried zero)
           :in-theory (union-theories
                       '(fn-bpnf-family-select fn-bpnf-family-next-aux
                         fn-bpnf-active-fragment-is-candidate
                         fn-bpnf-family-without-zero-key-is-not-ready
                         fn-bpnf-family-keys-not-readyp-member
                         fn-bpnf-family-keys-not-readyp-cons
                         fn-bpnf-subsetp-equal-reflexive
                         subsetp-equal car-cons cdr-cons)
                       (theory 'minimal-theory)))))

;; The work of one call, counted: STEPS counts a row visit and the key
;; comparisons its membership tests may make (1 + |zero| + |tried| for a
;; candidate row, 1 otherwise); PLANS counts the rows the select re-encodes
;; and plans (fn-bpnf-active-fragmentp, fn-bpnf-arrival-count and
;; fn-bpnf-family-plan-at, whose work is the family's octets, PRF-121).
(defun fn-bpnf-family-select-plans (st held observation tried zero)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count held)))
  (if (consp held)
      (let ((h (car held)))
        (if (not (fn-bpnf-fragment-candidatep h))
            (fn-bpnf-family-select-plans st (cdr held) observation tried zero)
          (let ((key (fn-bpnf-fragment-family-key h)))
            (if (or (not (member-equal key zero))
                    (member-equal key tried))
                (fn-bpnf-family-select-plans st (cdr held) observation
                                             tried zero)
              (if (and (fn-bpnf-active-fragmentp h)
                       (equal (fn-bpnf-arrival-count
                               (fn-bpn-nth 3 h) (fn-bpnf-held-list st)) 1))
                  (if (equal (fn-cbor-ag-car
                              (fn-bpnf-family-plan-at st h observation))
                             :ready)
                      1
                    (1+ (fn-bpnf-family-select-plans
                         st (cdr held) observation (cons key tried) zero)))
                (1+ (fn-bpnf-family-select-plans st (cdr held) observation
                                                 tried zero)))))))
    0))

(defun fn-bpnf-family-select-steps (st held observation tried zero)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count held)))
  (if (consp held)
      (let ((h (car held)))
        (if (not (fn-bpnf-fragment-candidatep h))
            (1+ (fn-bpnf-family-select-steps st (cdr held) observation
                                             tried zero))
          (let ((key (fn-bpnf-fragment-family-key h))
                (here (+ 1 (len zero) (len tried))))
            (if (or (not (member-equal key zero))
                    (member-equal key tried))
                (+ here (fn-bpnf-family-select-steps st (cdr held) observation
                                                     tried zero))
              (if (and (fn-bpnf-active-fragmentp h)
                       (equal (fn-bpnf-arrival-count
                               (fn-bpn-nth 3 h) (fn-bpnf-held-list st)) 1))
                  (if (equal (fn-cbor-ag-car
                              (fn-bpnf-family-plan-at st h observation))
                             :ready)
                      here
                    (+ here (fn-bpnf-family-select-steps
                             st (cdr held) observation (cons key tried) zero)))
                (+ here (fn-bpnf-family-select-steps st (cdr held) observation
                                                     tried zero)))))))
    0))

;; The rows whose family key is among ZERO.
(defun fn-bpnf-rows-in-zero-families (held zero)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp held)
      (+ (if (and (fn-bpnf-fragment-candidatep (car held))
                  (member-equal (fn-bpnf-fragment-family-key (car held)) zero))
             1 0)
         (fn-bpnf-rows-in-zero-families (cdr held) zero))
    0))

;; PRF-136 keystone: the rows re-encoded and planned are at most the rows
;; whose family holds its offset-zero fragment; every other row costs its
;; header.
(defthm fn-bpnf-family-select-plans-bound
  (<= (fn-bpnf-family-select-plans st held observation tried zero)
      (fn-bpnf-rows-in-zero-families held zero))
  :hints (("Goal" :induct (fn-bpnf-family-select-plans
                           st held observation tried zero)
           :in-theory (disable fn-bpnf-fragment-candidatep
                               fn-bpnf-fragment-family-key
                               fn-bpnf-active-fragmentp
                               fn-bpnf-arrival-count
                               fn-bpnf-family-plan-at)))
  :rule-classes :linear)

;; PRF-136 keystone: a call that plans no row does header work only, at most
;; one visit and |zero| + |tried| + 1 key comparisons per row.
(defthm fn-bpnf-family-select-steps-bound
  (implies (equal (fn-bpnf-family-select-plans st held observation tried zero)
                  0)
           (<= (fn-bpnf-family-select-steps st held observation tried zero)
               (* (len held) (+ 1 (len zero) (len tried)))))
  :hints (("Goal" :induct (fn-bpnf-family-select-steps
                           st held observation tried zero)
           :in-theory (disable fn-bpnf-fragment-candidatep
                               fn-bpnf-fragment-family-key
                               fn-bpnf-active-fragmentp
                               fn-bpnf-arrival-count
                               fn-bpnf-family-plan-at)))
  :rule-classes :linear)

(defthm fn-bpnf-zero-family-keys-bound
  (<= (len (fn-bpnf-zero-family-keys held)) (len held))
  :hints (("Goal" :in-theory (disable fn-bpnf-fragment-candidatep
                                      fn-bpnf-fragment-family-key)))
  :rule-classes :linear)

(in-theory (disable fn-bpnf-family-without-zero-key-is-not-ready
                    fn-bpnf-family-select-is-aux))

(defun fn-bpnf-family-next (st observation)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (if (or (fn-bpnf-issued st) (fn-bpnf-waits st)
          (not (fn-frame-natp (fn-bpnf-next-arrival st))))
      nil
    (mbe :logic (fn-bpnf-family-next-aux st (fn-bpnf-held-list st) observation)
         :exec (fn-bpnf-family-select
                st (fn-bpnf-held-list st) observation nil
                (fn-bpnf-zero-family-keys (fn-bpnf-held-list st))))))

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
