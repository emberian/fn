; Pure kind-18 application against the one held list. Live completion and
; ordered replay will call this same rule after validating the protected row.
(in-package "ACL2")
(include-book "bp-fnbs-family-codec")
(set-verify-guards-eagerness 0)

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec adds onto an accumulator.
(defun fn-bpnf-arrival-count-loop (arrival held acc)
  (declare (xargs :measure (acl2-count held) :guard (acl2-numberp acc) :verify-guards nil))
  (if (consp held)
      (fn-bpnf-arrival-count-loop arrival
                                  (cdr held)
                                  (+ (if (equal (fn-bpn-nth 3 (car held)) arrival) 1 0)
                                     acc))
    (+ acc 0)))

(defun fn-bpnf-arrival-count (arrival held)
  (declare (xargs :verify-guards nil :guard t :measure (acl2-count held)))
  (mbe :logic
       (if (consp held)
           (+ (if (equal (fn-bpn-nth 3 (car held)) arrival) 1 0)
              (fn-bpnf-arrival-count arrival (cdr held)))
         0)
       :exec (fn-bpnf-arrival-count-loop arrival held 0)))

(local
 (defthm fn-bpnf-arrival-count-loop-is-plus
   (implies (acl2-numberp acc)
            (equal (fn-bpnf-arrival-count-loop arrival held acc)
                   (+ acc (fn-bpnf-arrival-count arrival held))))
   :hints (("Goal" :induct (fn-bpnf-arrival-count-loop arrival held acc)
                   :in-theory (disable fn-bpn-nth)))))

(verify-guards fn-bpnf-arrival-count-loop)

(verify-guards fn-bpnf-arrival-count
  :hints (("Goal"
           :in-theory
           (disable fn-bpnf-arrival-count-loop fn-bpn-nth)
           :use
           ((:instance fn-bpnf-arrival-count-loop-is-plus (acc 0))))))


(defun fn-bpnf-find-arrival (arrival held)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (consp held)
      (if (equal (fn-bpn-nth 3 (car held)) arrival)
          (car held)
        (fn-bpnf-find-arrival arrival (cdr held)))
    nil))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-bpnf-family-retain-other-rows-loop (held consumed acc)
  (declare (xargs :measure (acl2-count held) :guard (true-listp acc) :verify-guards nil))
  (if (consp held)
      (if (fn-ag-member (car held) consumed)
          (fn-bpnf-family-retain-other-rows-loop (cdr held) consumed acc)
        (fn-bpnf-family-retain-other-rows-loop (cdr held)
                                               consumed
                                               (cons (car held) acc)))
    (revappend acc nil)))

(defun fn-bpnf-family-retain-other-rows (held consumed)
  (declare (xargs :verify-guards nil :guard t :measure (acl2-count held)))
  (mbe :logic
       (if (consp held)
           (if (fn-ag-member (car held) consumed)
               (fn-bpnf-family-retain-other-rows (cdr held) consumed)
             (cons (car held)
                   (fn-bpnf-family-retain-other-rows (cdr held) consumed)))
         nil)
       :exec (fn-bpnf-family-retain-other-rows-loop held consumed nil)))

(local
 (defthm fn-bpnf-family-retain-other-rows-loop-is-revappend
   (equal (fn-bpnf-family-retain-other-rows-loop held consumed acc)
          (revappend acc (fn-bpnf-family-retain-other-rows held consumed)))
   :hints (("Goal" :induct (fn-bpnf-family-retain-other-rows-loop held consumed acc)
                   :in-theory (union-theories '(fn-bpnf-family-retain-other-rows-loop fn-bpnf-family-retain-other-rows revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-bpnf-family-retain-other-rows-loop)

(verify-guards fn-bpnf-family-retain-other-rows
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-bpnf-family-retain-other-rows)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-bpnf-family-retain-other-rows-loop-is-revappend (acc nil))))))


(defun fn-bpnf-family-apply (st record expected-arrival)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
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
      (let ((plan (fn-bpnf-family-plan st anchor)))
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

; New kind-18 decisions carry their proposal observation.  Replay calls the
; same eligibility rule over the exact durable kind-5 rows; it never reads a
; new clock.  Legacy unversioned records remain decodable but cannot install
; a family because their expiry decision was never persisted.
(defun fn-bpnf-family-apply-at (st record expected-arrival)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (if (not (fn-bpnf-family-record-atp record))
      (list :fault :legacy-family-expiry)
    (let* ((observation (fn-bpn-nth 7 record))
           (anchor (fn-bpnf-find-arrival
                    (fn-bpn-nth 3 record) (fn-bpnf-held-list st)))
           (plan (fn-bpnf-family-plan-at st anchor observation)))
      (if (not (equal (car plan) :ready))
          (list :fault :family-expiry)
        (fn-bpnf-family-apply st record expected-arrival)))))

(defthm fn-bpnf-family-apply-ready-has-held-whole
  (implies (equal (car (fn-bpnf-family-apply st record expected-arrival))
                  :ready)
           (and (fn-bpnf-heldp
                 (fn-bpn-nth 2
                  (fn-bpnf-family-apply st record expected-arrival)))
                (equal (fn-bpn-nth 3
                        (fn-bpn-nth 2
                         (fn-bpnf-family-apply st record expected-arrival)))
                       expected-arrival)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpnf-family-plan
                               fn-bpnf-active-set
                               fn-bpnf-family-retain-other-rows
                               fn-bpnf-find-held
                               fn-bpnf-family-recordp
                               fn-bpnf-heldp)))
  :rule-classes nil)
