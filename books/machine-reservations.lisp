; Local partition conservation, carried by callers rather than rescanned.
(in-package "ACL2")
(include-book "arm-children")

(defun fn2-machines-reservation-view (ord fn2-machines)
  (declare (xargs :stobjs fn2-machines :verify-guards nil))
  (list (fn2-machines-active-counti ord fn2-machines)
        (fn2-machines-admission-creditsi ord fn2-machines)
        (fn2-machines-connection-counti ord fn2-machines)))
(defun fn2-machines-reservation-valuesp (values)
  (let ((active (car values)) (credits (cadr values)) (capacity (caddr values)))
    (and (natp active) (natp credits) (natp capacity)
         (<= (+ active credits) capacity))))
(defun fn2-machines-partition-reservedp (ord fn2-machines)
  (declare (xargs :stobjs fn2-machines :verify-guards nil))
  (and (natp ord) (< ord *fn2-machine-admitted-max*)
       (fn2-machines-reservation-valuesp (fn2-machines-reservation-view ord fn2-machines))))
(defthm fn2-machines-partition-reserved-forward
  (implies (fn2-machines-partition-reservedp ord machines)
    (and (natp ord) (< ord *fn2-machine-admitted-max*)
         (natp (fn2-machines-active-counti ord machines))
         (natp (fn2-machines-admission-creditsi ord machines))
         (natp (fn2-machines-connection-counti ord machines))
         (<= (+ (fn2-machines-active-counti ord machines)
                (fn2-machines-admission-creditsi ord machines))
             (fn2-machines-connection-counti ord machines))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory
           (enable fn2-machines-partition-reservedp fn2-machines-reservation-valuesp
                   fn2-machines-reservation-view))))

; Pure list effects. Constants identify schema positions only; neither
; expected function invokes checked writers, installers or reclamation.
(defun fn2-machines-reservation-put (field ord value machines)
  (update-nth field (update-nth ord value (nth field machines)) machines))
(defun fn2-machines-reclaim-list-expected (id ord retire machines control)
  (let* ((active (nth ord (nth *fn2-machines-active-count* machines)))
         (credits (nth ord (nth *fn2-machines-admission-credits* machines)))
         (machines (if retire machines
                     (fn2-machines-reservation-put *fn2-machines-free-head* ord id machines)))
         (machines (if retire machines
                     (fn2-machines-reservation-put *fn2-machines-admission-credits*
                                                  ord (+ 1 credits) machines)))
         (machines (fn2-machines-reservation-put *fn2-machines-active-count*
                                                ord (- active 1) machines)))
    (list machines control)))
(defun fn2-machines-install-list-expected (ord target next creditp machines control)
  (let* ((active (nth ord (nth *fn2-machines-active-count* machines)))
         (credits (nth ord (nth *fn2-machines-admission-credits* machines)))
         (machines (fn2-machines-reservation-put *fn2-machines-free-head* ord next machines))
         (machines (fn2-machines-reservation-put *fn2-machines-active-count*
                                                ord (+ 1 active) machines))
         (machines (if creditp
                       (fn2-machines-reservation-put *fn2-machines-admission-credits*
                                                    ord (- credits 1) machines)
                     machines)))
    (list (update-nth *fn2-machines-wake-id* target machines) control)))

(defthm fn2-machines-wait-reason-reservation-frame
  (equal
   (fn2-machines-partition-reservedp ord (fn2-machines-set-wait-reason id reason machines))
   (fn2-machines-partition-reservedp ord machines))
  :hints (("Goal" :in-theory
           (enable fn2-machines-partition-reservedp fn2-machines-reservation-valuesp
             fn2-machines-reservation-view fn2-machines-active-counti
             fn2-machines-admission-creditsi fn2-machines-connection-counti))))
(defthm fn2-machines-park-taken-reservation-frame
  (equal
   (fn2-machines-partition-reservedp query
     (car (fn2-machines-park-taken waiter ord reason machines control)))
   (fn2-machines-partition-reservedp query machines))
  :hints (("Goal" :in-theory
           (e/d (fn2-machines-park-taken fn2-machines-park-admission fn2-machines-stop-write
                 fn2-machines-partition-reservedp fn2-machines-reservation-valuesp
                 fn2-machines-reservation-view fn2-machines-active-counti
                 fn2-machines-admission-creditsi fn2-machines-connection-counti)
                (fn2-control-record-stop)))))

(defthm fn2-machines-reserved-reclaim-independent
  (implies (and (fn2-machinesp machines) (fn2-machines-wfp machines)
                (fn2-machines-partition-reservedp ord machines)
                (< 0 (fn2-machines-active-counti ord machines))
                (unsigned-byte-p 32 id))
    (equal (fn2-machines-reclaim id ord retire machines control)
           (fn2-machines-reclaim-list-expected id ord retire machines control)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn2-machines-reclaim fn2-machines-partition-reservedp
                 fn2-machines-reservation-valuesp fn2-machines-reservation-view
                 fn2-machines-reclaim-list-expected fn2-machines-reservation-put
                 fn2-machines-active-counti fn2-machines-admission-creditsi
                 fn2-machines-connection-counti update-fn2-machines-free-headi
                 update-fn2-machines-active-counti update-fn2-machines-admission-creditsi)
                (fn2-machinesp fn2-machines-wfp fn2-machines-stop-write)))))

; A take debits the credit in the same returned transition as its active
; increment. The non-credit installation used by listeners instead needs
; reserved slack; it is deliberately not asserted by this theorem.
(defthm fn2-machines-reserved-take-install-independent
  (implies (and (fn2-machinesp machines) (fn2-machines-wfp machines)
                (fn2-machines-partition-reservedp ord machines)
                (< 0 (fn2-machines-admission-creditsi ord machines))
                (unsigned-byte-p 32 target) (unsigned-byte-p 32 next))
    (equal (fn2-machines-partition-install ord target next t machines control)
           (fn2-machines-install-list-expected ord target next t machines control)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn2-machines-partition-install fn2-machines-partition-reservedp
                 fn2-machines-reservation-valuesp fn2-machines-reservation-view
                 fn2-machines-install-list-expected fn2-machines-reservation-put
                 fn2-machines-active-counti fn2-machines-admission-creditsi
                 fn2-machines-connection-counti update-fn2-machines-free-headi
                 update-fn2-machines-active-counti update-fn2-machines-admission-creditsi
                 update-fn2-machines-wake-id)
                (fn2-machinesp fn2-machines-wfp fn2-machines-stop-write)))))

(defthm fn2-machines-reserved-reclaim-preserved
  (implies (and (fn2-machinesp machines) (fn2-machines-wfp machines)
                (fn2-machines-partition-reservedp ord machines)
                (< 0 (fn2-machines-active-counti ord machines))
                (unsigned-byte-p 32 id))
    (fn2-machines-partition-reservedp ord
      (car (fn2-machines-reclaim id ord retire machines control))))
  :rule-classes :rewrite
  :hints (("Goal" :use fn2-machines-reserved-reclaim-independent
           :in-theory
           (e/d (fn2-machines-partition-reservedp fn2-machines-reclaim-list-expected
                 fn2-machines-reservation-valuesp fn2-machines-reservation-view
                 fn2-machines-reservation-put fn2-machines-active-counti
                 fn2-machines-admission-creditsi fn2-machines-connection-counti)
                (fn2-machines-reclaim fn2-machinesp fn2-machines-wfp)))))
(defthm fn2-machines-reserved-take-install-preserved
  (implies (and (fn2-machinesp machines) (fn2-machines-wfp machines)
                (fn2-machines-partition-reservedp ord machines)
                (< 0 (fn2-machines-admission-creditsi ord machines))
                (unsigned-byte-p 32 target) (unsigned-byte-p 32 next))
    (fn2-machines-partition-reservedp ord
      (car (fn2-machines-partition-install ord target next t machines control))))
  :rule-classes :rewrite
  :hints (("Goal" :use fn2-machines-reserved-take-install-independent
           :in-theory
           (e/d (fn2-machines-partition-reservedp fn2-machines-install-list-expected
                 fn2-machines-reservation-valuesp fn2-machines-reservation-view
                 fn2-machines-reservation-put fn2-machines-active-counti
                 fn2-machines-admission-creditsi fn2-machines-connection-counti)
                (fn2-machines-partition-install fn2-machinesp fn2-machines-wfp)))))

(defthm fn2-machines-reclaim-other-reservation-frame
  (implies (and (natp other) (natp ord) (not (equal other ord)))
    (equal
     (fn2-machines-reservation-view other
       (car (fn2-machines-reclaim id ord retire machines control)))
     (fn2-machines-reservation-view other machines)))
  :hints (("Goal" :in-theory
           (e/d (fn2-machines-reclaim fn2-machines-stop-write
                 fn2-machines-reservation-view fn2-machines-active-counti
                 fn2-machines-admission-creditsi fn2-machines-connection-counti
                 update-fn2-machines-free-headi update-fn2-machines-active-counti
                 update-fn2-machines-admission-creditsi)
                (fn2-control-record-stop)))))
(defthm fn2-machines-install-other-reservation-frame
  (implies (and (natp other) (natp ord) (not (equal other ord)))
    (equal
     (fn2-machines-reservation-view other
       (car (fn2-machines-partition-install ord target next creditp machines control)))
     (fn2-machines-reservation-view other machines)))
  :hints (("Goal" :in-theory
           (e/d (fn2-machines-partition-install fn2-machines-stop-write
                 fn2-machines-reservation-view fn2-machines-active-counti
                 fn2-machines-admission-creditsi fn2-machines-connection-counti
                 update-fn2-machines-free-headi update-fn2-machines-active-counti
                 update-fn2-machines-admission-creditsi update-fn2-machines-wake-id)
                (fn2-control-record-stop)))))
