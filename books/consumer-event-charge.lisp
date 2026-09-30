; Scalar charge of the currently admitted fixed CPE grammar. The decision
; does not allocate an encoding merely to count it. Future variable group
; and staged-authority grammars must establish their own carried charges;
; they are not accepted by this constructor or the current durable codec.
(in-package "ACL2")
(include-book "consumer-store-events")

(defun fn-cec-fields-charge (values kinds)
  (declare (xargs :guard t :measure (len kinds)))
  (if (not (consp kinds)) 0
    (+ (if (eq (car kinds) :id) (+ 1 (len (fn-cp-nth 0 values))) 4)
       (fn-cec-fields-charge (if (consp values) (cdr values) nil)
                             (cdr kinds)))))

(defun fn-cec-cursor-charge (cursor)
  (declare (xargs :guard t))
  (if (not (fn-cp-cursorp cursor)) 0
    (+ 26 (len (fn-cp-nth 1 cursor)) (len (fn-cp-nth 2 cursor))
       (len (fn-cp-nth 3 cursor)) (len (fn-cp-nth 4 cursor))
       (len (fn-cp-nth 5 cursor)))))

(defun fn-cec-event-charge (event)
  (declare (xargs :guard t))
  (if (not (fn-cpe-eventp event)) 0
    (let* ((op (fn-cpe-operation event)) (kind (fn-cp-nth 0 op)))
      (+ 18 (if (eq kind :ack)
                  (fn-cec-cursor-charge (fn-cp-nth 1 op))
                (fn-cec-fields-charge (if (consp op) (cdr op) nil)
                                      (fn-cpe-kinds kind)))))))

(defthm fn-cec-fields-charge-is-encoded-length
  (implies (and (true-listp kinds) (fn-cp-fields-validp values kinds))
           (equal (fn-cec-fields-charge values kinds)
                  (len (fn-cp-fields-encode values kinds))))
  :hints (("Goal" :induct (fn-cp-fields-encode values kinds)
           :in-theory (enable fn-cec-fields-charge fn-cp-fields-encode
                              fn-cp-fields-validp fn-cp-id-bytes))))

(defthm fn-cec-cursor-charge-is-encoded-length
  (equal (fn-cec-cursor-charge cursor) (len (fn-cp-cursor-encode cursor)))
  :hints (("Goal" :in-theory (enable fn-cec-cursor-charge fn-cp-cursor-encode
                                    fn-cp-id-bytes))))

; Constructor correspondence to the exact codec the owner persists. This
; keystone does not establish canonical tree charge or durable acceptance.
(defthm fn-cec-event-charge-is-encoded-length
  (equal (fn-cec-event-charge event) (len (fn-cpe-encode event)))
  :hints (("Goal" :in-theory
           (e/d (fn-cec-event-charge fn-cpe-encode fn-cpe-eventp
                  fn-cpe-operationp fn-cpe-kinds fn-cpe-operation
                  fn-cpe-sequence fn-cpe-txid fn-cpe-generation
                  fn-cp-nth fn-cp-fields-encode fn-cp-id-bytes)
                (fn-cp-cursor-encode fn-cec-cursor-charge
                 fn-cp-cursorp fn-cp-idp fn-cp-fields-validp)))))

(in-theory (disable fn-cec-fields-charge fn-cec-cursor-charge
                    fn-cec-event-charge))
