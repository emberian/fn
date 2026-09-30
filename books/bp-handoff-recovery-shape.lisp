; Typed handoff grammar from the real delivery producer and computed
; handed-off observation. No package interning or guessed symbol ceiling.
(in-package "ACL2")
(include-book "bp-node-machine")

(defun fn-bphs-exact-listp (x n)
  (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (if (zp (nfix n)) (null x)
    (and (consp x) (fn-bphs-exact-listp (cdr x) (1- (nfix n))))))

(defun fn-bphs-bundle-idp (id)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bphs-exact-listp id 6)
       (equal (nth 0 id) :fn-bp-bundle-id)
       (fn-bpp-eidp (nth 1 id))
       (fn-bpp-timep (nth 2 id)) (fn-bpp-timep (nth 3 id))
       (or (and (null (nth 4 id)) (null (nth 5 id)))
           (and (natp (nth 4 id)) (natp (nth 5 id))))))

(defun fn-bphs-triggerp (trigger)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bphs-exact-listp trigger 2)
       (or (null (nth 0 trigger)) (fn-bpn-machine-textp (nth 0 trigger)))
       (fn-bphs-bundle-idp (nth 1 trigger))))

(defun fn-bphs-handoffp (handoff)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bphs-exact-listp handoff 4)
       (equal (nth 0 handoff) :bpnf-handoff)
       (fn-cbor-octet-listp (nth 1 handoff)) (consp (nth 1 handoff))
       (<= (len (nth 1 handoff)) 256)
       (fn-bphs-triggerp (nth 2 handoff))
       (or (equal (nth 3 handoff) :owed)
           (and (fn-bphs-exact-listp (nth 3 handoff) 2)
                (equal (nth 0 (nth 3 handoff)) :handed-off)
                (natp (nth 1 (nth 3 handoff)))))))

(defun fn-bphs-handoffs-p (handoffs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom handoffs) (null handoffs)
    (and (fn-bphs-handoffp (car handoffs))
         (fn-bphs-handoffs-p (cdr handoffs)))))

; Proof-only recursive vocabulary. This is not a served revalidation pass.
(defun fn-bphs-symbol-domain-p (x)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp x)
      (and (fn-bphs-symbol-domain-p (car x)) (fn-bphs-symbol-domain-p (cdr x)))
    (or (not (symbolp x))
        (member-eq x '(nil :bpnf-handoff :owed :handed-off
                          :fn-bp-bundle-id :dtn :dtn-none :ipn)))))

(defthm fn-bphs-exact-listp-establishes-proper-list
  (implies (fn-bphs-exact-listp x n) (true-listp x))
  :hints (("Goal" :induct (fn-bphs-exact-listp x n)
            :in-theory (union-theories
              '(fn-bphs-exact-listp true-listp nfix natp zp)
              (theory 'minimal-theory)))))

(verify-guards fn-bphs-exact-listp)
(verify-guards fn-bphs-bundle-idp)
(verify-guards fn-bphs-triggerp)
(verify-guards fn-bphs-handoffp
 :hints (("Goal" :in-theory (disable fn-bphs-exact-listp fn-bphs-triggerp
                                     fn-cbor-octet-listp))))
(verify-guards fn-bphs-handoffs-p)
(verify-guards fn-bphs-symbol-domain-p)

(defthm fn-bphs-real-bundle-id-has-recovery-shape
  (implies (and (fn-bpp-blockp primary) (natp payload-length))
           (fn-bphs-bundle-idp (fn-bpp-bundle-id primary payload-length)))
  :hints (("Goal" :in-theory
    (union-theories
      '(fn-bphs-bundle-idp fn-bphs-exact-listp fn-bpp-bundle-id fn-bpp-blockp
        fn-bpp-timep fn-bpp-flags fn-bpp-crc-type fn-bpp-destination
        fn-bpp-source fn-bpp-report-to fn-bpp-creation-time fn-bpp-sequence
        fn-bpp-lifetime fn-bpp-fragment-offset fn-bpp-total-adu-length
        natp nth true-listp nfix zp car-cons cdr-cons
        cons car cdr consp equal not binary-+ < integerp)
      (theory 'minimal-theory))))
  :rule-classes nil)
