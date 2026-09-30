; Join a saved authority proposal into the actual durable configuration result.
; The join reconstructs fixed Store/owner spines without fn-own-refresh.
; No second revision computation or shared metadata scan occurs here. The owner
; collector must atomically install the full result and carried sidecars.
(in-package "ACL2")
(include-book "config-owner-carried")
(include-book "consumer-config-authority")

(defun fn-ccp-owner-with-approved (oc approved)
  (declare (xargs :guard t))
  (let* ((owner (fn-ocfg-owner oc))
         (store (fn-own-store owner)))
    (fn-ocfg-with-owner
     oc (fn-own-make
         (fn-sn-with-consumer store (fn-cp-nth 1 approved))
         (fn-own-view owner) (fn-own-conns owner) (fn-own-next-id owner)
         (fn-own-max-conns owner) (fn-own-pending owner)
         (fn-own-ledger-field owner) (fn-own-clock owner) (fn-own-facts owner)
         (fn-own-config owner) (fn-own-queue owner) (fn-own-inflight owner)
         (fn-own-feeds owner) (fn-own-node-secret owner) (fn-own-refused owner)))))

; Bounded projection of the one existing configuration decision. :REFUSED
; after a reported durable write is recovery-required at this boundary too.
; NIL publication root preserves the committed adopted account root; it never
; means an empty authentication root. Metadata NIL establishes no readiness.
(defun fn-ccp-collect (verdict next old approved)
  (declare (xargs :guard t))
  (if (and (eq (fn-cp-nth 0 approved) :ok) (eq verdict :durable))
      (list :durable (fn-ccp-owner-with-approved next approved)
            (fn-cp-nth 2 approved) nil)
    (list :recovery-required old nil nil)))

; The actual host calls this composed publication once, after consuming the
; captured staged-object proposal. CP7 is joined before any owner publication.
(defun fn-ccp-publish (oc generation max-octets approved)
  (declare (xargs :guard t))
  (if (not (eq (fn-cp-nth 0 approved) :ok))
      (list :recovery-required oc nil nil)
    (mv-let (verdict next)
      (fn-oclc-publish oc generation max-octets)
      (fn-ccp-collect verdict next oc approved))))

; The full-result boundary retains the saved CP and metadata literally. The
; original durable configuration verdict is required, not inferred from a
; nonempty record or a matching generation supplied by the caller.
(defthm fn-ccp-durable-collector-installs-the-approved-consumer
  (implies (and (eq verdict :durable) (eq (fn-cp-nth 0 approved) :ok))
           (let* ((one (fn-ccp-collect verdict next old approved))
                  (owner (fn-ocfg-owner (fn-cp-nth 1 one))))
             (and (eq (fn-cp-nth 0 one) :durable)
                  (equal (fn-sn-consumer (fn-own-store owner))
                         (fn-cp-nth 1 approved))
                  (equal (fn-cp-nth 2 one) (fn-cp-nth 2 approved))
                  (null (fn-cp-nth 3 one)))))
  :hints (("Goal" :in-theory
           (enable fn-ccp-collect fn-ccp-owner-with-approved
                   fn-ocfg-with-owner fn-cp-nth fn-sn-with-consumer
                   fn-sn-make-v6 fn-sn-consumer))))

(defthm fn-ccp-unapproved-publication-requires-recovery
  (implies (not (eq (fn-cp-nth 0 approved) :ok))
           (equal (fn-ccp-publish oc generation max-octets approved)
                  (list :recovery-required oc nil nil)))
  :hints (("Goal" :in-theory (enable fn-ccp-publish))))

(in-theory (disable fn-ccp-owner-with-approved fn-ccp-collect fn-ccp-publish))
