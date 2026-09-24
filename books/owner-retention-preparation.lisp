; The native owner retention preparation call constructs an ACL2 Store event
; and sends it through fn-ocfg-step.  This book names that exact owner path.
(in-package "ACL2")

(include-book "owner-config")

(local
 (defthm fn-orpr-owner-store-of-prepare-retention
   (equal
    (fn-own-store (fn-own-step o (list :store (list :prepare-retention event))))
   (fn-sn-prepare-retention (fn-own-store o) event))
   :hints (("Goal"
            :in-theory (e/d (fn-own-step fn-own-store-step fn-own-refresh
                              fn-own-store-of-fn-own-make fn-snrt-step)
                            (fn-sn-prepare-retention))))))

(defthm fn-orpr-configured-store-of-prepare-retention
  (equal
   (fn-own-store
    (fn-ocfg-owner
     (fn-ocfg-step oc (list :store (list :prepare-retention event)))))
   (fn-sn-prepare-retention
    (fn-own-store (fn-ocfg-owner oc)) event))
  :hints (("Goal"
           :use ((:instance fn-orpr-owner-store-of-prepare-retention
                            (o (fn-ocfg-owner oc))))
           :in-theory
           (e/d (fn-ocfg-step fn-ocfg-pass fn-ocfg-with-owner)
                (fn-own-step fn-own-store-step fn-sn-prepare-retention)))))

(local
 (defthm fn-orpr-file-prepare-staged-candidate
   (implies
    (and (equal (fn-sf-phase files) :reserved)
         (equal (fn-sf-phase
                 (fn-sf-prepare-record files event groups capacity))
                :record-staged))
    (equal (fn-sf-record-candidate
            (fn-sf-prepare-record files event groups capacity))
           event))
   :hints (("Goal" :in-theory (enable fn-sf-prepare-record)))))

(local
 (defthm fn-orpr-node-prepare-branches
   (implies
    (equal (fn-sf-phase (fn-sn-files s)) :reserved)
    (let ((prepared (fn-sn-prepare-retention s event)))
      (if (equal prepared s)
          (not (equal (fn-sf-phase (fn-sn-files prepared))
                      :record-staged))
        (and (equal (fn-sf-phase (fn-sn-files prepared))
                    :record-staged)
             (equal (fn-sf-record-candidate (fn-sn-files prepared))
                    event)))))
   :rule-classes nil
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance fn-orpr-file-prepare-staged-candidate
                             (files (fn-sn-files s))
                             (groups (fn-sn-groups s))
                             (capacity (fn-sn-capacity s))))
            :in-theory (e/d (fn-sn-prepare-retention fn-sn-update)
                            (fn-sf-prepare-record))))))

; host/owner-host.lisp:360-378 passes precisely this constructor to
; fn-owner-step, whose logical subject is fn-ocfg-step.  The host's
; fn-store-octets->string is fn-record-octets-string (host/store-host.lisp).
; In a reserved store, an unchanged Store projection is the host's :refused
; branch; every changed projection is staged with the supplied event.
(defthm fn-orpr-host-retention-prepare-branches
  (implies
   (equal (fn-sf-phase
           (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) :reserved)
   (let* ((s (fn-own-store (fn-ocfg-owner oc)))
          (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s))))
          (event (fn-store-retention-event-make
                  kind (fn-sn-identity-next s) txid txid
                  (fn-record-octets-string id-octets)
                  (fn-record-octets-string subject-octets)
                  (fn-record-octets-string evidence-octets) charge))
          (next (fn-ocfg-step oc
                              (list :store (list :prepare-retention event))))
          (prepared (fn-own-store (fn-ocfg-owner next))))
     (and (equal prepared (fn-sn-prepare-retention s event))
          (if (equal prepared s)
              (not (equal (fn-sf-phase (fn-sn-files prepared))
                          :record-staged))
            (and (equal (fn-sf-phase (fn-sn-files prepared))
                        :record-staged)
                 (equal (fn-sf-record-candidate (fn-sn-files prepared))
                        event))))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-orpr-node-prepare-branches
                            (s (fn-own-store (fn-ocfg-owner oc)))
                            (event (fn-store-retention-event-make
                                    kind
                                    (fn-sn-identity-next
                                     (fn-own-store (fn-ocfg-owner oc)))
                                    (fn-state-next-txid
                                     (fn-node-acceptance
                                      (fn-sn-node
                                       (fn-own-store (fn-ocfg-owner oc)))))
                                    (fn-state-next-txid
                                     (fn-node-acceptance
                                      (fn-sn-node
                                       (fn-own-store (fn-ocfg-owner oc)))))
                                    (fn-record-octets-string id-octets)
                                    (fn-record-octets-string subject-octets)
                                    (fn-record-octets-string evidence-octets)
                                    charge))))
           :in-theory (e/d (fn-orpr-configured-store-of-prepare-retention)
                           (fn-sn-prepare-retention fn-ocfg-step
                            fn-own-step fn-sf-prepare-record
                            fn-record-octets-string
                            fn-store-retention-event-make)))))
