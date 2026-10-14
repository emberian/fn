; Captured reader transport across durable-context-preserving owner prepares.
(in-package "ACL2")
(include-book "owner-retain-transitions")
(include-book "owner-prepare-deferred-carried")
(include-book "owner-prepare-outcome")
(include-book "owner-prepare-served-ocl")
(include-book "owner-log-ocl")

(defthm fn-k1-captured-views-transport-same-history
 (implies
  (and (fn-lgoc-invariantp oc0) (fn-lgoc-invariantp oc)
       (fn-captured-views-follow-ocfg views oc0)
       (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
              (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0)))))
       (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
              (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc0))))
       (equal (fn-ocfg-config oc) (fn-ocfg-config oc0))
       (equal (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
              (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))))
  (fn-captured-views-follow-ocfg views oc))
 :hints (("Goal" :induct (fn-captured-views-follow-ocfg views oc0)
           :in-theory '(fn-captured-views-follow-ocfg
                        fn-k1-captured-view-transport-same-history))))
(local
 (defthm fn-k1-deferred-config-of-with-owner
  (equal (fn-ocfg-config (fn-ocfg-with-owner oc owner)) (fn-ocfg-config oc))
  :hints (("Goal" :in-theory '(fn-ocfg-with-owner fn-ocfg-config-of-fn-ocfg-make)))))

(local
 (defthm fn-k1-consumer-keeps-frontier
  (equal (fn-sf-frontier (fn-sn-files (fn-pdc-sn-prepare-consumer st e)))
         (fn-sf-frontier (fn-sn-files st)))
  :hints (("Goal"
   :use ((:instance fn-psrv-pcar-stage-record-staged (files (fn-sn-files st))))
   :in-theory '( fn-pdc-sn-prepare-consumer fn-cstp-sn-update-fields)))))
(defthm fn-k1-consumer-keeps-durable-context
 (let* ((next (fn-pdc-ocfg-prepare-consumer oc e))
        (old (fn-own-store (fn-ocfg-owner oc)))
        (new (fn-own-store (fn-ocfg-owner next))))
  (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
       (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
       (equal (fn-sn-config-history new) (fn-sn-config-history old))
       (equal (fn-ocfg-config next) (fn-ocfg-config oc))))
 :hints (("Goal" :in-theory
  '( fn-pdc-ocfg-prepare-consumer fn-lgoc-store-of-owner-with-store
     fn-pdc-sn-prepares-keep-histories fn-k1-consumer-keeps-frontier
     fn-k1-deferred-config-of-with-owner))))
(defthm fn-k1-captured-views-of-prepare-consumer
 (implies (and (fn-lgoc-invariantp oc)
               (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (fn-pdc-ocfg-prepare-consumer oc e)))
 :hints (("Goal"
  :use ((:instance fn-k1-captured-views-transport-same-history
          (oc0 oc) (oc (fn-pdc-ocfg-prepare-consumer oc e))))
  :in-theory '( fn-pdc-ocfg-prepare-consumer-preserves-invariant
                fn-k1-consumer-keeps-durable-context))))

(local
 (defthm fn-k1-topic-keeps-frontier
  (equal (fn-sf-frontier (fn-sn-files (fn-pdc-sn-prepare-topic st e)))
         (fn-sf-frontier (fn-sn-files st)))
  :hints (("Goal"
   :use ((:instance fn-psrv-pcar-stage-record-staged (files (fn-sn-files st))))
   :in-theory '( fn-pdc-sn-prepare-topic fn-cstp-sn-update-fields)))))
(defthm fn-k1-topic-keeps-durable-context
 (let* ((next (fn-pdc-psrv-prepare-topic oc e))
        (old (fn-own-store (fn-ocfg-owner oc)))
        (new (fn-own-store (fn-ocfg-owner next))))
  (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
       (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
       (equal (fn-sn-config-history new) (fn-sn-config-history old))
       (equal (fn-ocfg-config next) (fn-ocfg-config oc))))
 :hints (("Goal" :in-theory
  '( fn-pdc-psrv-prepare-topic fn-lgoc-store-of-owner-with-store
     fn-pdc-sn-prepares-keep-histories fn-k1-topic-keeps-frontier
     fn-k1-deferred-config-of-with-owner))))
(defthm fn-k1-captured-views-of-prepare-topic
 (implies (and (fn-lgoc-invariantp oc)
               (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (fn-pdc-psrv-prepare-topic oc e)))
 :hints (("Goal"
  :use ((:instance fn-k1-captured-views-transport-same-history
          (oc0 oc) (oc (fn-pdc-psrv-prepare-topic oc e))))
  :in-theory '( fn-pdc-psrv-prepare-topic-preserves-invariant
                fn-k1-topic-keeps-durable-context))))

(local
 (defthm fn-k1-retention-keeps-frontier
  (equal (fn-sf-frontier (fn-sn-files (fn-pdc-sn-prepare-retention st e)))
         (fn-sf-frontier (fn-sn-files st)))
  :hints (("Goal"
   :use ((:instance fn-psrv-pcar-stage-record-staged (files (fn-sn-files st))))
   :in-theory '( fn-pdc-sn-prepare-retention fn-cstp-sn-update-fields)))))
(defthm fn-k1-retention-keeps-durable-context
 (let* ((next (fn-pdc-ocfg-prepare-retention oc e))
        (old (fn-own-store (fn-ocfg-owner oc)))
        (new (fn-own-store (fn-ocfg-owner next))))
  (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
       (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
       (equal (fn-sn-config-history new) (fn-sn-config-history old))
       (equal (fn-ocfg-config next) (fn-ocfg-config oc))))
 :hints (("Goal" :in-theory
  '( fn-pdc-ocfg-prepare-retention fn-lgoc-store-of-owner-with-store
     fn-pdc-sn-prepares-keep-histories fn-k1-retention-keeps-frontier
     fn-k1-deferred-config-of-with-owner))))
(defthm fn-k1-captured-views-of-prepare-retention
 (implies (and (fn-lgoc-invariantp oc)
               (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (fn-pdc-ocfg-prepare-retention oc e)))
 :hints (("Goal"
  :use ((:instance fn-k1-captured-views-transport-same-history
          (oc0 oc) (oc (fn-pdc-ocfg-prepare-retention oc e))))
  :in-theory '( fn-pdc-ocfg-prepare-retention-preserves-invariant
                fn-k1-retention-keeps-durable-context))))

; Resolution leaves every captured durable context in place.
(defthm fn-k1-retain-statep-implies-captured-views
 (implies (fn-owner-retain-statep state)
          (fn-captured-views-follow-ocfg (fn-owner-reader-views state) (fn-owner-ocfg state)))
 :rule-classes nil
 :hints (("Goal" :in-theory '(fn-owner-retain-statep fn-owner-captured-view-follows-store))))
(defthm fn-k1-refuse-reservation-keeps-durable-context
 (and (equal (fn-sf-frontier (fn-sn-files (fn-sn-refuse-reservation s txid)))
             (fn-sf-frontier (fn-sn-files s)))
      (equal (fn-sf-records (fn-sn-files (fn-sn-refuse-reservation s txid)))
             (fn-sf-records (fn-sn-files s)))
      (equal (fn-sn-config-history (fn-sn-refuse-reservation s txid))
             (fn-sn-config-history s)))
 :hints (("Goal" :use (fn-cstp-refuse-reservation-cases) :in-theory nil)))
(defthm fn-k1-known-abort-keeps-frontier
 (equal (fn-sf-frontier (fn-sn-files (fn-sn-known-abort s)))
        (fn-sf-frontier (fn-sn-files s)))
 :hints (("Goal" :use (fn-psrv-known-abort-cases
                       (:instance fn-psrv-known-abort-files-facts (files (fn-sn-files s)))
                       (:instance fn-cstp-sn-statep-files (st s)))
          :in-theory nil)))
(defthm fn-k1-pout-refuse-reservation-keeps-durable-context
 (let* ((next (mv-nth 1 (fn-pout-refuse-reservation oc fn-arena))) (old (fn-own-store (fn-ocfg-owner oc)))
        (new (fn-own-store (fn-ocfg-owner next))))
  (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
       (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
       (equal (fn-sn-config-history new) (fn-sn-config-history old))
       (equal (fn-ocfg-config next) (fn-ocfg-config oc))))
 :hints (("Goal" :in-theory '(fn-pout-refuse-reservation mv-nth nth car-cons cdr-cons
   fn-lgoc-store-of-owner-with-store fn-k1-deferred-config-of-with-owner
   fn-lgoc-refuse-reservation-is-owner-with-store fn-k1-refuse-reservation-keeps-durable-context (:executable-counterpart zp)))))
(defthm fn-k1-pout-refuse-reservation-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (mv-nth 1 (fn-pout-refuse-reservation oc fn-arena))))
 :rule-classes nil
 :hints (("Goal"
 :use ((:instance fn-k1-captured-views-transport-same-history (oc0 oc) (oc (mv-nth 1 (fn-pout-refuse-reservation oc fn-arena)))))
 :in-theory '(fn-pout-refuse-reservation mv-nth nth car-cons cdr-cons
              fn-lgoc-refuse-reservation-preserves-invariant
              fn-psrv-known-abort-preserves-invariant
              fn-k1-pout-refuse-reservation-keeps-durable-context
              (:executable-counterpart zp)))))
(defthm fn-k1-pout-known-abort-keeps-durable-context
 (let* ((next (mv-nth 1 (fn-pout-known-abort oc fn-arena))) (old (fn-own-store (fn-ocfg-owner oc)))
        (new (fn-own-store (fn-ocfg-owner next))))
  (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
       (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
       (equal (fn-sn-config-history new) (fn-sn-config-history old))
       (equal (fn-ocfg-config next) (fn-ocfg-config oc))))
 :hints (("Goal" :in-theory '(fn-pout-known-abort mv-nth nth car-cons cdr-cons
   fn-lgoc-store-of-owner-with-store fn-k1-deferred-config-of-with-owner
   fn-psrv-store-step-is-owner-with-store fn-snrt-step fn-k1-known-abort-keeps-frontier fn-psrv-known-abort-keeps-histories (:executable-counterpart zp)))))
(defthm fn-k1-pout-known-abort-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (mv-nth 1 (fn-pout-known-abort oc fn-arena))))
 :rule-classes nil
 :hints (("Goal"
 :use ((:instance fn-k1-captured-views-transport-same-history (oc0 oc) (oc (mv-nth 1 (fn-pout-known-abort oc fn-arena)))))
 :in-theory '(fn-pout-known-abort mv-nth nth car-cons cdr-cons
              fn-psrv-known-abort-preserves-invariant
              fn-k1-pout-known-abort-keeps-durable-context
              (:executable-counterpart zp)))))

; Article staging preserves captured-reader history and physical frontier.
(local (defthm fn-k1-article-prepare-context
 (implies (fn-prc-carryp carry)
 (let* ((next (fn-psrv-prepare oc record budget carry))
        (old (fn-own-store (fn-ocfg-owner oc))) (new (fn-own-store (fn-ocfg-owner next))))
  (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
       (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
       (equal (fn-sn-config-history new) (fn-sn-config-history old))
       (equal (fn-ocfg-config next) (fn-ocfg-config oc)))))
 :hints (("Goal" :use ((:instance fn-psrv-pcar-stage-record-staged
                                 (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) (e record)))
 :in-theory '(fn-psrv-prepare fn-prc-sbud-prepare-is-pidx-sbud-prepare
              fn-pcar-sbud-prepare fn-pcar-opc-prepare fn-pcar-opc-owner-prepare
              fn-pcar-spc-prepare fn-own-refresh-keeps-fields
              fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make fn-ocfg-config-of-fn-ocfg-make
              fn-own-store-of-fn-own-make fn-cstp-sn-update-fields fn-sbud-oc-store)))))
(defthm fn-k1-article-prepare-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-prc-carryp carry)
               (fn-captured-views-follow-ocfg views oc))
  (fn-captured-views-follow-ocfg views (fn-psrv-prepare oc record budget carry)))
 :rule-classes nil
 :hints (("Goal"
 :use ((:instance fn-k1-captured-views-transport-same-history
         (oc0 oc) (oc (fn-psrv-prepare oc record budget carry)))
       (:instance fn-psrv-prepare-preserves-invariant))
 :in-theory '(fn-k1-article-prepare-context))))
