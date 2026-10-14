; Captured reader transport for the owner models called by host writers.
(in-package "ACL2")
(include-book "owner-retain-captured-frames")
(include-book "owner-retain-captured-io-frame")
(include-book "owner-host-relation")
(include-book "owner-identity-prepare")
(local (defthm fn-k1-secret-keeps-store
 (equal (fn-own-store (fn-own-with-node-secret o secret)) (fn-own-store o))
 :hints (("Goal" :in-theory '(fn-own-with-node-secret fn-own-store-of-fn-own-make)))))
(local (defthm fn-k1-osb-keeps-store
 (equal (fn-own-store (mv-nth 1 (fn-osb-install o profile))) (fn-own-store o))
 :hints (("Goal" :in-theory '(fn-osb-install fn-own-configure fn-own-store-of-fn-own-make
                             mv-nth nth car-cons cdr-cons (:e zp))))))
(local (defthm fn-k1-pass-keeps-config
 (equal (fn-ocfg-config (fn-ocfg-pass oc event fn-arena)) (fn-ocfg-config oc))
 :hints (("Goal" :in-theory '(fn-ocfg-pass fn-ocfg-with-owner fn-ocfg-config-of-fn-ocfg-make)))))
(local (defthm fn-k1-close-preserves-lgoc
 (implies (fn-lgoc-invariantp oc) (fn-lgoc-invariantp (fn-ocfg-close oc id)))
 :hints (("Goal" :use (fn-ohr-step-close-preserves-carried-relation)
          :in-theory '(fn-ocfg-step car-cons cdr-cons (:e equal) (:e car) (:e cdr))))))
(local (defthm fn-k1-close-keeps-config
 (equal (fn-ocfg-config (fn-ocfg-close oc id)) (fn-ocfg-config oc))
 :hints (("Goal" :in-theory '(fn-ocfg-close fn-ocfg-config-of-fn-ocfg-make fn-ocfg-with-owner car-cons cdr-cons
                              (:e equal) (:e car) (:e cdr))))))
(defthm fn-k1-close-keeps-durable-context
 (implies (fn-lgoc-invariantp oc)
  (let* ((next (fn-ocfg-close oc id)) (old (fn-own-store (fn-ocfg-owner oc)))
         (new (fn-own-store (fn-ocfg-owner next))))
   (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
        (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
        (equal (fn-sn-config-history new) (fn-sn-config-history old))
        (equal (fn-ocfg-config next) (fn-ocfg-config oc)))))
 :hints (("Goal" :use (fn-k1-close-keeps-config) :in-theory '(fn-ohr-close-keeps-store fn-k1-close-keeps-config
                  fn-lgoc-invariantp fn-ohr-relation-owner-shapep))))
(defthm fn-k1-close-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (fn-ocfg-close oc id)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-k1-captured-views-transport-same-history
                         (oc0 oc) (oc (fn-ocfg-close oc id))))
          :in-theory '(fn-k1-close-preserves-lgoc fn-k1-close-keeps-durable-context fn-ocfg-step car-cons cdr-cons (:e equal) (:e car) (:e cdr)))))
(local (defthm fn-k1-fault-keeps-config
 (equal (fn-ocfg-config (cdr (fn-ocfg-fault oc id))) (fn-ocfg-config oc))
 :hints (("Goal" :in-theory '(fn-ocfg-fault fn-ocfg-config-of-fn-ocfg-make fn-ocfg-with-owner car-cons cdr-cons
                              (:e equal) (:e car) (:e cdr))))))
(defthm fn-k1-fault-keeps-durable-context
 (implies (fn-lgoc-invariantp oc)
  (let* ((next (cdr (fn-ocfg-fault oc id))) (old (fn-own-store (fn-ocfg-owner oc)))
         (new (fn-own-store (fn-ocfg-owner next))))
   (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
        (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
        (equal (fn-sn-config-history new) (fn-sn-config-history old))
        (equal (fn-ocfg-config next) (fn-ocfg-config oc)))))
 :hints (("Goal" :use (fn-k1-fault-keeps-config) :in-theory '(fn-ohr-fault-keeps-store fn-k1-fault-keeps-config
                  fn-lgoc-invariantp fn-ohr-relation-owner-shapep))))
(defthm fn-k1-fault-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (cdr (fn-ocfg-fault oc id))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-k1-captured-views-transport-same-history
                         (oc0 oc) (oc (cdr (fn-ocfg-fault oc id)))))
          :in-theory '(fn-ohr-fault-preserves-carried-relation fn-k1-fault-keeps-durable-context))))
(local (defthm fn-k1-open-peer-keeps-config
 (equal (fn-ocfg-config (cdr (fn-ocfg-open-peer oc peer acfg))) (fn-ocfg-config oc))
 :hints (("Goal" :in-theory '(fn-ocfg-open-peer fn-ocfg-config-of-fn-ocfg-make fn-ocfg-with-owner car-cons cdr-cons
                              (:e equal) (:e car) (:e cdr))))))
(defthm fn-k1-open-peer-keeps-durable-context
 (implies (fn-lgoc-invariantp oc)
  (let* ((next (cdr (fn-ocfg-open-peer oc peer acfg))) (old (fn-own-store (fn-ocfg-owner oc)))
         (new (fn-own-store (fn-ocfg-owner next))))
   (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
        (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
        (equal (fn-sn-config-history new) (fn-sn-config-history old))
        (equal (fn-ocfg-config next) (fn-ocfg-config oc)))))
 :hints (("Goal" :use (fn-k1-open-peer-keeps-config) :in-theory '(fn-ohr-open-peer-keeps-store-and-view fn-k1-open-peer-keeps-config
                  fn-lgoc-invariantp fn-ohr-relation-owner-shapep))))
(defthm fn-k1-open-peer-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (cdr (fn-ocfg-open-peer oc peer acfg))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-k1-captured-views-transport-same-history
                         (oc0 oc) (oc (cdr (fn-ocfg-open-peer oc peer acfg)))))
          :in-theory '(fn-ohr-open-peer-preserves-carried-relation fn-k1-open-peer-keeps-durable-context))))
(local (defthm fn-k1-take-keeps-config
 (equal (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-ocfg-config oc))
 :hints (("Goal" :in-theory '(fn-ocfg-step fn-ocfg-pass fn-ocfg-config-of-fn-ocfg-make fn-ocfg-with-owner car-cons cdr-cons
                              (:e equal) (:e car) (:e cdr))))))
(defthm fn-k1-take-keeps-durable-context
 (implies (fn-lgoc-invariantp oc)
  (let* ((next (fn-ocfg-step oc (list :take) fn-arena)) (old (fn-own-store (fn-ocfg-owner oc)))
         (new (fn-own-store (fn-ocfg-owner next))))
   (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
        (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
        (equal (fn-sn-config-history new) (fn-sn-config-history old))
        (equal (fn-ocfg-config next) (fn-ocfg-config oc)))))
 :hints (("Goal" :use (fn-k1-take-keeps-config) :in-theory '(fn-ohr-pass-take-keeps-store fn-k1-take-keeps-config
                  fn-lgoc-invariantp fn-ohr-relation-owner-shapep fn-ocfg-step fn-k1-pass-keeps-config car-cons cdr-cons (:e equal) (:e car) (:e cdr)))))
(defthm fn-k1-take-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (fn-ocfg-step oc (list :take) fn-arena)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-k1-captured-views-transport-same-history
                         (oc0 oc) (oc (fn-ocfg-step oc (list :take) fn-arena))))
          :in-theory '(fn-ohr-step-take-preserves-carried-relation fn-k1-take-keeps-durable-context))))
(local (defthm fn-k1-control-submit-keeps-config
 (equal (fn-ocfg-config (fn-ocfg-step oc (list :control-submit msgid groups octets) fn-arena)) (fn-ocfg-config oc))
 :hints (("Goal" :in-theory '(fn-ocfg-step fn-ocfg-pass fn-ocfg-config-of-fn-ocfg-make fn-ocfg-with-owner car-cons cdr-cons
                              (:e equal) (:e car) (:e cdr))))))
(defthm fn-k1-control-submit-keeps-durable-context
 (implies (fn-lgoc-invariantp oc)
  (let* ((next (fn-ocfg-step oc (list :control-submit msgid groups octets) fn-arena)) (old (fn-own-store (fn-ocfg-owner oc)))
         (new (fn-own-store (fn-ocfg-owner next))))
   (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
        (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
        (equal (fn-sn-config-history new) (fn-sn-config-history old))
        (equal (fn-ocfg-config next) (fn-ocfg-config oc)))))
 :hints (("Goal" :use (fn-k1-control-submit-keeps-config) :in-theory '(fn-ohr-pass-control-submit-keeps-store fn-k1-control-submit-keeps-config
                  fn-lgoc-invariantp fn-ohr-relation-owner-shapep fn-ocfg-step fn-k1-pass-keeps-config car-cons cdr-cons (:e equal) (:e car) (:e cdr)))))
(defthm fn-k1-control-submit-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (fn-ocfg-step oc (list :control-submit msgid groups octets) fn-arena)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-k1-captured-views-transport-same-history
                         (oc0 oc) (oc (fn-ocfg-step oc (list :control-submit msgid groups octets) fn-arena))))
          :in-theory '(fn-ohr-step-control-submit-preserves-carried-relation fn-k1-control-submit-keeps-durable-context))))
(local (defthm fn-k1-secret-keeps-config
 (equal (fn-ocfg-config (fn-ocfg-with-owner oc (fn-own-with-node-secret (fn-ocfg-owner oc) secret))) (fn-ocfg-config oc))
 :hints (("Goal" :in-theory '(fn-ocfg-with-owner fn-ocfg-config-of-fn-ocfg-make fn-ocfg-with-owner car-cons cdr-cons
                              (:e equal) (:e car) (:e cdr))))))
(defthm fn-k1-secret-keeps-durable-context
 (implies (fn-lgoc-invariantp oc)
  (let* ((next (fn-ocfg-with-owner oc (fn-own-with-node-secret (fn-ocfg-owner oc) secret))) (old (fn-own-store (fn-ocfg-owner oc)))
         (new (fn-own-store (fn-ocfg-owner next))))
   (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
        (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
        (equal (fn-sn-config-history new) (fn-sn-config-history old))
        (equal (fn-ocfg-config next) (fn-ocfg-config oc)))))
 :hints (("Goal" :use (fn-k1-secret-keeps-config) :in-theory '(fn-ohr-with-owner-store fn-k1-secret-keeps-store fn-k1-secret-keeps-config
                  fn-lgoc-invariantp fn-ohr-relation-owner-shapep))))
(defthm fn-k1-secret-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (fn-ocfg-with-owner oc (fn-own-with-node-secret (fn-ocfg-owner oc) secret))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-k1-captured-views-transport-same-history
                         (oc0 oc) (oc (fn-ocfg-with-owner oc (fn-own-with-node-secret (fn-ocfg-owner oc) secret)))))
          :in-theory '(fn-ohr-with-node-secret-preserves-carried-relation fn-k1-secret-keeps-durable-context))))
(local (defthm fn-k1-osb-keeps-config
 (equal (fn-ocfg-config (fn-ocfg-with-owner oc (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile)))) (fn-ocfg-config oc))
 :hints (("Goal" :in-theory '(fn-ocfg-with-owner fn-ocfg-config-of-fn-ocfg-make fn-ocfg-with-owner car-cons cdr-cons
                              (:e equal) (:e car) (:e cdr))))))
(defthm fn-k1-osb-keeps-durable-context
 (implies (fn-lgoc-invariantp oc)
  (let* ((next (fn-ocfg-with-owner oc (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile)))) (old (fn-own-store (fn-ocfg-owner oc)))
         (new (fn-own-store (fn-ocfg-owner next))))
   (and (equal (fn-sf-records (fn-sn-files new)) (fn-sf-records (fn-sn-files old)))
        (equal (fn-sf-frontier (fn-sn-files new)) (fn-sf-frontier (fn-sn-files old)))
        (equal (fn-sn-config-history new) (fn-sn-config-history old))
        (equal (fn-ocfg-config next) (fn-ocfg-config oc)))))
 :hints (("Goal" :use (fn-k1-osb-keeps-config) :in-theory '(fn-ohr-with-owner-store fn-k1-osb-keeps-store fn-k1-osb-keeps-config
                  fn-lgoc-invariantp fn-ohr-relation-owner-shapep))))
(defthm fn-k1-osb-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (fn-ocfg-with-owner oc (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-k1-captured-views-transport-same-history
                         (oc0 oc) (oc (fn-ocfg-with-owner oc (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile))))))
          :in-theory '(fn-ohr-osb-install-preserves-carried-relation fn-k1-osb-keeps-durable-context))))

(defthm fn-k1-idrp-captured-views
 (implies (and (fn-lgoc-invariantp oc)
               (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg
           views (mv-nth 1 (fn-idrp-prepare-retention oc event grant fn-arena))))
 :rule-classes nil
 :hints (("Goal"
          :use (fn-idrp-retention-preparation-consumes-exact-current-grant)
          :in-theory '(fn-k1-captured-views-of-prepare-retention))))
