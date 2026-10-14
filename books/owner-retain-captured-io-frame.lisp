; Reader captures remain coherent across the host's file and log observations.
(in-package "ACL2")
(include-book "owner-retain-captured-frames")
(include-book "owner-log-route")
(include-book "owner-prepare-served-ocl")
(local (defthm fn-k1-len-append
 (equal (len (append xs ys)) (+ (len xs) (len ys)))
 :hints (("Goal" :induct (len xs) :in-theory (enable len binary-append)))))
(local (defthm fn-k1-append-prefix-suffix
 (implies (fn-sf-prefixp xs ys) (equal (append xs (nthcdr (len xs) ys)) ys))
 :hints (("Goal" :induct (fn-sf-prefixp xs ys)
          :in-theory (enable fn-sf-prefixp len nthcdr binary-append)))))
(defthm fn-k1-captured-view-transport-history-extension
 (implies (and (fn-lgoc-invariantp oc0) (fn-lgoc-invariantp oc) (fn-captured-view-follows-ocfg view oc0) (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) (append (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0)))) extra)) (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))) (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc0)))) (equal (fn-ocfg-config oc) (fn-ocfg-config oc0)) (<= (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc0)))) (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))) (fn-captured-view-follows-ocfg view oc))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-ocl-relation-of-a-view-captured-before-appends
          (oc0 (fn-ocfg-with-view oc0 view)))
        (:instance fn-k1-len-append (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))) (ys extra))
        (:instance fn-lgoc-invariant-statep (oc oc))
        (:instance fn-cstp-sn-statep-files (st (fn-own-store (fn-ocfg-owner oc))))
        (:instance fn-snt-typed-frontier-natural (files (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
  :in-theory (union-theories
    '(fn-captured-view-follows-ocfg fn-captured-view-follows-files
      fn-lgoc-invariantp fn-ocfg-with-view-keeps-the-rest (:type-prescription len))
    (theory 'minimal-theory)))))
(defthm fn-k1-captured-views-transport-history-prefix
 (implies (and (fn-lgoc-invariantp oc0) (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc0) (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0)))) (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))) (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))) (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc0)))) (equal (fn-ocfg-config oc) (fn-ocfg-config oc0)) (<= (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc0)))) (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))) (fn-captured-views-follow-ocfg views oc))
 :rule-classes nil
 :hints (("Goal" :induct (fn-captured-views-follow-ocfg views oc0)
          :in-theory '(fn-captured-views-follow-ocfg))
         ("Subgoal *1/1"
          :use ((:instance fn-k1-append-prefix-suffix (xs (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))) (ys (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                (:instance fn-k1-captured-view-transport-history-extension
                  (view (car views)) (extra (nthcdr (len (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))) (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))))
          :in-theory '(fn-captured-views-follow-ocfg))))
(local (defthm fn-k1-file-step-nonreserve-keeps-frontier
 (implies (not (fn-cstp-reserve-opp operation))
          (equal (fn-sf-frontier (fn-sn-file-step files operation result))
                 (fn-sf-frontier files)))
 :hints (("Goal" :in-theory
  (enable fn-cstp-reserve-opp fn-sn-file-step
          fn-sf-record-file-result fn-sf-record-link-result fn-sf-record-dir-result
          fn-sf-recovery-barrier)))))
(defthm fn-k1-file-step-frontier-monotone
 (implies (fn-sf-statep files)
          (<= (fn-sf-frontier files)
              (fn-sf-frontier (fn-sn-file-step files operation result))))
 :rule-classes nil
 :hints (("Goal"
  :cases ((fn-cstp-reserve-opp operation))
  :use (fn-cstp-reserve-file-step-cases fn-snt-typed-frontier-natural)
  :in-theory (union-theories '(fn-k1-file-step-nonreserve-keeps-frontier)
                              (theory 'minimal-theory)))))
(defthm fn-k1-sn-io-coherence-context
 (implies (fn-sn-statep s)
  (and (fn-sf-prefixp (fn-sf-records (fn-sn-files s))
                      (fn-sf-records (fn-sn-files (fn-sn-io s operation result))))
       (equal (fn-sn-config-history (fn-sn-io s operation result))
              (fn-sn-config-history s))
       (<= (fn-sf-frontier (fn-sn-files s))
           (fn-sf-frontier (fn-sn-files (fn-sn-io s operation result))))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-snt-io-records-prefix
        (:instance fn-k1-file-step-frontier-monotone (files (fn-sn-files s)))
        (:instance fn-cstp-sn-statep-files (st s)))
  :in-theory '(fn-cstp-io-fields))))
(local (defthm fn-k1-rcon-io-keeps-config
 (equal (fn-ocfg-config (fn-rcon-ocfg-io oc operation result)) (fn-ocfg-config oc))
 :hints (("Goal" :in-theory '(fn-lgoc-rcon-io-is-owner-with-store fn-ocfg-with-owner
                             fn-ocfg-config-of-fn-ocfg-make)))))
(defthm fn-k1-rcon-io-coherence-context
 (implies (fn-lgoc-invariantp oc) (and (fn-sf-prefixp (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner (fn-rcon-ocfg-io oc operation result)))))) (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner (fn-rcon-ocfg-io oc operation result)))) (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))) (equal (fn-ocfg-config (fn-rcon-ocfg-io oc operation result)) (fn-ocfg-config oc)) (<= (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) (fn-sf-frontier (fn-sn-files (fn-own-store (fn-ocfg-owner (fn-rcon-ocfg-io oc operation result))))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lgoc-invariant-statep)
                       (:instance fn-k1-sn-io-coherence-context (s (fn-own-store (fn-ocfg-owner oc)))))
          :in-theory '(fn-lgoc-store-of-rcon-io fn-k1-rcon-io-keeps-config))))
(defthm fn-k1-rcon-io-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc)
               (fn-psrv-io-safep operation))
          (fn-captured-views-follow-ocfg views (fn-rcon-ocfg-io oc operation result)))
 :rule-classes nil
 :hints (("Goal" :use (fn-k1-rcon-io-coherence-context
                       (:instance fn-k1-captured-views-transport-history-prefix
                         (oc0 oc) (oc (fn-rcon-ocfg-io oc operation result))))
          :in-theory '(fn-psrv-rcon-io-preserves-invariant))))
(defthm fn-k1-log-reserve-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (fn-olr-ocfg-reserve oc)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-k1-rcon-io-captured-views (oc oc) (operation :start-frontier) (result nil))
(:instance fn-k1-rcon-io-captured-views (oc (fn-rcon-ocfg-io oc :start-frontier nil)) (operation :frontier-file) (result :ok))
(:instance fn-k1-rcon-io-captured-views (oc (fn-rcon-ocfg-io (fn-rcon-ocfg-io oc :start-frontier nil) :frontier-file :ok)) (operation :frontier-replace) (result :ok))
(:instance fn-k1-rcon-io-captured-views (oc (fn-rcon-ocfg-io (fn-rcon-ocfg-io (fn-rcon-ocfg-io oc :start-frontier nil) :frontier-file :ok) :frontier-replace :ok)) (operation :frontier-directory) (result :ok)))
          :in-theory '(fn-olr-ocfg-reserve fn-psrv-rcon-io-preserves-invariant
                        fn-psrv-io-safep fn-cstp-reserve-opp member-equal
                        (:executable-counterpart equal) (:executable-counterpart member-equal)))))
(defthm fn-k1-log-order-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
          (fn-captured-views-follow-ocfg views (fn-olr-ocfg-order oc)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-k1-rcon-io-captured-views (oc oc) (operation :record-file) (result :ok))
(:instance fn-k1-rcon-io-captured-views (oc (fn-rcon-ocfg-io oc :record-file :ok)) (operation :record-link) (result :ok))
(:instance fn-k1-rcon-io-captured-views (oc (fn-rcon-ocfg-io (fn-rcon-ocfg-io oc :record-file :ok) :record-link :ok)) (operation :record-directory) (result :ok)))
          :in-theory '(fn-olr-ocfg-order fn-psrv-rcon-io-preserves-invariant
                        fn-psrv-io-safep fn-cstp-reserve-opp member-equal
                        (:executable-counterpart equal) (:executable-counterpart member-equal)))))
