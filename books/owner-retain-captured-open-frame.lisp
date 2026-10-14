; Whole returned-state preservation through captured-reader open and working-view restore.
(in-package "ACL2")
(include-book "owner-retain-live")
(local (include-book "owner-retain-captured-live-frame"))
(local (defthm fn-k1-open-keeps-config
 (equal (fn-ocfg-config (cdr (fn-ocfg-open oc acfg))) (fn-ocfg-config oc))
 :hints (("Goal" :in-theory '(fn-ocfg-open fn-ocfg-config-of-fn-ocfg-make car-cons cdr-cons)))))
(local (defthm fn-k1-reader-selection-preserves-lgoc
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
  (fn-lgoc-invariantp (fn-ocfg-at-reader-view oc views)))
 :rule-classes nil
 :hints (("Goal" :in-theory '(fn-lgoc-invariantp fn-ocfg-at-reader-view fn-ocv-reader-view
                              fn-captured-views-follow-ocfg fn-captured-view-follows-ocfg
                              fn-ocfg-with-view-keeps-the-rest)))))
(local (defthm fn-k1-reader-selection-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
  (fn-captured-views-follow-ocfg views (fn-ocfg-at-reader-view oc views)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-k1-captured-views-transport-same-history
          (oc0 oc) (oc (fn-ocfg-at-reader-view oc views)))
        (:instance fn-k1-reader-selection-preserves-lgoc))
  :in-theory '(fn-ocfg-at-reader-view fn-ocv-reader-view fn-ocfg-with-view-keeps-the-rest)))))
(local (defthm fn-k1-ocar-open-preserves-lgoc
 (implies (fn-lgoc-invariantp oc)
  (fn-lgoc-invariantp (cdr (fn-ocar-ocfg-open oc acfg))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-ocl-open-preserves-historical-relation))
          :in-theory '(fn-lgoc-invariantp fn-ocar-ocfg-open-is-ocfg-open-under-ocl-relation
                       fn-ocar-ocfg-open-keeps-store fn-ocl-open-keeps-store-and-view)))))
(local (defthm fn-k1-ocar-open-captured-views
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
  (fn-captured-views-follow-ocfg views (cdr (fn-ocar-ocfg-open oc acfg))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-k1-captured-views-transport-same-history
          (oc0 oc) (oc (cdr (fn-ocar-ocfg-open oc acfg))))
        (:instance fn-k1-ocar-open-preserves-lgoc))
  :in-theory '(fn-lgoc-invariantp fn-ocar-ocfg-open-is-ocfg-open-under-ocl-relation
               fn-ocar-ocfg-open-keeps-store fn-ocl-open-keeps-store-and-view fn-k1-open-keeps-config)))))
(local (defthm fn-k1-open-config-equal-from-same-store
 (implies (and (fn-lgoc-invariantp oc0) (fn-lgoc-invariantp oc)
               (equal (fn-own-store (fn-ocfg-owner oc)) (fn-own-store (fn-ocfg-owner oc0))))
  (equal (fn-ocfg-config oc) (fn-ocfg-config oc0)))
 :rule-classes nil
 :hints (("Goal" :in-theory '(fn-lgoc-invariantp fn-ocl-relation fn-ocl-config-historyp)))))
(local (defthm fn-k1-open-true-list-fix
 (implies (true-listp xs) (equal (true-list-fix xs) xs))
 :hints (("Goal" :induct (true-listp xs) :in-theory '(true-listp true-list-fix car-cdr-elim)))))
(local (defthm fn-k1-working-view-restores-lgoc
 (implies (and (fn-lgoc-invariantp oc0) (fn-lgoc-invariantp oc)
               (equal (fn-own-store (fn-ocfg-owner oc)) (fn-own-store (fn-ocfg-owner oc0))))
  (fn-lgoc-invariantp (fn-ocfg-with-view oc (fn-own-view (fn-ocfg-owner oc0)))))
 :rule-classes nil
 :hints (("Goal"
 :use ((:instance fn-k1-open-config-equal-from-same-store)
       (:instance fn-ocl-relation-of-a-view-captured-before-appends (extra nil))
       (:instance fn-lgoc-invariant-statep (oc oc0))
       (:instance fn-cstp-sn-statep-files (st (fn-own-store (fn-ocfg-owner oc0))))
       (:instance fn-sf-state-records-are-true-list (s (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))))
 :in-theory '(fn-lgoc-invariantp fn-ocfg-with-view-keeps-the-rest fn-lgt-append-nil fn-k1-open-true-list-fix)))))
(local (defthm fn-k1-open-reader-and-restore-context
 (implies (and (fn-lgoc-invariantp oc) (fn-captured-views-follow-ocfg views oc))
  (let* ((selected (fn-ocfg-at-reader-view oc views))
         (opened (cdr (fn-ocar-ocfg-open selected acfg)))
         (restored (if (consp views) (fn-ocfg-with-view opened (fn-own-view (fn-ocfg-owner oc))) opened)))
   (and (fn-lgoc-invariantp restored)
        (equal (fn-own-store (fn-ocfg-owner restored)) (fn-own-store (fn-ocfg-owner oc)))
        (fn-captured-views-follow-ocfg views restored))))
 :rule-classes nil
 :hints (("Goal" :cases ((consp views))
 :use ((:instance fn-k1-reader-selection-preserves-lgoc)
       (:instance fn-k1-ocar-open-preserves-lgoc (oc (fn-ocfg-at-reader-view oc views)))
       (:instance fn-k1-working-view-restores-lgoc (oc0 oc) (oc (cdr (fn-ocar-ocfg-open (fn-ocfg-at-reader-view oc views) acfg))))
       (:instance fn-k1-captured-views-follow-same-store (oc0 oc)
         (oc (if (consp views) (fn-ocfg-with-view (cdr (fn-ocar-ocfg-open (fn-ocfg-at-reader-view oc views) acfg)) (fn-own-view (fn-ocfg-owner oc)))
                (cdr (fn-ocar-ocfg-open (fn-ocfg-at-reader-view oc views) acfg))))))
 :in-theory '(fn-ocfg-at-reader-view fn-ocv-reader-view fn-ocfg-with-view-keeps-the-rest fn-ocar-ocfg-open-keeps-store)))))
(local (defthm fn-k1-open-whole-state-projections
 (let* ((next (mv-nth 2 (fn-owner-open state)))
        (oc (fn-owner-ocfg state)) (views (fn-owner-reader-views state))
        (selected (fn-ocfg-at-reader-view oc views))
        (opened (cdr (fn-ocar-ocfg-open selected (fn-owner-auth (fn-owner-callback-at-reader-view state)))))
        (restored (if (consp views) (fn-ocfg-with-view opened (fn-own-view (fn-ocfg-owner oc))) opened)))
  (and (equal (fn-owner-ocfg next) restored)
       (equal (fn-owner-reader-views next) views)
       (equal (fn-owner-retain-carry next) (fn-owner-retain-carry state))
       (boundp-global 'fn-owner next)))
 :hints (("Goal"
 :in-theory '(fn-owner-open fn-owner-callback-open fn-owner-callback-at-reader-view
              fn-owner-callback-at-working-view fn-owner-callback-open-at
              fn-owner-callback-install-effects fn-owner-install-served-effects
              fn-owner-core-is-configured-owner-by-definition
              fn-owner-ocfg-of-install-ocfg fn-owner-ocfg-of-other-global-put
              fn-owner-reader-views-of-install-ocfg fn-owner-reader-views-of-other-global-put
              fn-owner-retain-carry-of-install-ocfg fn-owner-retain-carry-of-other-global-put
              fn-owner-bound-of-install-ocfg fn-owner-bound-of-other-global-put
              fn-ocfg-at-reader-view fn-ocv-reader-view
              mv-nth nth zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--))))))
(defthm fn-owner-retain-open-keeps-retained-state
 (implies (fn-owner-retain-retained-statep state)
          (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-open state))))
 :rule-classes nil
 :hints (("Goal"
 :use ((:instance fn-k1-open-reader-and-restore-context
         (oc (fn-owner-ocfg state)) (views (fn-owner-reader-views state))
         (acfg (fn-owner-auth (fn-owner-callback-at-reader-view state)))))
 :in-theory '(fn-owner-retain-retained-statep fn-owner-retain-statep
              fn-owner-captured-view-follows-store
              fn-owner-store-is-configured-store-by-definition fn-k1-open-whole-state-projections))))
(defthm fn-owner-retain-open-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-open state)) fn-arena))
  :hints (("Goal"
    :use ((:instance fn-k1-open-reader-and-restore-context
            (oc (fn-owner-ocfg state)) (views (fn-owner-reader-views state))
            (acfg (fn-owner-auth (fn-owner-callback-at-reader-view state)))))
    :in-theory '(fn-owner-retain-livep fn-owner-retain-statep
                 fn-owner-captured-view-follows-store
                 fn-owner-store-is-configured-store-by-definition
                 fn-k1-open-whole-state-projections))))
