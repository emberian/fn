; Same-store owner replacement preserves every live retained conjunct.
; No captured-view premise added: store equality and both relations imply it.
(in-package "ACL2")
(include-book "owner-retain-livep")
(include-book "owner-retain-captured-frames")
(local (defthm fn-k1-config-equal-from-same-store
  (implies (and (fn-lgoc-invariantp oc0) (fn-lgoc-invariantp oc)
                (equal (fn-own-store (fn-ocfg-owner oc)) (fn-own-store (fn-ocfg-owner oc0))))
           (equal (fn-ocfg-config oc) (fn-ocfg-config oc0)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-lgoc-invariantp fn-ocl-relation fn-ocl-config-historyp)))))
(defthm fn-k1-captured-views-follow-same-store
  (implies (and (fn-lgoc-invariantp oc0) (fn-lgoc-invariantp oc)
                (fn-captured-views-follow-ocfg views oc0)
                (equal (fn-own-store (fn-ocfg-owner oc)) (fn-own-store (fn-ocfg-owner oc0))))
           (fn-captured-views-follow-ocfg views oc))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-k1-config-equal-from-same-store)
                         (:instance fn-k1-captured-views-transport-same-history))
           :in-theory nil)))
(defthm fn-k1-same-store-install-preserves-livep
   (implies (and (fn-owner-retain-livep state fn-arena)
                 (fn-lgoc-invariantp oc)
                 (equal (fn-sbud-oc-store oc) (fn-owner-store state)))
            (fn-owner-retain-livep (fn-owner-install-ocfg oc state) fn-arena))
   :rule-classes nil
   :hints (("Goal"
    :use ((:instance fn-k1-captured-views-follow-same-store
            (oc0 (fn-owner-ocfg state)) (views (fn-owner-reader-views state))))
    :in-theory '(fn-owner-retain-livep fn-owner-retain-statep
                 fn-owner-captured-view-follows-store fn-sbud-oc-store
                 fn-owner-store-is-configured-store-by-definition
                 fn-owner-bound-of-install-ocfg fn-owner-ocfg-of-install-ocfg
                 fn-owner-retain-carry-of-install-ocfg
                 fn-owner-reader-views-of-install-ocfg))))
