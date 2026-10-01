; WIP actual shallow-remap boundary. No runtime predicate or new decoder.
(in-package "ACL2")
(include-book "history-cold-record-cursor")
(include-book "snapshot-decode-remap")

(local
 (defthm fn-rccd-put-keeps-abstract-spine-length
  (implies (and (natp n) (fn-odm-prefixp (1+ n) node))
   (equal (len (fn-hdc-abstract (fn-odm-put n value node) pool))
          (len (fn-hdc-abstract node pool))))
  :hints (("Goal" :induct (fn-odm-put n value node)
   :in-theory (enable fn-odm-put fn-odm-prefixp fn-odm-pairp
                      fn-hdc-pair fn-hdc-car fn-hdc-cdr fn-hdc-abstract)))))

(local
 (defthm fn-rccd-put-keeps-decoded-octet-domain
  (implies (and (natp n) (fn-odm-prefixp (1+ n) node)
                (fn-hrcur-dos-domainp node pool)
                (fn-hrcur-dos-domainp value pool))
   (fn-hrcur-dos-domainp (fn-odm-put n value node) pool))
  :hints (("Goal" :induct (fn-odm-put n value node)
   :in-theory (enable fn-odm-put fn-odm-prefixp fn-odm-pairp
                      fn-hdc-pair fn-hdc-car fn-hdc-cdr
                      fn-hrcur-dos-domainp fn-hrcur-field fn-hrcur-widthp)))))

(local
 (defthm fn-rccd-cold-domain-has-decoded-octet-domain
  (implies (fn-hrcur-cold-domainp node pool)
   (fn-hrcur-dos-domainp node pool))
  :hints (("Goal" :expand ((fn-hrcur-cold-domainp node pool))))))

(local
 (defthm fn-rccd-cold-domain-has-spine-bound
  (implies (fn-hrcur-cold-domainp node pool)
   (< (len (fn-hdc-abstract node pool)) *fn-hrcur-u64-bound*))
  :hints (("Goal" :expand ((fn-hrcur-cold-domainp node pool))))))

(defthm fn-rccd-actual-put-preserves-cold-codec-domain
 (implies (and (natp n) (fn-odm-prefixp (1+ n) node)
               (fn-hrcur-cold-domainp node pool)
               (fn-hrcur-cold-domainp value pool))
  (fn-hrcur-cold-domainp (fn-odm-put n value node) pool))
 :hints (("Goal" :induct (fn-odm-put n value node)
  :in-theory (e/d (fn-odm-put fn-odm-prefixp fn-odm-pairp
                   fn-hdc-pair fn-hdc-car fn-hdc-cdr
                   fn-hrcur-cold-domainp fn-hrcur-field fn-hrcur-widthp)
                  (fn-hrcur-dos-domainp fn-hdc-abstract)))
 ("Subgoal *1/2" :use ((:instance fn-rccd-put-keeps-abstract-spine-length)
                      (:instance fn-rccd-put-keeps-decoded-octet-domain)))
 ("Subgoal *1/1" :use ((:instance fn-rccd-put-keeps-abstract-spine-length)
                      (:instance fn-rccd-put-keeps-decoded-octet-domain)))))

(defthm fn-rccd-actual-held-remap-preserves-cold-codec-domain
 (implies (and (fn-odm-prefixp 5 node)
               (fn-hrcur-cold-domainp node pool)
               (fn-hrcur-cold-domainp (fn-hdc-atom handle) pool))
  (fn-hrcur-cold-domainp (fn-odm-held node handle) pool))
 :hints (("Goal" :use ((:instance fn-rccd-actual-put-preserves-cold-codec-domain
                        (n 4) (value (fn-hdc-atom handle))))
  :in-theory (enable fn-odm-held))))

(local
 (defthm fn-rccd-selected-prefix-child-has-cold-domain
  (implies (and (natp n) (fn-odm-prefixp (1+ n) node)
                (fn-hrcur-cold-domainp node pool))
   (fn-hrcur-cold-domainp (fn-odm-at n node) pool))
  :hints (("Goal" :induct (fn-odm-at n node)
   :in-theory (enable fn-odm-at fn-odm-prefixp fn-odm-pairp
                      fn-hdc-car fn-hdc-cdr fn-hrcur-cold-domainp
                      fn-hrcur-field fn-hrcur-widthp)))))

(defthm fn-rccd-actual-composite-remap-preserves-cold-codec-domain
 (implies (and (fn-odm-prefixp 3 node)
               (fn-odm-prefixp 5 (fn-odm-at 2 node))
               (fn-hrcur-cold-domainp node pool)
               (fn-hrcur-cold-domainp (fn-hdc-atom handle) pool))
  (fn-hrcur-cold-domainp (fn-odm-composite node handle) pool))
 :hints (("Goal"
  :use ((:instance fn-rccd-selected-prefix-child-has-cold-domain (n 2))
        (:instance fn-rccd-actual-held-remap-preserves-cold-codec-domain
                   (node (fn-odm-at 2 node)))
        (:instance fn-rccd-actual-put-preserves-cold-codec-domain
                   (n 2) (value (fn-odm-held (fn-odm-at 2 node) handle))))
  :in-theory (e/d (fn-odm-composite)
                 (fn-odm-put fn-odm-held fn-hrcur-cold-domainp)))))
