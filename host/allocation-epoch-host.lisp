; Internal collector callback declarations. Raw dispatch preserves the carried
; allocation state; it neither installs that state nor authorizes measurements.
; The native public wrapper takes only a nonce and reads its fixed carrier.
(in-package "ACL2")
(include-book "../books/allocation-epoch-collection-request")
(include-book "../books/definterface")

(local
 (defthm fn-aech-collector-complete-keeps-installed-state
  (implies (and (fn-aec-statep i m e l a n g) (not (eq m :uninstalled)))
   (mv-let (word nm ne nl na ng)
    (fn-aec-collect-complete i m e l a n g oi oe og status ol)
    (declare (ignore word))
    (and (fn-aec-statep i nm ne nl na n ng)
         (not (eq nm :uninstalled)))))
  :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-at fn-aec-ceiling)))))

(local
 (defthm fn-aech-pool-uncertain-keeps-installed-state
  (implies (and (fn-aec-pool-statep pool) (not (eq (fn-prp-alloc-mode pool) :uninstalled)))
   (and (fn-aec-pool-statep (fn-aec-pool-uncertain-internal pool))
        (not (eq (fn-prp-alloc-mode (fn-aec-pool-uncertain-internal pool)) :uninstalled))))
  :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-at fn-aec-ceiling)))))

(local
 (defthm fn-aech-pool-issued-keeps-installed-state
  (implies (and (fn-aec-pool-statep pool) (not (eq (fn-prp-alloc-mode pool) :uninstalled)))
   (let ((next (mv-nth 1 (fn-aec-pool-collect-issued-internal issued pool))))
    (and (fn-aec-pool-statep next) (not (eq (fn-prp-alloc-mode next) :uninstalled)))))
  :hints (("Goal" :in-theory (disable fn-aec-installationp fn-aec-at fn-aec-ceiling)))))

(local
 (defthm fn-aech-pool-complete-keeps-installed-state
  (implies (and (fn-aec-pool-statep pool) (not (eq (fn-prp-alloc-mode pool) :uninstalled)))
   (let ((next (mv-nth 1 (fn-aec-pool-collect-complete-internal oi oe og status ol pool))))
    (and (fn-aec-pool-statep next) (not (eq (fn-prp-alloc-mode next) :uninstalled)))))
  :hints (("Goal" :in-theory (disable fn-aec-collect-complete fn-aec-statep)
   :use ((:instance fn-aech-collector-complete-keeps-installed-state
     (i (fn-prp-alloc-installation pool)) (m (fn-prp-alloc-mode pool))
     (e (fn-prp-alloc-epoch pool)) (l (fn-prp-alloc-occupied pool))
     (a (fn-prp-alloc-allocated pool)) (n (fn-prp-alloc-active-turns pool))
     (g (fn-prp-alloc-gc-nonce pool))))))))

(local
 (defthm fn-aech-pool-prepay-keeps-installed-state
  (implies (and (fn-aec-pool-statep pool) (not (eq (fn-prp-alloc-mode pool) :uninstalled)))
   (let ((next (mv-nth 1 (fn-aec-pool-collect-prepay-internal pool))))
    (and (fn-aec-pool-statep next) (not (eq (fn-prp-alloc-mode next) :uninstalled)))))
  :hints (("Goal" :in-theory (disable fn-aec-pool-collect-prepay-internal fn-aec-pool-statep)
           :use fn-aec-pool-prepay-preserves-installed-state))))

(local
 (defthm fn-aech-keep-ledger-keeps-installed-state
  (and (equal (fn-aec-pool-statep (fn-owner-page-read-keep-ledger ledger pool))
               (fn-aec-pool-statep pool))
       (equal (fn-prp-alloc-mode (fn-owner-page-read-keep-ledger ledger pool))
               (fn-prp-alloc-mode pool)))
  :hints (("Goal" :in-theory (disable fn-aec-statep)))))

(defthm fn-aech-request-preserves-carried-state
 (implies (and (fn-aec-pool-statep fn-page-read-pool)
               (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))
  (fn-aec-pool-statep
   (mv-nth 4 (fn-aec-pool-collection-request-internal fn-page-read-pool))))
 :hints (("Goal" :in-theory
  (disable fn-aec-pool-statep fn-aec-pool-collect-prepay-internal
           fn-aec-pool-collect-issued-internal fn-aec-pool-uncertain-internal
           fn-aec-collection-issue fn-owner-page-read-keep-ledger
           fn-prp-alloc-mode fn-prp-alloc-installation fn-prp-alloc-epoch fn-prp-alloc-gc-nonce
           fn-owner-page-read-ledger)))
 :rule-classes nil)

(defthm fn-aech-observed-preserves-carried-state
 (implies (and (fn-aec-pool-statep fn-page-read-pool)
               (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))
  (fn-aec-pool-statep
   (mv-nth 1 (fn-aec-pool-collect-observed-internal
              requested-nonce oi oe og status pages page-octets reservation fn-page-read-pool))))
 :hints (("Goal" :in-theory
  (disable fn-aec-pool-statep fn-aec-pool-collect-complete-internal
           fn-aec-pool-uncertain-internal fn-aec-observed-occupancy)))
 :rule-classes nil)

(defthm fn-aech-uncertain-preserves-carried-state
 (implies (and (fn-aec-pool-statep fn-page-read-pool)
               (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))
  (fn-aec-pool-statep (fn-aec-pool-uncertain-internal fn-page-read-pool)))
 :hints (("Goal" :in-theory (disable fn-aec-pool-statep fn-aec-pool-uncertain-internal)))
 :rule-classes nil)

(defthm fn-aech-request-preserves-existing-roots
 (let ((next (mv-nth 4 (fn-aec-pool-collection-request-internal pool))))
  (and (equal (fn-prp-alloc-installation next) (fn-prp-alloc-installation pool))
       (equal (fn-prp-alloc-epoch next) (fn-prp-alloc-epoch pool))
       (equal (fn-prp-alloc-occupied next) (fn-prp-alloc-occupied pool))
       (equal (fn-prp-alloc-active-turns next) (fn-prp-alloc-active-turns pool))
       (equal (fn-prp-mode next) (fn-prp-mode pool))
       (equal (fn-prp-incoming-slot next) (fn-prp-incoming-slot pool))))
 :hints (("Goal" :in-theory
  (disable nth update-nth fn-aec-collect-prepay fn-aec-collect-issued fn-aec-collection-issue)))
 :rule-classes nil)

(defthm fn-aech-observed-preserves-existing-roots
 (let ((next (mv-nth 1 (fn-aec-pool-collect-observed-internal
                        requested-nonce oi oe og status pages page-octets reservation pool))))
  (and (equal (fn-prp-alloc-installation next) (fn-prp-alloc-installation pool))
       (equal (fn-prp-data next) (fn-prp-data pool))
       (equal (fn-prp-alloc-active-turns next) (fn-prp-alloc-active-turns pool))
       (equal (fn-prp-mode next) (fn-prp-mode pool))
       (equal (fn-prp-incoming-slot next) (fn-prp-incoming-slot pool))))
 :hints (("Goal" :in-theory (disable nth update-nth fn-aec-observed-occupancy fn-aec-collect-complete)))
 :rule-classes nil)

(definterface fn-aec-pool-collection-request-internal
 :class :common-lisp-compliant
 :raw-with (fn-aech-request-preserves-carried-state fn-aech-request-preserves-existing-roots))

(definterface fn-aec-pool-collect-observed-internal
 :class :common-lisp-compliant
 :raw-with (fn-aech-observed-preserves-carried-state fn-aech-observed-preserves-existing-roots))

(definterface fn-aec-pool-uncertain-internal
 :class :common-lisp-compliant
 :raw-with (fn-aech-uncertain-preserves-carried-state fn-aec-pool-uncertainty-retains-charge-and-identities))
