; Fixed-arity INTERNAL observation projection. The public native wrapper takes
; only a nonce and reads its installed preallocated collector carrier. These
; raw fields are not public request inputs and cannot install geometry.
(in-package "ACL2")
(include-book "allocation-epoch-pool")

(defun fn-aec-observed-occupancy (installation oi pages page-octets reservation)
 (declare (xargs :guard (fn-aec-installationp installation)))
 (let ((association (fn-aec-at 1 installation))
       (domain (fn-aec-at 2 installation)))
  (if (and (equal oi association)
           (equal page-octets (fn-aec-at 4 association))
           (equal reservation (fn-aec-at 5 association))
           (natp pages) (posp page-octets) (natp reservation)
           (<= reservation domain)
           (<= pages (floor reservation page-octets)))
      ;; Divide the installed bounded reservation BEFORE multiplying. Thus
      ;; even rejected observations cannot construct an oversized product.
      (mv :observed (* pages page-octets))
    (mv :invalid-observation 0))))

(defun fn-aec-pool-collect-observed-internal
 (requested-nonce oi oe og status pages page-octets reservation fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool
  :guard (and (fn-aec-pool-statep fn-page-read-pool)
              (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))))
 (if (not (and (equal requested-nonce (fn-prp-alloc-gc-nonce fn-page-read-pool))
               (eq status :completed)))
     (let ((fn-page-read-pool (fn-aec-pool-uncertain-internal fn-page-read-pool)))
      (mv :recovery-required fn-page-read-pool))
   (mv-let (word occupied)
    (fn-aec-observed-occupancy (fn-prp-alloc-installation fn-page-read-pool)
                              oi pages page-octets reservation)
    (if (eq word :observed)
        (fn-aec-pool-collect-complete-internal oi oe og status occupied fn-page-read-pool)
      (let ((fn-page-read-pool (fn-aec-pool-uncertain-internal fn-page-read-pool)))
       (mv :recovery-required fn-page-read-pool))))))

(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (local
  (defthm fn-aec-observation-product-bound
   (implies (and (natp pages) (natp reservation) (posp page-octets)
                 (<= pages (floor reservation page-octets)))
            (<= (* pages page-octets) reservation))
   :hints (("Goal" :nonlinearp t)) :rule-classes nil))
 (defthm fn-aec-observed-occupancy-binds-installed-geometry
  (implies (eq (mv-nth 0 (fn-aec-observed-occupancy i oi pages page-octets reservation)) :observed)
   (let ((occupied (mv-nth 1 (fn-aec-observed-occupancy i oi pages page-octets reservation))))
    (and (equal oi (fn-aec-at 1 i))
         (equal page-octets (fn-aec-at 4 (fn-aec-at 1 i)))
         (equal reservation (fn-aec-at 5 (fn-aec-at 1 i)))
         (natp occupied) (<= occupied reservation)
         (<= occupied (fn-aec-at 2 i))
         (equal occupied (* pages page-octets)))))
  :hints (("Goal"
   :in-theory (set-difference-theories
                (current-theory 'fn-aec-pool-collect-observed-internal) '(fn-aec-at))
   :use ((:instance fn-aec-observation-product-bound))))
  :rule-classes nil))

(defthm fn-aec-request-nonce-mismatch-retains-accounting
 (implies (not (equal requested-nonce (fn-prp-alloc-gc-nonce pool)))
  (equal (mv-nth 1 (fn-aec-pool-collect-observed-internal
                    requested-nonce oi oe og status pages page-octets reservation pool))
         (fn-aec-pool-uncertain-internal pool)))
 :hints (("Goal" :in-theory (disable fn-aec-pool-uncertain-internal)))
 :rule-classes nil)
