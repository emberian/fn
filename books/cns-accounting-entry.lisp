; Actual initializer entry for the counted CNS accounting hypotheses.
; Native pool geometry is reused; no executor/reference world is imported.
(in-package "ACL2")
(include-book "pool-initialization")
(include-book "machine-reservations-entry")

(make-event
 (value (cons 'progn (fn2-core-init-projection-events 'fn2-core-pool (w state)))))

(defthm fn2-cns-core-init-pool-accounting-entry
  (implies (and (fn2-corep core) (fn2-core-profilep profile))
    (fn2-pool-semanticp (fn2-core-pool (fn2-core-init profile core))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-pool-init-semantic
                            (p (fn2-core-pool core))
                            (classes (fn2-profile-pool-classes profile))
                            (gen-start (fn2-profile-generation-start profile))
                            (gen-limit (fn2-profile-generation-limit profile)))
                 init-fn2-core-pool-profile
                 (:instance fn2-core-pool-type (fn2-core core))
                 fn2-profile-generation-bounds)
           :in-theory (disable fn2-core-init fn2-pool-init fn2-core-pool
                               fn2-corep fn2-core-profilep fn2-profilep
                               fn2-pool-semanticp fn2-pool-profilep))))

; Initialization establishes accounting; admission establishes a live row.
; This statement deliberately does not assert the draining domain at entry.
(defthm fn2-cns-core-init-accounting-entry
  (implies (and (fn2-corep core) (fn2-core-profilep profile))
    (let ((after (fn2-core-init profile core)))
      (and (fn2-corep after) (fn2-core-wfp after)
           (fn2-pool-semanticp (fn2-core-pool after))
           (fn2-machines-partition-reservedp
             *fn2-cns-admission-ordinal* (fn2-core-machines after)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-core-init-pool-accounting-entry
                 (:instance fn2-core-init-partition-reservation-entry
                            (ord *fn2-cns-admission-ordinal*)))
           :in-theory (disable fn2-core-init fn2-core-profilep
                               fn2-pool-semanticp fn2-machines-partition-reservedp))))
