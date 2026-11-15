; Sequential release accounting and distinct-row admission.
; Kept after the complete native release refinement, not on its proof path.
(in-package "ACL2")
(include-book "cns-release-refinement")
(include-book "pool-release-admission")

(defthm fn2-cns-semantic-pool-type-by-definition
  (implies (fn2-pool-semanticp pool)
           (and (fn2-poolp pool) (fn2-pool-wfp pool)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory
           (e/d (fn2-pool-semanticp)
                (fn2-poolp fn2-pool-wfp fn2-pool-row-invariantp
                 fn2-pool-class-accountsp fn2-pool-retired-slots
                 fn2-pool-nslots fn2-pool-capacity-bytes)))))

(defthm fn2-cns-owned-pool-release-pool-effect
  (implies (and (fn2-poolp pool) (fn2-pool-wfp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool))
    (equal (mv-nth 1 (fn2-pool-release slot gen *fn2-cns-kind* id ogen pool))
           (fn2-cns-drain-release-pool-effect slot pool)))
  :rule-classes nil
  :hints (("Goal" :use fn2-cns-owned-pool-release-independent
           :in-theory (e/d (fn2-cns-owned-pool-release-expected)
                            (fn2-pool-release fn2-cns-drain-release-pool-effect)))))

(defthm fn2-cns-distinct-releasable-after-pool-release
  (implies (and (fn2-pool-semanticp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool)
                (fn2-cns-drain-releasablep other other-gen id ogen pool)
                (not (equal other slot)))
    (fn2-cns-drain-releasablep other other-gen id ogen
      (mv-nth 1 (fn2-pool-release slot gen *fn2-cns-kind* id ogen pool))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-owned-pool-release-pool-effect
                 (:instance fn2-pool-distinct-workspace-admits-release-after-release
                            (okind *fn2-cns-kind*) (oslot id)))
           :in-theory
           (union-theories
            (theory 'fn2-cns-pool-readers)
            (e/d (fn2-cns-drain-releasablep fn2-cns-drain-release-pool-effect
                  fn2-cns-drain-put-cells fn2-cns-drain-put-cell fn2-cns-drain-put
                  fn2-cns-drain-cell fn2-cns-drain-get fn2-cns-drain-index
                  fn2-pool-release-countp fn2-pool-logical-slotp fn2-pool-nslots
                  fn2-pool-rows fn2-pool-nclasses fn2-pool-gen-limit
                  fn2-pool-retired-count fn2-pool-class-headsi fn2-pool-class-countsi)
                 (fn2-pool-release fn2-pool-semanticp fn2-poolp fn2-pool-wfp))))))

(defthm fn2-cns-independent-release-preserves-pool-accounting
  (implies (and (fn2-pool-semanticp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool))
    (fn2-pool-semanticp (fn2-cns-drain-release-pool-effect slot pool)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-owned-pool-release-pool-effect
                 (:instance fn2-pool-release-conservation
                            (fn2-pool pool) (okind *fn2-cns-kind*) (oslot id)))
           :in-theory (disable fn2-pool-semanticp fn2-pool-release
                               fn2-cns-drain-releasablep fn2-cns-drain-release-pool-effect))))

(defthm fn2-cns-independent-release-keeps-second-releasable
  (implies (and (fn2-pool-semanticp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool)
                (fn2-cns-drain-releasablep other other-gen id ogen pool)
                (not (equal other slot)))
    (fn2-cns-drain-releasablep other other-gen id ogen
      (fn2-cns-drain-release-pool-effect slot pool)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-distinct-releasable-after-pool-release
                 fn2-cns-owned-pool-release-pool-effect)
           :in-theory (disable fn2-pool-semanticp fn2-pool-release
                               fn2-cns-drain-releasablep fn2-cns-drain-release-pool-effect))))

(defthm fn2-cns-owned-core-release-pool-effect
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-drain-releasablep slot gen id ogen (fn2-core-pool core)))
    (equal
     (fn2-core-pool (mv-nth 1 (fn2-core-release slot gen *fn2-cns-kind* id ogen core)))
     (fn2-cns-drain-release-pool-effect slot (fn2-core-pool core))))
  :rule-classes nil
  :hints (("Goal" :use fn2-cns-core-release-independent
           :in-theory
           (e/d (fn2-cns-core-release-expected fn2-cns-owned-pool-release-expected)
                (fn2-core-release fn2-core-pool fn2-cns-drain-release-pool-effect)))))

(defthm fn2-cns-owned-core-release-pool-accounting
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-pool-semanticp (fn2-core-pool core))
                (fn2-cns-drain-releasablep slot gen id ogen (fn2-core-pool core)))
    (fn2-pool-semanticp
      (fn2-core-pool (mv-nth 1 (fn2-core-release slot gen *fn2-cns-kind* id ogen core)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-owned-core-release-pool-effect
                 (:instance fn2-cns-independent-release-preserves-pool-accounting
                            (pool (fn2-core-pool core))))
           :in-theory (disable fn2-core-release fn2-core-pool fn2-pool-semanticp
                               fn2-cns-drain-releasablep fn2-cns-drain-release-pool-effect))))

(defthm fn2-cns-distinct-releasable-after-core-release
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-pool-semanticp (fn2-core-pool core))
                (fn2-cns-drain-releasablep slot gen id ogen (fn2-core-pool core))
                (fn2-cns-drain-releasablep other other-gen id ogen (fn2-core-pool core))
                (not (equal other slot)))
    (fn2-cns-drain-releasablep other other-gen id ogen
      (fn2-core-pool (mv-nth 1 (fn2-core-release slot gen *fn2-cns-kind* id ogen core)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-owned-core-release-pool-effect
                 (:instance fn2-cns-distinct-releasable-after-pool-release
                            (pool (fn2-core-pool core)))
                 (:instance fn2-cns-owned-pool-release-pool-effect
                            (pool (fn2-core-pool core))))
           :in-theory (disable fn2-core-release fn2-pool-release
                               fn2-cns-drain-releasablep fn2-cns-drain-release-pool-effect))))
