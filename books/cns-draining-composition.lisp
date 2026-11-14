; Independent application effects lifted through the actual served core
; faces. The original counted CNS obligation keeps its full antecedent.
(in-package "ACL2")
(include-book "cns-pool-refinement")
(include-book "core-product-lowering")

; Consume the shared reconstruction laws for the two actual written core
; children. No duplicate core shape or writeback implementation is needed.
(make-event
 (let* ((world (w state))
        (selected (fn2-product-entries (fn2-core-child-registry world)
                                      '(fn2-core-pool fn2-core-control) world)))
   (value (cons 'progn
     (append (fn2-product-core-shape-events world)
             (fn2-product-writeback-facts selected selected world)
             (fn2-product-spine-facts selected world))))))

(defthm fn2-cns-owned-release-admission-by-definition
  (implies (and (fn2-poolp pool) (fn2-pool-wfp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool))
           (fn2-pool-release-countp slot pool))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'fn2-cns-pool-readers)
            (e/d (fn2-pool-release-countp fn2-pool-rows fn2-pool-nclasses
                  fn2-pool-retired-count fn2-pool-class-countsi
                  fn2-cns-drain-releasablep fn2-cns-drain-cell
                  fn2-cns-drain-get fn2-cns-drain-index)
                 (fn2-poolp fn2-pool-wfp))))))

(defun fn2-cns-release-children-expected (slot gen kind id ogen pool control)
  (let ((out (fn2-cns-owned-pool-release-expected slot gen kind id ogen pool)))
    (list (car out) (cadr out) control)))
(defthm fn2-cns-core-release-children-independent
  (implies (and (fn2-poolp pool) (fn2-pool-wfp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool))
    (equal
     (fn2-core-release-children slot gen *fn2-cns-kind* id ogen pool control)
     (fn2-cns-release-children-expected slot gen *fn2-cns-kind* id ogen pool control)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-owned-release-admission-by-definition
                 fn2-cns-owned-pool-release-independent)
           :in-theory
           (e/d (fn2-core-release-children fn2-cns-release-children-expected
                 fn2-cns-owned-pool-release-expected)
                (fn2-pool-release fn2-pool-release-countp fn2-poolp fn2-pool-wfp
                 fn2-cns-drain-releasablep fn2-cns-drain-released-pool
                 fn2-cns-drain-cell fn2-cns-drain-get fn2-control-record-stop)))))

(defun fn2-cns-core-release-expected (slot gen kind id ogen before)
  (let ((out (fn2-cns-owned-pool-release-expected slot gen kind id ogen
               (fn2-cns-drain-child 'fn2-pool before))))
    (list (car out) (fn2-cns-drain-put-child 'fn2-pool (cadr out) before))))

(defthm fn2-cns-pool-child-by-definition
  (equal (fn2-cns-drain-child 'fn2-pool core) (fn2-core-pool core))
  :hints (("Goal" :in-theory
           (enable fn2-cns-drain-child fn2-cns-drain-child-index fn2-core-pool))))
(defthm fn2-cns-pool-put-child-by-definition
  (equal (fn2-cns-drain-put-child 'fn2-pool pool core)
         (update-fn2-core-pool pool core))
  :hints (("Goal" :in-theory
           (enable fn2-cns-drain-put-child fn2-cns-drain-child-index update-fn2-core-pool))))

(defthm fn2-cns-core-release-independent
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-drain-releasablep slot gen id ogen (fn2-core-pool core)))
    (equal (fn2-core-release slot gen *fn2-cns-kind* id ogen core)
           (fn2-cns-core-release-expected slot gen *fn2-cns-kind* id ogen core)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-cns-core-release-children-independent
                            (pool (fn2-core-pool core))
                            (control (fn2-core-control core)))
                 (:instance fn2-product-core-shape (fn2-core core)))
           :in-theory
           (e/d (fn2-core-release fn2-cns-core-release-expected
                 fn2-cns-release-children-expected)
                (fn2-core-release-children fn2-core-pool fn2-core-control
                 update-fn2-core-pool update-fn2-core-control
                 fn2-cns-drain-releasablep fn2-cns-owned-pool-release-expected
                 fn2-corep fn2-core-wfp)))))

(defthm fn2-cns-release-ns-independent-by-definition
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-drain-releasablep slot gen id ogen (fn2-core-pool core)))
    (equal (fn2-cns-release-ns slot gen *fn2-cns-kind* id ogen core)
           (fn2-cns-core-release-expected slot gen *fn2-cns-kind* id ogen core)))
  :rule-classes nil
  :hints (("Goal" :use fn2-cns-core-release-independent
           :in-theory (e/d (fn2-cns-release-ns) (fn2-core-release)))))
(defthm fn2-cns-lease-release-is-core-release-by-definition
  (equal (fn2-cns-lease-release slot gen kind id ogen core)
         (fn2-core-release slot gen kind id ogen core))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn2-cns-lease-release fn2-core-release)
                (fn2-core-release-children fn2-core-pool fn2-core-control
                 update-fn2-core-pool update-fn2-core-control)))))

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
           (fn2-cns-drain-released-pool slot pool)))
  :rule-classes nil
  :hints (("Goal" :use fn2-cns-owned-pool-release-independent
           :in-theory (e/d (fn2-cns-owned-pool-release-expected)
                            (fn2-pool-release fn2-cns-drain-released-pool)))))

; Initial local count bounds alone do not fund both releases. This bridge
; consumes maintained semantic accounting, conservation, and distinct-row
; preservation to establish the second release's actual admission guard.
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
            (e/d (fn2-cns-drain-releasablep fn2-cns-drain-released-pool
                  fn2-cns-drain-put-cells fn2-cns-drain-put-cell fn2-cns-drain-put
                  fn2-cns-drain-cell fn2-cns-drain-get fn2-cns-drain-index
                  fn2-pool-release-countp fn2-pool-logical-slotp fn2-pool-nslots
                  fn2-pool-rows fn2-pool-nclasses fn2-pool-gen-limit
                  fn2-pool-retired-count fn2-pool-class-headsi fn2-pool-class-countsi)
                 (fn2-pool-release fn2-pool-semanticp fn2-poolp fn2-pool-wfp))))))

(defthm fn2-cns-owned-core-release-pool-effect
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-drain-releasablep slot gen id ogen (fn2-core-pool core)))
    (equal
     (fn2-core-pool (mv-nth 1 (fn2-core-release slot gen *fn2-cns-kind* id ogen core)))
     (fn2-cns-drain-released-pool slot (fn2-core-pool core))))
  :rule-classes nil
  :hints (("Goal" :use fn2-cns-core-release-independent
           :in-theory
           (e/d (fn2-cns-core-release-expected fn2-cns-owned-pool-release-expected)
                (fn2-core-release fn2-core-pool fn2-cns-drain-released-pool)))))
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
                               fn2-cns-drain-releasablep fn2-cns-drain-released-pool))))
