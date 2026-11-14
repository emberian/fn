; Independent application effects lifted through the actual served core
; faces. The original counted CNS obligation keeps its full antecedent.
(in-package "ACL2")
(include-book "cns-pool-refinement")
(include-book "core-product-lowering")
(include-book "cns-accounting-entry")

; Consume the shared reconstruction laws for the actual written core
; children. No duplicate core shape or writeback implementation is needed.
(make-event
 (let* ((world (w state))
        (selected (fn2-product-entries (fn2-core-child-registry world)
                                      '(fn2-core-pool fn2-core-control fn2-core-machines) world)))
   (value (cons 'progn
     (append (fn2-product-core-shape-events world)
             (fn2-product-writeback-facts selected selected world)
             (fn2-product-spine-facts selected world))))))

(defthm fn2-cns-reservation-native-by-definition
  (equal (fn2-cns-draining-reservedp core)
         (fn2-machines-partition-reservedp *fn2-cns-admission-ordinal*
                                         (fn2-core-machines core)))
  :hints (("Goal" :in-theory
           (enable fn2-cns-draining-reservedp fn2-cns-drain-child
             fn2-cns-drain-child-index fn2-cns-drain-cell fn2-cns-drain-get
             fn2-cns-drain-index fn2-machines-partition-reservedp
             fn2-machines-reservation-valuesp fn2-machines-reservation-view
             fn2-machines-active-counti fn2-machines-admission-creditsi
             fn2-machines-connection-counti fn2-core-machines))))
(defthm fn2-cns-core-init-reservation-entry
  (fn2-cns-draining-reservedp (fn2-core-init profile core))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-core-init-partition-reservation-entry
                                   (ord *fn2-cns-admission-ordinal*)))
           :in-theory (disable fn2-core-init fn2-cns-draining-reservedp
                               fn2-machines-partition-reservedp))))

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

(defun fn2-cns-core-model-projection-events (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) nil
    (let* ((field (caar entries))
           (child (fn2-core-child-property (car entries) :stobj))
           (writer (fn2-product-writer field)))
      (append
       `((defthm ,(fn2-columns-sym field "-CNS-MODEL-BY-DEFINITION")
           (equal (fn2-cns-drain-child ',child core) (,field core))
           :hints (("Goal" :in-theory
                    (enable fn2-cns-drain-child fn2-cns-drain-child-index ,field))))
         (defthm ,(fn2-columns-sym writer "-CNS-MODEL-BY-DEFINITION")
           (equal (fn2-cns-drain-put-child ',child value core) (,writer value core))
           :hints (("Goal" :in-theory
                    (enable fn2-cns-drain-put-child fn2-cns-drain-child-index ,writer)))))
       (fn2-cns-core-model-projection-events (cdr entries))))))
(make-event
 (value (cons 'progn
   (fn2-cns-core-model-projection-events
     (fn2-product-entries (fn2-core-child-registry (w state))
       '(fn2-core-pool fn2-core-control fn2-core-machines fn2-core-sched fn2-cns-table) (w state))))))

(defthm fn2-cns-draining-domain-snapshot-by-definition
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-draining-domainp id core))
           (equal (fn2-cns-snapshot-read-code id core) :ok))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory
           (e/d (fn2-cns-draining-domainp fn2-cns-snapshot-read-code
                 fn2-machine-phase-read-code fn2-machine-idp
                 fn2-machine-kind fn2-machine-kind-read-code
                 fn2-machine-slot fn2-machine-slot-read-code
                 fn2-machines-kind fn2-machines-slot fn2-machines-rows fn2-cns-rows
                 fn2-cns-drain-cell fn2-cns-drain-get fn2-cns-drain-index)
                (fn2-cns-drain-releasablep fn2-core-machines fn2-cns-table
                 fn2-core-pool fn2-core-control fn2-core-sched fn2-corep fn2-core-wfp)))))

; Normalize only the row readers the actual public run/draining bodies
; call. Other arms and their columns stay outside the proof's open theory.
(defun fn2-cns-draining-row-projection-events (columns calls readers)
  (declare (xargs :verify-guards nil))
  (if (atom columns)
      `((deftheory fn2-cns-draining-native-readers ',(reverse readers)))
    (let* ((field (caar columns)) (reader (fn2-machine-row-reader 'fn2-cns field))
           (directoryp (fn2-machine-directory-fieldp field))
           (native (fn2-columns-col-name (if directoryp 'fn2-machines 'fn2-cns) field))
           (table (if directoryp 'fn2-core-machines 'fn2-cns-table))
           (index (if directoryp 'id '(fn2-machine-slot id fn2-core))))
      (if (not (member-eq reader calls))
          (fn2-cns-draining-row-projection-events (cdr columns) calls readers)
        (cons
         `(defthm ,(fn2-columns-sym reader "-BY-DEFINITION")
            (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                          (equal (fn2-cns-snapshot-read-code id fn2-core) :ok))
                     (equal (,reader id fn2-core) (,native ,index (,table fn2-core))))
            :hints (("Goal" :use fn2-cns-row-access-valid
                     :in-theory
                     (e/d (,reader)
                          (fn2-cns-snapshot-read-code fn2-machine-slot ,native ,table
                           fn2-machines-rows fn2-corep fn2-core-wfp)))))
         (fn2-cns-draining-row-projection-events (cdr columns) calls (cons native readers)))))))
(make-event
 (let* ((world (w state))
        (run (getpropc 'fn2-cns-run 'unnormalized-body nil world))
        (drain (getpropc 'fn2-cns-run-draining 'unnormalized-body nil world)))
   (if (or (not run) (not drain))
       (er soft 'fn2-cns-draining-row-projection-events "Actual CNS run bodies are missing.")
     (value (cons 'progn
       (fn2-cns-draining-row-projection-events (fn2-machine-property 'fn2-cns :columns world)
         (union-eq (all-fnnames run) (all-fnnames drain)) nil))))))

(defun fn2-cns-core-reclaim-expected (id ord retire before)
  (fn2-cns-drain-put-child 'fn2-machines
    (car (fn2-machines-reclaim-list-expected id ord retire
           (fn2-cns-drain-child 'fn2-machines before) nil)) before))
(defthm fn2-cns-core-reclaim-independent
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-machines-partition-reservedp ord (fn2-core-machines core))
                (< 0 (fn2-machines-active-counti ord (fn2-core-machines core)))
                (unsigned-byte-p 32 id))
    (equal (fn2-cns-reclaim id ord retire core)
           (fn2-cns-core-reclaim-expected id ord retire core)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-machines-reserved-reclaim-independent
                            (machines (fn2-core-machines core))
                            (control (fn2-core-control core)))
                 (:instance fn2-product-core-shape (fn2-core core)))
           :in-theory
           (e/d (fn2-cns-reclaim fn2-cns-core-reclaim-expected fn2-machines-reclaim-list-expected)
                (fn2-machines-reclaim fn2-machines-reservation-put
                 fn2-core-machines fn2-core-control update-fn2-core-machines update-fn2-core-control
                 fn2-corep fn2-core-wfp fn2-machines-partition-reservedp)))))

(defthm fn2-cns-core-reclaim-reservation-preserved
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (fn2-cns-draining-reservedp core)
                (< 0 (fn2-machines-active-counti *fn2-cns-admission-ordinal*
                                                (fn2-core-machines core)))
                (unsigned-byte-p 32 id))
    (fn2-cns-draining-reservedp
      (fn2-cns-reclaim id *fn2-cns-admission-ordinal* retire core)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn2-cns-core-reclaim-independent (ord *fn2-cns-admission-ordinal*))
                 (:instance fn2-machines-reserved-reclaim-preserved
                            (ord *fn2-cns-admission-ordinal*)
                            (machines (fn2-core-machines core)) (control (fn2-core-control core)))
                 (:instance fn2-machines-reserved-reclaim-independent
                            (ord *fn2-cns-admission-ordinal*)
                            (machines (fn2-core-machines core)) (control (fn2-core-control core))))
           :in-theory
           (e/d (fn2-cns-core-reclaim-expected fn2-machines-reclaim-list-expected)
                (fn2-cns-reclaim fn2-machines-reclaim fn2-machines-reservation-put
                 fn2-cns-draining-reservedp fn2-machines-partition-reservedp
                 fn2-core-machines fn2-core-control)))))

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

(defthm fn2-cns-core-release-protected-children
  (let ((after (mv-nth 1 (fn2-core-release slot gen kind id ogen core))))
    (and (equal (fn2-core-machines after) (fn2-core-machines core))
         (equal (fn2-cns-table after) (fn2-cns-table core))
         (equal (fn2-core-sched after) (fn2-core-sched core))))
  :hints (("Goal" :in-theory
           (e/d (fn2-core-release)
                (fn2-core-release-children fn2-core-machines fn2-cns-table fn2-core-sched
                 fn2-core-pool fn2-core-control update-fn2-core-pool update-fn2-core-control)))))

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

; Keep the independent intermediate state usable after the first actual
; call has been rewritten to its complete result. These bridges consume
; conservation and the actual release refinement, not a second oracle.
(defthm fn2-cns-independent-release-preserves-pool-accounting
  (implies (and (fn2-pool-semanticp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool))
    (fn2-pool-semanticp (fn2-cns-drain-released-pool slot pool)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-owned-pool-release-pool-effect
                 (:instance fn2-pool-release-conservation
                            (fn2-pool pool) (okind *fn2-cns-kind*) (oslot id)))
           :in-theory (disable fn2-pool-semanticp fn2-pool-release
                               fn2-cns-drain-releasablep fn2-cns-drain-released-pool))))
(defthm fn2-cns-independent-release-keeps-second-releasable
  (implies (and (fn2-pool-semanticp pool)
                (fn2-cns-drain-releasablep slot gen id ogen pool)
                (fn2-cns-drain-releasablep other other-gen id ogen pool)
                (not (equal other slot)))
    (fn2-cns-drain-releasablep other other-gen id ogen
      (fn2-cns-drain-released-pool slot pool)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-cns-distinct-releasable-after-pool-release
                 fn2-cns-owned-pool-release-pool-effect)
           :in-theory (disable fn2-pool-semanticp fn2-pool-release
                               fn2-cns-drain-releasablep fn2-cns-drain-released-pool))))

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
                               fn2-cns-drain-releasablep fn2-cns-drain-released-pool))))
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

; Preserve the exact public take operation's live guard and scalar ABI.
; Registry child facts compose through the actual core face; no synthetic
; take or initializer substitutes for the served operation.
(defun fn2-cns-take-reservation-events (world)
  (declare (xargs :verify-guards nil))
  (let* ((child 'fn2-machine-take-fn2-cns-children)
         (face 'fn2-machine-take-fn2-cns)
         (child-call (cons child (getpropc child 'formals nil world)))
         (face-call (cons face (getpropc face 'formals nil world))))
    (if (or (not (getpropc child 'unnormalized-body nil world))
            (not (getpropc face 'unnormalized-body nil world))
            (not (equal (cdr child-call)
                        '(waiter ctl ctl-gen request fpos flen fkind tx-slot tx-gen
                          ordinal kind fn2-cns fn2-machines fn2-pool fn2-control)))
            (not (equal (cdr face-call)
                        '(waiter ctl ctl-gen request fpos flen fkind tx-slot tx-gen fn2-core)))
            (not (equal (getpropc child 'stobjs-out nil world)
                        '(nil nil nil fn2-cns fn2-machines fn2-pool fn2-control)))
            (not (equal (getpropc face 'stobjs-out nil world) '(nil nil nil fn2-core))))
        '((make-event (er soft 'fn2-cns-take-reservation-events
            "Actual CNS take child/core bodies or full result ABI are unavailable.")))
      `((defthm fn2-cns-take-children-reservation-preserved
          (implies
           (and ,@(fn2-lower-predicates
                    (remove-eq nil (getpropc child 'stobjs-in nil world)) "P")
                ,(getpropc child 'guard t world)
                (fn2-machines-partition-reservedp ordinal fn2-machines))
           (fn2-machines-partition-reservedp ordinal (mv-nth 4 ,child-call)))
          :rule-classes nil
          :hints (("Goal" :in-theory
                   (e/d (,child fn2-machines-free-head-of)
                        (fn2-machines-partition-reservedp fn2-machines-partition-install
                         fn2-machines-park-taken fn2-pool-reserve fn2-core-release-children
                         fn2-machines-free-headi fn2-cns-next-free
                         fn2-cnsp fn2-cns-wfp fn2-machinesp fn2-machines-wfp
                         fn2-poolp fn2-pool-wfp fn2-controlp fn2-control-wfp)))))
        (defthm fn2-cns-take-core-reservation-preserved
          (implies (and (fn2-corep fn2-core) ,(getpropc face 'guard t world)
                        (fn2-cns-draining-reservedp fn2-core))
                   (fn2-cns-draining-reservedp (mv-nth 3 ,face-call)))
          :rule-classes nil
          :hints (("Goal"
                   :use ((:instance fn2-cns-take-children-reservation-preserved
                            (fn2-cns (fn2-cns-table fn2-core))
                            (fn2-machines (fn2-core-machines fn2-core))
                            (fn2-pool (fn2-core-pool fn2-core))
                            (fn2-control (fn2-core-control fn2-core))
                            (ordinal *fn2-cns-admission-ordinal*) (kind *fn2-cns-kind*)))
                   :in-theory
                   (e/d (,face)
                        (,child fn2-cns-draining-reservedp fn2-machines-partition-reservedp
                         fn2-cns-table fn2-core-machines fn2-core-pool fn2-core-control
                         fn2-corep fn2-core-wfp)))))))))
(make-event (value (cons 'progn (fn2-cns-take-reservation-events (w state)))))

; The target is the original live obligation's exact H/C, including its
; defensive held-lease inputs. No discharge is registered until this
; actual public-function proof and its complete evidence have passed.
(defthm fn2-cns-draining-counted-independent-composed
  (implies (and (fn2-corep core) (fn2-core-wfp core)
                (natp budget) (fn2-cns-draining-domainp id core)
                (fn2-cns-draining-reservedp core)
                (fn2-pool-semanticp (fn2-core-pool core)))
    (mv-let (b s d r after) (fn2-cns-run id budget core)
      (fn2-cns-draining-resultp id core b s d r after)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((equal (fn2-cns-row-lease id core) *fn2-cns-lease-held*))
           :in-theory
           (union-theories
            (theory 'fn2-cns-draining-native-readers)
            (e/d (fn2-cns-run fn2-cns-run-draining fn2-machine-contract-check fn2-cns-arm-ok-p
                  fn2-cns-draining-domainp fn2-cns-draining-resultp fn2-cns-draining-expected
                  fn2-cns-drain-cell fn2-cns-drain-get fn2-cns-drain-index
                  fn2-cns-drain-child fn2-cns-drain-child-index fn2-cns-drain-put-child
                  fn2-cns-drain-put-cells fn2-cns-drain-put-cell fn2-cns-drain-put)
                 (fn2-corep fn2-core-wfp fn2-pool-semanticp fn2-pool-release
                  fn2-cns-drain-releasablep fn2-cns-draining-reservedp
                  fn2-core-release fn2-cns-release-ns fn2-cns-lease-release fn2-cns-reclaim))))))
