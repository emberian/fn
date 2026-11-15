; Exact whole-H/C controls for FN2-CNS-CORE-RELEASE-INDEPENDENT.
; The actual initialized core has two owned ranges and nonempty sibling data.
; These component witnesses do not claim the owner is a reachable CNS row.
(in-package "ACL2")
(include-book "../books/cns-release-refinement")
(include-book "core-snapshot-support")

(defun fn2-cns-core-release-law-run (control fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((profile *fn2-profile-tiny*)
       (supported (fn2-core-profilep profile))
       (fn2-core (fn2-core-init profile fn2-core))
       ((mv rc slot gen fn2-core)
        (fn2-core-reserve 0 *fn2-cns-kind* 10 1 fn2-core))
       ((mv sc sibling sibling-gen fn2-core)
        (fn2-core-reserve 0 *fn2-cns-kind* 11 1 fn2-core))
       ((unless (and (eq rc :ok) (eq sc :ok))) (mv nil fn2-core))
       ((mv wc fn2-core)
        (fn2-core-write sibling sibling-gen 0 77 *fn2-cns-kind* 11 1 fn2-core))
       (before (fn2-test-core-snapshot fn2-core))
       (pool (fn2-cns-drain-child 'fn2-pool before))
       (base (and supported (eq wc :ok) (not (equal slot sibling))
                  (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                  (fn2-cns-drain-releasablep slot gen 10 1 pool)
                  (fn2-cns-drain-releasablep sibling sibling-gen 11 1 pool)
                  (equal (fn2-cns-drain-cell 'fn2-pool-data
                           (fn2-cns-drain-cell 'fn2-pool-base sibling pool) pool) 77)))
       ; Only the supplied generation is changed by the removal control.
       ; The complete before-state and its type/WFP premises are retained.
       (argument-gen (if (eq control :without-generation) (+ 1 gen) gen))
       (ownership (fn2-cns-drain-releasablep slot argument-gen 10 1 pool))
       (whole-h (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) ownership))
       ((mv code fn2-core)
        (fn2-core-release slot argument-gen *fn2-cns-kind* 10 1 fn2-core))
       (released (fn2-test-core-snapshot fn2-core))
       (expected (fn2-cns-core-release-expected
                  slot argument-gen *fn2-cns-kind* 10 1 before))
       (original-c (equal (list code released) expected))
       ; Execute the changed behavior, keeping the actual release scalar.
       ((mv mc fn2-core)
        (if (eq control :sibling-write)
            (fn2-core-write sibling sibling-gen 0 88 *fn2-cns-kind* 11 1 fn2-core)
          (mv :ok fn2-core)))
       (after (fn2-test-core-snapshot fn2-core))
       (conclusion (equal (list code after) expected)))
    (mv (and base
             (case control
               ; The evidence payload is the actual constructor's before
               ; snapshot. The release above cannot change that value.
               (:snapshot (list slot gen sibling sibling-gen before))
               (:positive (and whole-h original-c conclusion
                               (member-eq code '(:ok :retired))))
               (:without-generation
                (and (not ownership) (not whole-h) (eq code :stale)
                     (equal (fn2-cns-drain-child 'fn2-pool released) pool)
                     (equal (fn2-cns-drain-get 'fn2-control-stop
                              (fn2-cns-drain-child 'fn2-control released)) 1)
                     (equal (fn2-cns-drain-get 'fn2-control-stop-reason
                              (fn2-cns-drain-child 'fn2-control released))
                            *fn2-stop-reason-pool-release*)
                     (not original-c) (not conclusion)))
               (:sibling-write
                (and whole-h original-c (eq mc :ok) (not conclusion)
                     (equal (car expected) code)))
               (otherwise nil)))
        fn2-core)))

(defun fn2-cns-core-release-control (control)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (yes fn2-core)
      (fn2-cns-core-release-law-run control fn2-core) yes)))
(defun fn2-cns-core-release-positive ()
  (declare (xargs :verify-guards nil))
  (fn2-cns-core-release-control :positive))
(defun fn2-cns-core-release-without-generation ()
  (declare (xargs :verify-guards nil))
  (fn2-cns-core-release-control :without-generation))
(defun fn2-cns-core-release-sibling-mutation ()
  (declare (xargs :verify-guards nil))
  (fn2-cns-core-release-control :sibling-write))
(assert-event (and (fn2-cns-core-release-positive)
                   (fn2-cns-core-release-without-generation)
                   (fn2-cns-core-release-sibling-mutation)))

(fn2-assert-owed-teeth fn2-cns-core-release-independent)
