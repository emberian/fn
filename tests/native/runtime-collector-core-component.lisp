;;; Load only in a dedicated disposable ACL2/SBCL process after the actual
;;; allocation-epoch-host leaf and the native collector/bridge. This invokes
;;; full GC in that process. Never load into a node or another lane's world.
;;; Core callbacks and concrete pool representation are the actual definitions.
;;; Installation/profile values are explicit fixtures, not installed authority.
(in-package "ACL2")

(defun fnn-test-collector-core-pool (turns next)
  (let* ((pool (create-fn-page-read-pool))
         (reservation (sb-ext:dynamic-space-size))
         (association (list :allocation-epoch-association
                            :test-runtime :test-profile :test-pool
                            sb-vm:gencgc-page-bytes reservation))
         (installation (list :allocation-epoch-installation association
                             most-positive-fixnum reservation 1 0 0 0 0
                             64 128 256)))
    (assert (fn-aec-installationp installation))
    (update-fn-prp-alloc-installation installation pool)
    (update-fn-prp-alloc-mode :draining pool)
    (update-fn-prp-alloc-epoch 17 pool)
    (update-fn-prp-alloc-occupied 65536 pool)
    (update-fn-prp-alloc-allocated 512 pool)
    (update-fn-prp-alloc-active-turns turns pool)
    (update-fn-prp-alloc-gc-nonce nil pool)
    (fn-owner-page-read-keep-ledger
     (fn-prl-build '(1000000 1000 1000 1000 100)
                   '(0 0 0 0 0) next nil '(0 0 0 0 0)) pool)
    (assert (fn-aec-pool-statep pool))
    pool))

;; Run the actual world-checked installer; it checks each carried guard theorem
;; and the selected raw symbol's common-lisp-compliant class before publishing.
(fnn-install-raw-dispatch)
(dolist (entry '(fn-aec-pool-collection-request-internal
                fn-aec-pool-collect-observed-internal
                fn-aec-pool-uncertain-internal))
  (assert (eq (gethash entry *fnn-raw-dispatch*) entry)))

(let* ((pool (fnn-test-collector-core-pool 1 9))
       (binding (fnn-runtime-collector-binding-make pool))
       (sample (fnn-runtime-collector-binding-observation binding))
       (gc-epoch sb-kernel::*gc-epoch*)
       (ledger (fn-owner-page-read-ledger pool)))
  (assert (eq (fnn-runtime-collection-step binding) :not-quiescent))
  (assert (eq gc-epoch sb-kernel::*gc-epoch*))
  (assert (eq ledger (fn-owner-page-read-ledger pool)))
  (assert (= (fn-prp-alloc-allocated pool) 512))
  (assert (eq (fnn-runtime-collection-status sample) :unobserved))
  ;; Test fixture supplies a completed drain. Actual once-only turn receipt
  ;; ownership is tested separately, not inferred from this direct update.
  (update-fn-prp-alloc-active-turns 0 pool)
  (assert (eq (fnn-runtime-collection-step binding) :resume))
  (assert (not (eq gc-epoch sb-kernel::*gc-epoch*)))
  (assert (eq (fnn-runtime-collection-status sample) :completed))
  (assert (= (fnn-runtime-collection-nonce sample) 9))
  (assert (= (fn-prl-nth 2 (fn-owner-page-read-ledger pool)) 10))
  (assert (equal (fn-prl-nth 1 (fn-owner-page-read-ledger pool)) '(0 0 0 0 1)))
  (assert (eq (fn-prp-alloc-mode pool) :active))
  (assert (= (fn-prp-alloc-epoch pool) 18))
  (assert (= (fn-prp-alloc-allocated pool) 256))
  (assert (= (fn-prp-alloc-occupied pool)
             (* (fnn-runtime-collection-dynamic-pages sample)
                (fnn-runtime-collection-page-octets sample))))
  (assert (null (fn-prp-alloc-gc-nonce pool)))
  (assert (fn-aec-pool-statep pool))
  ;; Replaying the previously valid observation cannot reset the next epoch.
  (let ((occupied (fn-prp-alloc-occupied pool)))
    (assert (eq (fnn-runtime-collection-complete binding 9) :recovery-required))
    (assert (eq (fn-prp-alloc-mode pool) :recovery))
    (assert (= (fn-prp-alloc-epoch pool) 18))
    (assert (= (fn-prp-alloc-occupied pool) occupied))
    (assert (= (fn-prp-alloc-allocated pool) 256))))

(let* ((pool (fnn-test-collector-core-pool 0 11))
       (binding (fnn-runtime-collector-binding-make pool)))
  (sb-sys:without-gcing
    (assert (eq (fnn-runtime-collection-step binding) :recovery-required)))
  (assert (eq (fnn-runtime-collection-status
               (fnn-runtime-collector-binding-observation binding)) :deferred))
  (assert (eq (fn-prp-alloc-mode pool) :recovery))
  (assert (= (fn-prp-alloc-epoch pool) 17))
  (assert (= (fn-prp-alloc-occupied pool) 65536))
  (assert (= (fn-prp-alloc-allocated pool) 640))
  (assert (= (fn-prp-alloc-gc-nonce pool) 11))
  (assert (= (fn-prl-nth 2 (fn-owner-page-read-ledger pool)) 12))
  (assert (fn-aec-pool-statep pool)))

(format t "~&COLLECTOR-ACTUAL-CORE PASS drain/full/replay/deferred~%")
