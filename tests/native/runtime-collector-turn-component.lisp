;;; Load only in a dedicated disposable ACL2/SBCL process after the actual
;;; allocation-epoch-host leaf and the native collector/bridge. This invokes
;;; full GC in that process. Never load into a node or another lane's world.
;;; Core callbacks and concrete pool representation are the actual definitions.
;;; Installation/profile values are explicit fixtures, not installed authority.
(in-package "ACL2")

(defun fnn-test-collector-turn-pool (turns next)
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

;; Source fixture installation is explicit; turn counts below are changed ONLY
;; by the actual ATS entry/finish definitions. No hand-written drain update.
(fnn-install-raw-dispatch)
(dolist (entry '(fn-aec-pool-collection-request-internal
                fn-aec-pool-collect-observed-internal fn-aec-pool-uncertain-internal
                fn-ats-enter-internal fn-ats-finish-owned fn-ats-uncertain-internal))
  (assert (eq (fnn-fixed-raw-callback entry) (symbol-function entry))))

(let* ((pool (fnn-test-collector-turn-pool 0 9))
       (slots (create-fn-allocation-turn-slots))
       (binding (fnn-runtime-collector-binding-make pool))
       (epoch sb-kernel::*gc-epoch*))
  (update-fn-prp-alloc-mode :active pool)
  (multiple-value-bind (word actual-slots)
      (fn-ats-construct-internal '(:connection-start :read-completion) slots pool)
    (assert (and (eq word :constructed) (eq actual-slots slots))))
  (multiple-value-bind (word0 nonce0 s0 p0)
      (fn-ats-enter-internal 0 :connection-start slots pool)
    (assert (and (eq word0 :gate-owned) (= nonce0 9) (eq s0 slots) (eq p0 pool)))
    (multiple-value-bind (word1 nonce1 s1 p1)
        (fn-ats-enter-internal 1 :read-completion slots pool)
      (assert (and (eq word1 :gate-owned) (= nonce1 10) (eq s1 slots) (eq p1 pool)))
      (assert (= (fn-prp-alloc-active-turns pool) 2))
      (assert (eq (fn-ats-prepay-body-internal 0 nonce0 32 slots pool) :prepaid))
      (assert (eq (fn-ats-prepay-body-internal 1 nonce1 48 slots pool) :prepaid))
      ;; Admission closes through the actual core transition, not the collector.
      (fn-aec-pool-drain-internal pool)
      (let ((allocated (fn-prp-alloc-allocated pool))
            (ledger (fn-owner-page-read-ledger pool)))
        (assert (eq (fnn-runtime-collection-step binding) :not-quiescent))
        (assert (eq (fn-prp-alloc-mode pool) :draining))
        (assert (eq epoch sb-kernel::*gc-epoch*))
        (assert (= allocated (fn-prp-alloc-allocated pool)))
        (assert (eq ledger (fn-owner-page-read-ledger pool)))
        ;; First real receipt settles once; duplicate cannot settle slot1.
        (assert (eq (fn-ats-finish-owned 0 nonce0 slots pool) :left))
        (assert (= (fn-prp-alloc-active-turns pool) 1))
        (assert (eq (fn-ats-finish-owned 0 nonce0 slots pool) :stale))
        (assert (= (fn-prp-alloc-active-turns pool) 1))
        (assert (eq (fnn-runtime-collection-step binding) :not-quiescent))
        (assert (eq epoch sb-kernel::*gc-epoch*))
        (assert (= allocated (fn-prp-alloc-allocated pool)))
        ;; Last real receipt authorizes drain completion, then real full GC.
        (assert (eq (fn-ats-finish-owned 1 nonce1 slots pool) :left))
        (assert (= (fn-prp-alloc-active-turns pool) 0))
        (assert (= allocated (fn-prp-alloc-allocated pool)))
        (assert (eq (fnn-runtime-collection-step binding) :resume))
        (assert (not (eq epoch sb-kernel::*gc-epoch*)))
        (assert (= (fn-prp-alloc-epoch pool) 18))
        (assert (= (fn-prp-alloc-allocated pool) 256))
        (assert (= (fnn-runtime-collection-nonce
                     (fnn-runtime-collector-binding-observation binding)) 11))
        ;; The same physical slot gets a fresh shared identity after GC.
        (multiple-value-bind (word2 nonce2 s2 p2)
            (fn-ats-enter-internal 0 :connection-start slots pool)
          (assert (and (eq word2 :gate-owned) (= nonce2 12)
                       (eq s2 slots) (eq p2 pool)))
          (assert (eq (fn-ats-finish-owned 0 nonce0 slots pool) :stale))
          (assert (= (fn-prp-alloc-active-turns pool) 1))
          (assert (eq (fn-ats-finish-owned 0 nonce2 slots pool) :left))
          (assert (= (fn-prp-alloc-active-turns pool) 0)))
      (assert (fn-aec-pool-statep pool))))))
(format t "~&COLLECTOR-ACTUAL-TURNS PASS two-slot/drain/duplicate/full/reuse~%")
