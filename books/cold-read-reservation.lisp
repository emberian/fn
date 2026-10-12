; P12: the explicit cold pool's budget (its heap and its persistent
; cold_workers' stacks and runtime), which the served run's launch funds as
; one of its pools (books/heap-command.lisp fn-mo-serve-pools: the
; configure's LIMIT excludes it and the dynamic space adds it; its workers
; are the launch's pool threads, fn-mo-serve-pool-threads).  No guessed
; resource defaults here.
(in-package "ACL2")
(include-book "heap-reservation")
(include-book "native-config")
(include-book "page-read-resources")
(include-book "cold-read-wait")

(defun fn-crv-nth (n x)
  (declare (xargs :guard (natp n)))
  (if (consp x) (if (zp n) (car x) (fn-crv-nth (- n 1) (cdr x))) nil))

(defun fn-crv-policy-p (policy)
  (declare (xargs :guard t))
  (and policy (fn-native-config-cold-resources-wfp policy) t))

; Idle executor native storage is held until service shutdown. Per-job
; settlement releases only the execution lease, never these native octets.
(defun fn-crv-native-per-worker (profile)
  (declare (xargs :guard t))
  (+ (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*))

(defun fn-crv-native-baseline (policy profile)
  (declare (xargs :guard t))
  (+ (* (nfix (fn-crv-nth 1 policy)) (fn-crv-native-per-worker profile))
     (fn-cwq-queue-octets)))

(defun fn-crv-pool-budget (policy profile)
  (declare (xargs :guard t))
  (list (+ (nfix (fn-crv-nth 0 policy)) (fn-crv-native-baseline policy profile))
        0 (nfix (fn-crv-nth 2 policy)) (nfix (fn-crv-nth 1 policy))
        (nfix (fn-crv-nth 3 policy))))

; The bounded wait's queue is charged: the pool's native baseline is at least
; its storage (books/cold-read-wait.lisp), whatever the worker count.
(defthm fn-crv-native-baseline-charges-the-cold-wait-queue
  (<= (fn-cwq-queue-octets) (fn-crv-native-baseline policy profile))
  :hints (("Goal" :in-theory (enable fn-crv-native-baseline fn-crv-native-per-worker)))
  :rule-classes nil)

(in-theory (disable fn-crv-nth fn-crv-policy-p fn-crv-native-per-worker
                    fn-crv-native-baseline fn-crv-pool-budget))
