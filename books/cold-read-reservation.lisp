; P12 launcher extension, separate from concrete allocator demand refinement.
; Explicit pool heap + persistent cold_workers stacks/runtime are added to
; the exact existing launch decision. No guessed resource defaults here.
(in-package "ACL2")
(include-book "heap-reservation")
(include-book "native-config")
(include-book "page-read-resources")

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
  (* (nfix (fn-crv-nth 1 policy)) (fn-crv-native-per-worker profile)))

(defun fn-crv-pool-budget (policy profile)
  (declare (xargs :guard t))
  (list (+ (nfix (fn-crv-nth 0 policy)) (fn-crv-native-baseline policy profile))
        0 (nfix (fn-crv-nth 2 policy)) (nfix (fn-crv-nth 1 policy))
        (nfix (fn-crv-nth 3 policy))))

(defun fn-crv-extend-reservation (base policy core observations)
  (declare (xargs :guard t))
  (cond ((not policy) base)
        ((not (fn-crv-policy-p policy))
         (list :refused :invalid-cold-resource-profile
               (nfix (fn-crv-nth 1 base)) (fn-crv-nth 3 base)))
        ((not (equal (fn-crv-nth 0 base) :heap)) base)
        (t
         (let* ((mb (fn-heap-mb-of (fn-heap-grow-runtime-dynamic (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                        (nfix (fn-crv-nth 0 policy))
                        (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))))
                (stack (nfix (fn-crv-nth 4 base)))
                (threads (+ (nfix (fn-crv-nth 5 base)) (nfix (fn-crv-nth 1 policy))))
                (total (fn-heap-reservation-octets mb core stack threads)))
           (if (<= total (fn-heap-machine-octets observations))
               (list :heap mb (fn-crv-nth 2 base) (fn-crv-nth 3 base) stack threads)
             (list :refused :machine-cannot-hold-threads (fn-heap-mb-of total)
                   (fn-crv-nth 3 base)))))))

; This is the numerical subject the native launcher will call. Its actual
; target-layout/allocator model and initialization are separate obligations.
(defthm fn-crv-accepted-launch-fits-observed-machine
  (implies (and (fn-crv-policy-p policy)
                (equal (fn-crv-nth 0 (fn-crv-extend-reservation base policy core observations)) :heap))
           (let ((d (fn-crv-extend-reservation base policy core observations)))
             (<= (fn-heap-reservation-octets (fn-crv-nth 1 d) core
                                             (fn-crv-nth 4 d) (fn-crv-nth 5 d))
                 (fn-heap-machine-octets observations))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-crv-extend-reservation fn-crv-nth fn-crv-policy-p)
                                  (fn-heap-reservation-octets fn-heap-machine-octets
                                   fn-native-config-cold-resources-wfp fn-heap-mb-of)))))

(defthm fn-crv-accepted-launch-funds-persistent-cold-workers-by-definition
  (implies (and (fn-crv-policy-p policy)
                (equal (fn-crv-nth 0 (fn-crv-extend-reservation base policy core observations)) :heap))
           (equal (fn-crv-nth 5 (fn-crv-extend-reservation base policy core observations))
                  (+ (nfix (fn-crv-nth 5 base)) (nfix (fn-crv-nth 1 policy)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-crv-extend-reservation fn-crv-nth fn-crv-policy-p)
                                  (fn-heap-reservation-octets fn-heap-machine-octets
                                   fn-native-config-cold-resources-wfp fn-heap-mb-of)))))

(defthm fn-crv-accepted-launch-funds-pool-dynamic-allowance
  (implies (equal (fn-crv-nth 0 (fn-crv-extend-reservation base policy core observations)) :heap)
           (<= (+ (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                  (nfix (fn-crv-nth 0 policy)))
               (* *fn-heap-mib* (nfix (fn-crv-nth 1 (fn-crv-extend-reservation base policy core observations))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-heap-mb-of-covers
                            (octets (fn-heap-grow-runtime-dynamic
                                       (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                                       (nfix (fn-crv-nth 0 policy))
                                       (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))))
           :in-theory (e/d (fn-crv-extend-reservation fn-crv-nth fn-crv-policy-p)
                            (fn-heap-grow-runtime-dynamic fn-heap-mb-of fn-heap-reservation-octets
                             fn-heap-machine-octets fn-native-config-cold-resources-wfp)))))

(in-theory (disable fn-crv-nth fn-crv-policy-p fn-crv-native-per-worker
                    fn-crv-native-baseline fn-crv-pool-budget fn-crv-extend-reservation))
