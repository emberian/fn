; HST-047 / PRF-1259: the output pool's actual launch/startup producer.
; Numerical funding is distinct from the allocation refinement of a cursor,
; matcher or mux window. An absent policy remains a partial resource frontier.
(in-package "ACL2")
(include-book "cold-read-reservation")

(defun fn-orv-policy-p (policy)
  (declare (xargs :guard t))
  (and policy (fn-native-config-output-resources-wfp policy) t))

; Extend the already composed store/thread/cold decision exactly once. The
; caller supplies that decision; no cold allowance is subtracted here.
(defun fn-orv-extend-reservation (base policy core observations)
  (declare (xargs :guard t))
  (cond ((not policy) base)
        ((not (fn-orv-policy-p policy))
         (list :refused :invalid-output-resource-profile
               (nfix (fn-crv-nth 1 base)) (fn-crv-nth 3 base)))
        ((not (equal (fn-crv-nth 0 base) :heap)) base)
        (t
         (let* ((mb (fn-heap-mb-of
                     (fn-heap-grow-runtime-dynamic (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                        (nfix (fn-crv-nth 0 policy))
                        (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))))
                (stack (nfix (fn-crv-nth 4 base)))
                (threads (nfix (fn-crv-nth 5 base)))
                (total (fn-heap-reservation-octets mb core stack threads)))
           (if (<= total (fn-heap-machine-octets observations))
               (list :heap mb (fn-crv-nth 2 base) (fn-crv-nth 3 base) stack threads)
             (list :refused :machine-cannot-hold-output-pool (fn-heap-mb-of total)
                   (fn-crv-nth 3 base)))))))

; The typed flat ledger has seventeen resizable columns. This is a named
; layout projection (two copies of 8-byte cells plus fixed setup storage),
; not a proved SBCL allocator/collector bound. It must be refined before an
; operation can declare its complete allocation tariff.
(defun fn-orv-startup-slots (max-connections)
  (declare (xargs :guard t))
  (+ 2 (nfix max-connections)))

(defun fn-orv-bookkeeping-octets (slots)
  (declare (xargs :guard t))
  (+ 8192 (* 272 (nfix slots))))

(local
 (defthm fn-orv-capture-at-is-config-at
   (implies (natp n) (equal (fn-crv-nth n x) (fn-ncfg-nth n x)))
   :hints (("Goal" :in-theory (enable fn-crv-nth fn-ncfg-nth)))))

; DYNAMIC is the actual runtime capture. STORE-NEED is the existing store
; figure before either extension; COLD is the normalized explicit descriptor.
; The owner gets bookkeeping and one maintenance lease first. At least one
; equal user lease must remain affordable; none borrows collector/nursery room.
(defun fn-orv-startup-grant (dynamic store-need cold policy slots)
  (declare (xargs :guard t))
  (cond ((not policy) (list :partial :output-resources-unconfigured))
        ((not (and (fn-orv-policy-p policy)
                   (fn-native-config-cold-resources-wfp cold)
                   (natp dynamic) (natp store-need)
                   (natp slots) (<= 3 slots) (< slots (expt 2 32))))
         (list :refused :invalid-output-resource-profile))
        ((< dynamic (+ store-need (nfix (fn-crv-nth 0 cold))
                       (fn-crv-nth 0 policy)))
         (list :refused :output-pool-not-held))
        ((< (fn-crv-nth 0 policy)
            (+ (fn-orv-bookkeeping-octets slots) (* 2 (fn-crv-nth 1 policy))))
         (list :refused :minimum-output-quantum-unaffordable))
        (t (list :hold (fn-crv-nth 0 policy) (fn-crv-nth 1 policy)
                 (fn-orv-bookkeeping-octets slots) slots))))

(defthm fn-orv-accepted-launch-fits-observed-machine
  (implies (and (fn-orv-policy-p policy)
                (equal (fn-crv-nth 0 (fn-orv-extend-reservation base policy core observations)) :heap))
           (let ((d (fn-orv-extend-reservation base policy core observations)))
             (<= (fn-heap-reservation-octets (fn-crv-nth 1 d) core
                                             (fn-crv-nth 4 d) (fn-crv-nth 5 d))
                 (fn-heap-machine-octets observations))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-orv-extend-reservation fn-crv-nth fn-orv-policy-p)
                                  (fn-heap-reservation-octets fn-heap-machine-octets
                                   fn-native-config-output-resources-wfp fn-heap-mb-of)))))

(defthm fn-orv-accepted-launch-funds-output-dynamic-allowance
  (implies (equal (fn-crv-nth 0 (fn-orv-extend-reservation base policy core observations)) :heap)
           (<= (+ (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                  (nfix (fn-crv-nth 0 policy)))
               (* *fn-heap-mib* (nfix (fn-crv-nth 1 (fn-orv-extend-reservation base policy core observations))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-heap-mb-of-covers
                            (octets (fn-heap-grow-runtime-dynamic
                                       (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                                       (nfix (fn-crv-nth 0 policy))
                                       (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))))
           :in-theory (e/d (fn-orv-extend-reservation fn-crv-nth fn-orv-policy-p)
                            (fn-heap-grow-runtime-dynamic fn-heap-mb-of fn-heap-reservation-octets
                             fn-heap-machine-octets fn-native-config-output-resources-wfp)))))

(defthm fn-orv-startup-hold-protects-owner-and-one-quantum
  (implies (equal (car (fn-orv-startup-grant dynamic store-need cold policy slots)) :hold)
           (and (<= (+ store-need (nfix (fn-crv-nth 0 cold)) (fn-crv-nth 0 policy)) dynamic)
                (<= (+ (fn-orv-bookkeeping-octets slots) (* 2 (fn-crv-nth 1 policy)))
                    (fn-crv-nth 0 policy))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-orv-startup-grant) (fn-crv-nth fn-orv-policy-p fn-orv-bookkeeping-octets)))))

;; The status/health line naming the output-accounting mode, so the mode is
;; never silent (root ruling 2026-10-04): with no [resources] output policy
;; the node runs unaccounted output; with one, every first command passes
;; the admission gate (books/output-command-admission.lisp).
(defun fn-orv-accounting-line (policy)
  (declare (xargs :guard t))
  (if (fn-orv-policy-p policy)
      (coerce (append (coerce "output accounting: on output_heap_octets=" 'list)
                      (explode-nonnegative-integer (nfix (fn-crv-nth 0 policy)) 10 nil)
                      (coerce " output_quantum_heap_octets=" 'list)
                      (explode-nonnegative-integer (nfix (fn-crv-nth 1 policy)) 10 nil))
              'string)
    "output accounting: off (no [resources])"))

(defthm fn-orv-accounting-line-off-without-policy
  (equal (fn-orv-accounting-line nil) "output accounting: off (no [resources])"))

(in-theory (disable fn-orv-policy-p fn-orv-extend-reservation
                    fn-orv-bookkeeping-octets fn-orv-startup-grant))
