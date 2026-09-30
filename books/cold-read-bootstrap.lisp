; Concrete permanent cold-pool startup demand for selected SBCL layout.
; Payload/list/decoder demand is separate. This does not assert a complete
; supported served profile until those physical consumers are joined.
(in-package "ACL2")
(include-book "cold-read-layout")
(include-book "assumptions-cold-runtime")
(include-book "cold-read-reservation")
(include-book "payload-extent")

(defun fn-crb-cache-capacity ()
  (declare (xargs :guard t))
  (+ 1 (fn-arx-read-cache-entries)))

; Registered incarnations and checkpoint-retention pins jointly consume F
; descriptor/retention credits. Issued and discovery rows consume W worker
; credits. Cache insertion can coexist with the eight retained rows.
(defun fn-crb-binding-capacity (policy)
  (declare (xargs :guard t))
  (+ (nfix (fn-crv-nth 2 policy)) (nfix (fn-crv-nth 1 policy))
     (fn-crb-cache-capacity)))

(defun fn-crb-map-octets (policy)
  (declare (xargs :guard t))
  (+ (* 4 (fn-crl-table-octets (fn-crv-nth 2 policy) nil))
     (fn-crl-table-octets (fn-crv-nth 1 policy) t)
     (fn-crl-table-octets (fn-crb-cache-capacity) nil)))

; Selected runtime dynamic thread objects and persistent registry paths,
; including structural slots. Active result/I/O/token rows are per-job demand.
(defun fn-crb-executor-octets (policy runtime)
  (declare (xargs :guard t))
  (fn-crt-executor-octets (fn-crv-nth 1 policy) runtime))

; fn-prl-remove-aux creates at most one reverse spine and one final spine.
; Original binding spines stay in the per-row live charges. This reserve
; remains available even when a refused call cannot acquire a new job.
(defun fn-crb-remove-scratch-octets (policy)
  (declare (xargs :guard t))
  (* 2 16 (fn-crb-binding-capacity policy)))

(defun fn-crb-permanent-baseline (policy profile runtime)
  (declare (xargs :guard t))
  (list (+ (fn-crv-native-baseline policy profile)
           (* 2 (+ (fn-crb-map-octets policy)
                   (fn-crb-executor-octets policy runtime)
                   (fn-crb-remove-scratch-octets policy))))
        0 0 0 0))

; The plan names native constructor capacities; the host never recomputes
; normalization, cache insertion overlap or the table's representable limit.
; Failure returns no constructor arguments and allocates no installed pool.
; Bookkeeping and all other demand are obligations of the eventual caller.
(defun fn-crb-start-plan (policy profile runtime)
  (declare (xargs :guard t))
  (cond ((not (fn-crt-selectedp runtime)) '(:refused :unsupported-cold-runtime))
        ((not (fn-crv-policy-p policy)) '(:refused :invalid-cold-resource-profile))
        ((not (and (fn-crl-table-supportedp (fn-crv-nth 1 policy))
                   (fn-crl-table-supportedp (fn-crv-nth 2 policy))
                   (fn-crl-table-supportedp (fn-crb-cache-capacity))))
         '(:refused :unrepresentable-cold-table-capacity))
        (t
         (let ((budget (fn-crv-pool-budget policy profile))
               (baseline (fn-crb-permanent-baseline policy profile runtime)))
           (if (fn-prs-fundedp budget baseline '(0 0 0 0 0) '(0 0 0 0 0))
               (list :admitted budget baseline
                     (fn-crl-table-capacity (fn-crv-nth 2 policy))
                     (fn-crl-table-capacity (fn-crv-nth 1 policy))
                     (fn-crl-table-capacity (fn-crb-cache-capacity))
                     (fn-crv-nth 1 policy))
             '(:refused :cold-bootstrap-exceeds-budget))))))

; Numerical projection of the plan; not an allocator refinement theorem.
(defthm fn-crb-admitted-start-funds-permanent-baseline-by-definition
  (implies (equal (fn-crv-nth 0 (fn-crb-start-plan policy profile runtime)) :admitted)
           (fn-prs-fundedp (fn-crv-pool-budget policy profile)
                           (fn-crb-permanent-baseline policy profile runtime)
                           '(0 0 0 0 0) '(0 0 0 0 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-crb-start-plan fn-crv-nth)
                                  (fn-crv-pool-budget fn-crb-permanent-baseline
                                   fn-prs-fundedp)))))

(in-theory (disable fn-crb-cache-capacity fn-crb-binding-capacity
                    fn-crb-map-octets fn-crb-executor-octets
                    fn-crb-remove-scratch-octets fn-crb-permanent-baseline
                    fn-crb-start-plan))
