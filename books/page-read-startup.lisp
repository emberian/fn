; DEFAULT pre-open SAME-pool backing projection. Partial selected storage
; coverage, not a complete collector/controller/source graph tariff.
(in-package "ACL2")
(include-book "cold-read-layout")
(include-book "cold-guard-bootstrap")
(include-book "decoded-worker-backing")
(include-book "output-reservation")

(defun fn-prstartup-nth (n x)
 (declare (xargs :guard (natp n)))
 (if (consp x) (if (zp n) (car x) (fn-prstartup-nth (1- n) (cdr x))) nil))

(defun fn-prstartup-fd-bookkeeping ()
 (declare (xargs :guard t)) 16)

(defun fn-prstartup-baseline-heap (files workers)
 (declare (xargs :guard t))
 (+ (* 5 (fn-crl-table-octets files nil))
    (fn-cgb-baseline-octets)
    (nfix (fn-prstartup-nth 0 (fn-dwb-reusable-baseline-vector workers)))))

; Preserve a registration working reserve alongside the five persistent
; tables. Actual full paths are charged by the existing path issuer; ROOT
; here pays a minimum feasible quantum, not a bound on later filenames.
(defun fn-prstartup-required-heap (files workers root)
 (declare (xargs :guard t))
 (+ (fn-prstartup-baseline-heap files workers)
    (* (nfix files) 2 (+ (fn-prstartup-fd-bookkeeping) 32
                        (* 4 (if (stringp root) (length root) 0))))))

(defun fn-prstartup-affordable-capacity (lo hi fuel available workers root)
 (declare (xargs :guard (and (natp lo) (natp hi) (natp fuel))
                 :measure (nfix fuel)))
 (if (or (zp fuel) (<= hi lo)) lo
  (let ((mid (min hi (max (+ 1 lo) (nfix (ceiling (+ lo hi) 2))))))
   (if (<= (fn-prstartup-required-heap mid workers root) (nfix available))
    (fn-prstartup-affordable-capacity mid hi (1- fuel) available workers root)
    (fn-prstartup-affordable-capacity lo (1- mid) (1- fuel) available workers root)))))

(defun fn-prstartup-plan (dynamic occupied protected root workers stack runtime cache-limit fd-limit)
 (declare (xargs :guard t))
 (let* ((available (nfix (- (nfix dynamic) (max (nfix occupied) (nfix protected)))))
        (minimum (max 8 (+ 1 (nfix cache-limit))))
        (native (* (nfix workers) (+ (nfix stack) (nfix runtime)))))
  (cond
   ((not (and (natp dynamic) (natp occupied) (natp protected) (stringp root)
              (posp workers) (natp stack) (natp runtime) (natp cache-limit) (natp fd-limit)
              (<= occupied dynamic) (<= protected dynamic)))
    (list :refused :invalid-default-pool-capture))
   ((not (and (<= minimum fd-limit) (fn-crl-table-supportedp minimum)))
    (list :refused :default-pool-table-not-representable))
   ((not (<= (fn-prstartup-required-heap minimum workers root) available))
    (list :refused :default-pool-headroom-unavailable))
   (t
    (let* ((files (fn-prstartup-affordable-capacity minimum (min (nfix fd-limit) (expt 2 24)) 25 available workers root))
           (baseline (+ (fn-prstartup-baseline-heap files workers) native)))
      (list :admitted
        (list (+ available native) 0 files workers 18446744073709551615)
        (list baseline 0 0 0 0)
        0 (fn-prstartup-fd-bookkeeping) 18446744073709551615
        workers (fn-cgb-capacity)))))))

(defun fn-prstartup-file-capacity (plan)
 (declare (xargs :guard t)) (nfix (fn-prstartup-nth 2 (fn-prstartup-nth 1 plan))))

(defun fn-prstartup-cache-capacity (plan)
 (declare (xargs :guard t))
 ; The same funded peak table size covers cache insertion overlap.
 (fn-prstartup-file-capacity plan))

(defun fn-prstartup-scope ()
 (declare (xargs :guard t)) :partial-fixed-storage)

(defun fn-prstartup-protected (profile core nursery output max-connections)
 (declare (xargs :guard t) (ignore max-connections))
 (+ (fn-heap-figure-octets profile core nursery)
    (nfix (fn-crv-nth 0 output))))

(defun fn-prstartup-default-plan
  (dynamic occupied profile core nursery cold output max-connections root workers cache-limit fd-limit)
 (declare (xargs :guard t))
 (cond (cold (list :refused :unpriced-complete-cold-profile))
       ((not (or (not output) (fn-orv-policy-p output)))
        (list :refused :invalid-output-resource-profile))
       (t (fn-prstartup-plan dynamic occupied
            (fn-prstartup-protected profile core nursery output max-connections)
            root workers (fn-heap-stack-octets profile)
            *fn-heap-thread-runtime-octets* cache-limit fd-limit))))

(defun fn-prstartup-planp (plan)
 (declare (xargs :guard t))
 (let* ((b (fn-prstartup-nth 1 plan)) (u (fn-prstartup-nth 2 plan))
        (f (fn-prstartup-file-capacity plan)) (workers (fn-prstartup-nth 6 plan)))
  (and (true-listp plan) (equal (len plan) 8) (eq (car plan) :admitted)
       (posp workers) (<= 8 f) (fn-crl-table-supportedp f)
       (natp (fn-prstartup-nth 0 b)) (natp (fn-prstartup-nth 0 u))
       (equal b (list (fn-prstartup-nth 0 b) 0 f workers 18446744073709551615))
       (equal u (list (fn-prstartup-nth 0 u) 0 0 0 0))
       (<= (fn-prstartup-nth 0 u) (fn-prstartup-nth 0 b))
       (<= (fn-prstartup-baseline-heap f workers) (fn-prstartup-nth 0 u))
       (equal (fn-prstartup-nth 3 plan) 0)
       (equal (fn-prstartup-nth 4 plan) (fn-prstartup-fd-bookkeeping))
       (equal (fn-prstartup-nth 5 plan) 18446744073709551615)
       (equal (fn-prstartup-nth 7 plan) (fn-cgb-capacity)))))

(defun fn-prstartup-decoded-workers (plan)
 (declare (xargs :guard t))
 (if (fn-prstartup-planp plan) (nfix (fn-prstartup-nth 6 plan)) 0))

(defun fn-prstartup-status (plan)
 (declare (xargs :guard t))
 (cond ((eq (fn-prstartup-nth 0 plan) :admitted) :admitted)
       ((eq (fn-prstartup-nth 0 plan) :refused) :refused) (t :fault)))
(defun fn-prstartup-refusal-line (plan)
 (declare (xargs :guard t))
 (case (fn-prstartup-nth 1 plan)
  (:unpriced-complete-cold-profile "cold startup refused: complete cold profile is unpriced")
  (:invalid-output-resource-profile "cold startup refused: invalid output resource profile")
  (:invalid-default-pool-capture "cold startup refused: invalid runtime capture")
  (:default-pool-table-not-representable "cold startup refused: descriptor table cannot represent the runtime allowance")
  (:default-pool-headroom-unavailable "cold startup refused: fixed storage headroom unavailable")
  (otherwise "cold startup refused: unsupported resource decision")))
(defun fn-prstartup-install-status (word)
 (declare (xargs :guard t))
 (cond ((eq word :installed) :installed)
       ((member-eq word '(:already-installed :invalid-resource-mode)) :refused)
       (t :fault)))
(defun fn-prstartup-install-refusal-line (word)
 (declare (xargs :guard t))
 (case word
  (:already-installed "cold startup refused: pool is already installed")
  (:invalid-resource-mode "cold startup refused: pool entered another resource mode")
  (:invalid-resource-profile "cold startup refused: baseline is not funded")
  (:invalid-default-pool-plan "cold startup refused: invalid default backing plan")
  (otherwise "cold startup refused: unsupported installation decision")))

; Numeric startup admission is about the selected table/backing projection.
; It establishes no complete runtime/collector tariff.
(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (local (defthm fn-prstartup-capacity-stays-affordable
 (implies (and (natp lo) (natp hi) (natp fuel)
               (<= (fn-prstartup-required-heap lo workers root) (nfix available)))
  (<= (fn-prstartup-required-heap
       (fn-prstartup-affordable-capacity lo hi fuel available workers root) workers root)
      (nfix available)))
 :hints (("Goal" :induct (fn-prstartup-affordable-capacity lo hi fuel available workers root)
  :in-theory (e/d (fn-prstartup-affordable-capacity) (fn-prstartup-required-heap))))))
 (local (defthm fn-prstartup-capacity-in-range
 (implies (and (natp lo) (natp hi) (natp fuel) (<= lo hi))
  (and (natp (fn-prstartup-affordable-capacity lo hi fuel available workers root))
       (<= lo (fn-prstartup-affordable-capacity lo hi fuel available workers root))
       (<= (fn-prstartup-affordable-capacity lo hi fuel available workers root) hi)))
 :hints (("Goal" :induct (fn-prstartup-affordable-capacity lo hi fuel available workers root)
  :in-theory (e/d (fn-prstartup-affordable-capacity) (fn-prstartup-required-heap ceiling nfix))))))
(defthm fn-prstartup-admitted-capacity-is-funded
 (let ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime cache-limit fd-limit)))
  (implies (equal (fn-prstartup-nth 0 plan) :admitted)
   (and (natp (fn-prstartup-file-capacity plan))
        (<= (max 8 (+ 1 (nfix cache-limit))) (fn-prstartup-file-capacity plan))
        (<= (fn-prstartup-file-capacity plan) (nfix fd-limit))
        (<= (fn-prstartup-required-heap (fn-prstartup-file-capacity plan) workers root)
            (nfix (- (nfix dynamic) (max (nfix occupied) (nfix protected))))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-prstartup-capacity-stays-affordable
          (lo (max 8 (+ 1 (nfix cache-limit))))
          (hi (min (nfix fd-limit) (expt 2 24))) (fuel 25)
          (available (nfix (- (nfix dynamic) (max (nfix occupied) (nfix protected))))))
        (:instance fn-prstartup-capacity-in-range
          (lo (max 8 (+ 1 (nfix cache-limit))))
          (hi (min (nfix fd-limit) (expt 2 24))) (fuel 25)
          (available (nfix (- (nfix dynamic) (max (nfix occupied) (nfix protected)))))))
  :in-theory (e/d (fn-prstartup-plan fn-prstartup-nth fn-prstartup-file-capacity fn-crl-table-supportedp fn-crl-table-capacity)
      (fn-prstartup-affordable-capacity fn-prstartup-required-heap fn-prstartup-baseline-heap fn-prstartup-capacity-stays-affordable fn-prstartup-capacity-in-range)))))
)
