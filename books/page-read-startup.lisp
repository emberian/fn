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
(defun fn-prstartup-registration-reserve (files root)
 (declare (xargs :guard t))
 (* (nfix files) 2 (+ (fn-prstartup-fd-bookkeeping) 32
                     (* 4 (if (stringp root) (length root) 0)))))

(defun fn-prstartup-required-heap (files workers root)
 (declare (xargs :guard t))
 (+ (fn-prstartup-baseline-heap files workers)
    (fn-prstartup-registration-reserve files root)))

(defthm fn-prstartup-baseline-heap-natp
 (natp (fn-prstartup-baseline-heap files workers))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn-crl-table-octets fn-crl-array-octets fn-crl-align16))))

(defthm fn-prstartup-required-heap-natp
 (natp (fn-prstartup-required-heap files workers root))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn-crl-table-octets fn-crl-array-octets fn-crl-align16))))

; The heap the pool may take: past the larger of the occupied and the
; Store's protected runtime.
(defun fn-prstartup-available (dynamic occupied protected)
 (declare (xargs :guard t))
 (nfix (- (nfix dynamic) (max (nfix occupied) (nfix protected)))))

(defun fn-prstartup-affordable-capacity (lo hi fuel available workers root)
 (declare (xargs :guard (and (natp lo) (natp hi) (natp fuel))
                 :measure (nfix fuel)))
 (if (or (zp fuel) (<= hi lo)) lo
  (let ((mid (min hi (max (+ 1 lo) (nfix (ceiling (+ lo hi) 2))))))
   (if (<= (fn-prstartup-required-heap mid workers root) (nfix available))
    (fn-prstartup-affordable-capacity mid hi (1- fuel) available workers root)
    (fn-prstartup-affordable-capacity lo (1- mid) (1- fuel) available workers root)))))

; THE READS IN FLIGHT (lane pool-refusal, 2026-10-05).  Every read the pool
; admits takes one of WORKERS execution slots (fn-prs-worker-demand's slot
; coordinate; the budget's slot coordinate is WORKERS), so at most WORKERS
; reads are in flight at once; each charges its resident demand until it
; settles.  The plan keeps RESERVE octets of the available heap out of the
; descriptor table's growth so those reads fit beside it.  Before this the
; table grew into every octet the registration quantum left, and on the
; peer catch-up native (1000 posts, max-record-octets 196608) a checkpoint
; publication's second whole-segment read was refused with one in flight:
; budget 22512946, headroom under two 391756-octet reads.
;
; The largest extent a read names: one checkpoint segment written at the
; profile's max-record-octets (fn-scc-segment-max-octets: header, chunk,
; trailer); a log record's frame is smaller.
(defun fn-prstartup-read-extent (profile)
 (declare (xargs :guard t))
 (fn-scc-segment-max-octets (nfix (fn-bs-profile-max-record-octets profile))))

; A read token's integer digits at their widest: five 64-bit coordinates
; and a 256-bit trailer (books/cold-read-layout.lisp fn-crl-natural-octets).
(defun fn-prstartup-read-token-octets ()
 (declare (xargs :guard t))
 (fn-crl-token-integer-octets (1- (expt 2 64)) (1- (expt 2 64)) (1- (expt 2 64))
                              (1- (expt 2 64)) (1- (expt 2 64)) (1- (expt 2 256))))

; One read's resident charge at EXTENT octets: what fn-owner-page-read-admit
; and -discovery-admit charge (host/page-read-host.lisp) with the installed
; pool's bookkeeping and native octets, both 0 (fn-prstartup-plan's fourth
; field and fn-owner-page-read-install-baseline), and the widest token.
(defun fn-prstartup-read-demand (extent)
 (declare (xargs :guard t))
 (nfix (car (fn-prs-worker-demand extent (fn-prstartup-read-token-octets) 0 0))))

(defun fn-prstartup-read-reserve (extent workers)
 (declare (xargs :guard t))
 (* (nfix workers) (fn-prstartup-read-demand extent)))

(defun fn-prstartup-plan (dynamic occupied protected root workers stack runtime cache-limit fd-limit reserve)
 (declare (xargs :guard t))
 (let* ((available (fn-prstartup-available dynamic occupied protected))
        (minimum (max 8 (+ 1 (nfix cache-limit))))
        (native (* (nfix workers) (+ (nfix stack) (nfix runtime)))))
  (cond
   ((not (and (natp dynamic) (natp occupied) (natp protected) (stringp root)
              (posp workers) (natp stack) (natp runtime) (natp cache-limit) (natp fd-limit)
              (natp reserve) (<= occupied dynamic)))
    (list :refused :invalid-default-pool-capture))
   ; A well-formed capture whose process heap is smaller than the Store's
   ; protected runtime: the process was started below its launcher figure.
   ((not (<= protected dynamic))
    (list :refused :default-pool-heap-not-held))
   ((not (and (<= minimum fd-limit) (fn-crl-table-supportedp minimum)))
    (list :refused :default-pool-table-not-representable))
   ((not (<= (fn-prstartup-required-heap minimum workers root) available))
    (list :refused :default-pool-headroom-unavailable))
   ((not (<= (+ (fn-prstartup-required-heap minimum workers root) reserve) available))
    (list :refused :default-pool-read-headroom-unavailable))
   (t
    (let* ((files (fn-prstartup-affordable-capacity minimum (min (nfix fd-limit) (expt 2 24)) 25
                                                    (nfix (- available reserve)) workers root))
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

; OBSERVED: the store on disk, as the launcher's figure observed it.
(defun fn-prstartup-protected (profile core nursery output max-connections observed)
 (declare (xargs :guard t) (ignore max-connections))
 (+ (fn-heap-runtime-protected-octets profile core nursery observed)
    (nfix (fn-crv-nth 0 output))))

(defun fn-prstartup-default-plan
  (dynamic occupied profile core nursery cold output max-connections root workers cache-limit fd-limit
   observed)
 (declare (xargs :guard t))
 (cond (cold (list :refused :unpriced-complete-cold-profile))
       ((not (or (not output) (fn-orv-policy-p output)))
        (list :refused :invalid-output-resource-profile))
       (t (fn-prstartup-plan dynamic occupied
            (fn-prstartup-protected profile core nursery output max-connections observed)
            root workers (fn-heap-stack-octets profile)
            *fn-heap-thread-runtime-octets* cache-limit fd-limit
            (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers)))))

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
  (:default-pool-heap-not-held "cold startup refused: the process heap does not hold the store's protected runtime")
  (:default-pool-table-not-representable "cold startup refused: descriptor table cannot represent the runtime allowance")
  (:default-pool-headroom-unavailable "cold startup refused: fixed storage headroom unavailable")
  (:default-pool-read-headroom-unavailable "cold startup refused: the read pool cannot hold its workers' reads in flight")
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
 (local (defthm fn-prstartup-capacity-stays-affordable
 (implies (and (natp lo) (natp hi) (natp fuel)
               (<= (fn-prstartup-required-heap lo workers root) (nfix available)))
  (<= (fn-prstartup-required-heap
       (fn-prstartup-affordable-capacity lo hi fuel available workers root) workers root)
      (nfix available)))
 :hints (("Goal" :induct (fn-prstartup-affordable-capacity lo hi fuel available workers root)
  :in-theory (e/d (fn-prstartup-affordable-capacity) (fn-prstartup-required-heap ceiling min max))))))
 (local (defthm fn-prstartup-capacity-in-range
 (implies (and (natp lo) (natp hi) (natp fuel) (<= lo hi))
  (and (natp (fn-prstartup-affordable-capacity lo hi fuel available workers root))
       (<= lo (fn-prstartup-affordable-capacity lo hi fuel available workers root))
       (<= (fn-prstartup-affordable-capacity lo hi fuel available workers root) hi)))
 :hints (("Goal" :induct (fn-prstartup-affordable-capacity lo hi fuel available workers root)
  :in-theory (e/d (fn-prstartup-affordable-capacity) (fn-prstartup-required-heap ceiling nfix))))))
; An admitted plan, unfolded once: every later fact is read off this.
(defthm fn-prstartup-plan-when-admitted
 (let ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                cache-limit fd-limit reserve)))
  (implies (equal (fn-prstartup-nth 0 plan) :admitted)
   (let* ((available (fn-prstartup-available dynamic occupied protected))
          (minimum (max 8 (+ 1 (nfix cache-limit))))
          (native (* workers (+ stack runtime)))
          (files (fn-prstartup-affordable-capacity minimum (min fd-limit (expt 2 24)) 25
                                                   (nfix (- available reserve)) workers root)))
    (and (natp dynamic) (natp occupied) (natp protected) (stringp root)
         (posp workers) (natp stack) (natp runtime) (natp cache-limit) (natp fd-limit)
         (natp reserve)
         (<= minimum fd-limit) (fn-crl-table-supportedp minimum)
         (<= (+ (fn-prstartup-required-heap minimum workers root) reserve) available)
         (equal plan
                (list :admitted
                      (list (+ available native) 0 files workers 18446744073709551615)
                      (list (+ (fn-prstartup-baseline-heap files workers) native) 0 0 0 0)
                      0 (fn-prstartup-fd-bookkeeping) 18446744073709551615
                      workers (fn-cgb-capacity)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-prstartup-plan fn-prstartup-nth)
                                 (fn-prstartup-affordable-capacity fn-prstartup-baseline-heap
                                  fn-prstartup-required-heap fn-prstartup-available
                                  fn-crl-table-supportedp fn-cgb-capacity)))))

(defthm fn-prstartup-admitted-capacity-is-funded
 (let ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime cache-limit fd-limit reserve)))
  (implies (equal (fn-prstartup-nth 0 plan) :admitted)
   (and (natp (fn-prstartup-file-capacity plan))
        (<= (max 8 (+ 1 (nfix cache-limit))) (fn-prstartup-file-capacity plan))
        (<= (fn-prstartup-file-capacity plan) (nfix fd-limit))
        (<= (+ (fn-prstartup-required-heap (fn-prstartup-file-capacity plan) workers root) reserve)
            (fn-prstartup-available dynamic occupied protected)))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-prstartup-plan-when-admitted)
        (:instance fn-prstartup-capacity-stays-affordable
          (lo (max 8 (+ 1 (nfix cache-limit))))
          (hi (min fd-limit (expt 2 24))) (fuel 25)
          (available (nfix (- (fn-prstartup-available dynamic occupied protected) reserve))))
        (:instance fn-prstartup-capacity-in-range
          (lo (max 8 (+ 1 (nfix cache-limit))))
          (hi (min fd-limit (expt 2 24))) (fuel 25)
          (available (nfix (- (fn-prstartup-available dynamic occupied protected) reserve)))))
  :in-theory (e/d (fn-prstartup-nth fn-prstartup-file-capacity fn-crl-table-supportedp
                   fn-crl-table-capacity)
      (fn-prstartup-plan fn-prstartup-affordable-capacity fn-prstartup-required-heap
       fn-prstartup-baseline-heap fn-prstartup-capacity-stays-affordable
       fn-prstartup-available fn-prstartup-capacity-in-range)))))

; KEYSTONE (lane pool-refusal): an admitted plan's resident budget holds,
; beyond its installed baseline, the registration quantum of every file the
; table admits and RESERVE -- for the default plan, WORKERS reads of the
; profile's largest extent (fn-prstartup-read-reserve).  Scope: the plan's
; own coordinates; the launched heap's room for it is the launcher's
; extension below (fn-prstartup-extend-default-reservation adds it).
(defthm fn-prstartup-plan-holds-the-reads-in-flight
 (let* ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime cache-limit fd-limit reserve))
        (budget (fn-prstartup-nth 1 plan))
        (used (fn-prstartup-nth 2 plan)))
  (implies (equal (fn-prstartup-nth 0 plan) :admitted)
           (<= (+ (fn-prstartup-nth 0 used)
                  (fn-prstartup-registration-reserve (fn-prstartup-file-capacity plan) root)
                  reserve)
               (fn-prstartup-nth 0 budget))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-prstartup-plan-when-admitted)
        (:instance fn-prstartup-admitted-capacity-is-funded))
  :in-theory (e/d (fn-prstartup-nth fn-prstartup-file-capacity fn-prstartup-required-heap)
                  (fn-prstartup-plan fn-prstartup-affordable-capacity fn-prstartup-baseline-heap
                   fn-prstartup-available fn-prstartup-registration-reserve)))))

(defthm fn-prstartup-admitted-plan-shape
 (let ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime cache-limit fd-limit reserve)))
  (implies (equal (fn-prstartup-nth 0 plan) :admitted)
           (and (equal (fn-prstartup-nth 1 plan)
                       (list (fn-prstartup-nth 0 (fn-prstartup-nth 1 plan)) 0
                             (fn-prstartup-file-capacity plan) workers 18446744073709551615))
                (equal (fn-prstartup-nth 2 plan)
                       (list (fn-prstartup-nth 0 (fn-prstartup-nth 2 plan)) 0 0 0 0))
                (natp (fn-prstartup-nth 0 (fn-prstartup-nth 1 plan)))
                (natp (fn-prstartup-nth 0 (fn-prstartup-nth 2 plan)))
                (natp (fn-prstartup-file-capacity plan))
                (posp workers))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-prstartup-plan-when-admitted)
                       (:instance fn-prstartup-admitted-capacity-is-funded))
                 :in-theory (e/d (fn-prstartup-nth fn-prstartup-file-capacity)
                                 (fn-prstartup-plan fn-prstartup-affordable-capacity
                                  fn-prstartup-baseline-heap fn-prstartup-required-heap
                                  fn-prstartup-available)))))

; The admission arithmetic: one more read fits when a slot is free.
(defthm fn-prstartup-one-more-slot
 (implies (and (natp a) (natp b) (natp d) (< a b))
          (<= (+ (* a d) d) (* b d)))
 :rule-classes nil
 :hints (("Goal" :nonlinearp t)))

; fn-prs-issue over five-coordinate vectors, coordinate by coordinate.
(defthm fn-prstartup-issue-admits
 (implies (and (natp b0) (natp f) (natp w) (natp l) (natp u0)
               (natp c0) (natp c1) (natp c2) (natp c3) (natp c4) (natp d0)
               (<= (+ u0 c0) b0) (<= c1 0) (<= c2 f) (<= c3 w) (<= c4 l)
               (<= (+ u0 c0 d0) b0) (< c3 w) (< c4 l)
               (natp next) (natp limit) (< next limit))
          (equal (mv-nth 0 (fn-prs-issue (list b0 0 f w l) (list u0 0 0 0 0) '(0 0 0 0 0)
                                         (list c0 c1 c2 c3 c4) next limit
                                         (list d0 0 0 1 1)))
                 :admitted))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-prs-issue fn-prs-fundedp fn-prs-plus fn-prs-below
                                    fn-prs-vectorp fn-prs-nats-p))))

(defthm fn-prstartup-issue-admits-within-the-reserve
 (implies (and (equal budget (list b0 0 f w l)) (equal used (list u0 0 0 0 0))
               (equal demand (list d0 0 0 1 1))
               (natp b0) (natp f) (natp w) (natp l) (natp u0) (natp d0) (natp r) (natp d)
               (natp c0) (natp c1) (natp c2) (natp c3) (natp c4)
               (fn-prs-fundedp budget used '(0 0 0 0 0) (list c0 c1 c2 c3 c4))
               (<= (+ u0 r (* w d)) b0)
               (< c3 w) (<= c0 (+ r (* c3 d))) (<= d0 d) (< c4 l)
               (natp next) (natp limit) (< next limit))
          (equal (mv-nth 0 (fn-prs-issue budget used '(0 0 0 0 0) (list c0 c1 c2 c3 c4)
                                         next limit demand))
                 :admitted))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-prstartup-issue-admits)
                       (:instance fn-prstartup-one-more-slot (a c3) (b w)))
                 :in-theory (e/d (fn-prs-fundedp fn-prs-plus fn-prs-below fn-prs-vectorp fn-prs-nats-p)
                                 (fn-prs-issue)))))


; KEYSTONE (lane pool-refusal): what the reserve buys.  Over the admitted
; default-shaped plan (RESERVE = WORKERS reads of EXTENT), a pool whose
; charge is its registrations within their quantum and one read of at most
; EXTENT per slot in use -- the caches having yielded their charge
; (host/native/extent.lisp fnn-extent-cache-yield-oldest) -- admits one more
; read of at most EXTENT octets whenever a slot is free: the pool's octets
; never refuse it (fn-prs-issue, the admission both fn-owner-page-read-admit
; and -discovery-admit run).  Teeth (tests/acl2/page-read-startup-tests.lisp):
; the plan without the reserve, at the catch-up native's figures, refuses
; the second read with one in flight.
(defthm fn-prstartup-reserve-admits-a-read
 (let* ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                 cache-limit fd-limit (fn-prstartup-read-reserve extent workers)))
        (budget (fn-prstartup-nth 1 plan))
        (used (fn-prstartup-nth 2 plan)))
  (implies (and (equal (fn-prstartup-nth 0 plan) :admitted)
                (natp c0) (natp c1) (natp c2) (natp c3) (natp c4)
                (fn-prs-fundedp budget used '(0 0 0 0 0) (list c0 c1 c2 c3 c4))
                (< c3 workers)
                (<= c0 (+ (fn-prstartup-registration-reserve (fn-prstartup-file-capacity plan) root)
                          (* c3 (fn-prstartup-read-demand extent))))
                (< c4 18446744073709551615)
                (natp extent) (natp elen) (<= elen extent)
                (natp tok) (<= tok (fn-prstartup-read-token-octets))
                (natp next) (natp limit) (< next limit))
           (equal (mv-nth 0 (fn-prs-issue budget used '(0 0 0 0 0) (list c0 c1 c2 c3 c4) next limit
                                          (fn-prs-worker-demand elen tok 0 0)))
                  :admitted)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-prstartup-plan-holds-the-reads-in-flight
          (reserve (fn-prstartup-read-reserve extent workers)))
        (:instance fn-prstartup-admitted-plan-shape
          (reserve (fn-prstartup-read-reserve extent workers)))
        (:instance fn-prstartup-issue-admits-within-the-reserve
          (budget (fn-prstartup-nth 1 (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                 cache-limit fd-limit (fn-prstartup-read-reserve extent workers))))
          (used (fn-prstartup-nth 2 (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                 cache-limit fd-limit (fn-prstartup-read-reserve extent workers))))
          (demand (fn-prs-worker-demand elen tok 0 0))
          (b0 (fn-prstartup-nth 0 (fn-prstartup-nth 1 (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                 cache-limit fd-limit (fn-prstartup-read-reserve extent workers)))))
          (u0 (fn-prstartup-nth 0 (fn-prstartup-nth 2 (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                 cache-limit fd-limit (fn-prstartup-read-reserve extent workers)))))
          (f (fn-prstartup-file-capacity (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                 cache-limit fd-limit (fn-prstartup-read-reserve extent workers))))
          (w workers) (l 18446744073709551615)
          (d0 (* 2 (+ elen 32 tok)))
          (r (fn-prstartup-registration-reserve (fn-prstartup-file-capacity (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                 cache-limit fd-limit (fn-prstartup-read-reserve extent workers))) root))
          (d (fn-prstartup-read-demand extent))))
  :in-theory (e/d (fn-prs-worker-demand fn-prstartup-read-reserve fn-prstartup-read-demand)
                  (fn-prstartup-plan fn-prstartup-registration-reserve fn-prs-issue fn-prs-fundedp
                   fn-prstartup-file-capacity fn-prstartup-read-token-octets)))))
)

; Named equality bridge from the actual native subject to the numerical core.
; This definitional bridge is not a separate funding keystone.
(defthm fn-prstartup-default-plan-refines-plan-by-definition
 (equal (fn-prstartup-default-plan dynamic occupied profile core nursery cold output
                                   max-connections root workers cache-limit fd-limit observed)
        (cond (cold (list :refused :unpriced-complete-cold-profile))
              ((not (or (not output) (fn-orv-policy-p output)))
               (list :refused :invalid-output-resource-profile))
              (t (fn-prstartup-plan dynamic occupied
                   (fn-prstartup-protected profile core nursery output max-connections observed)
                   root workers (fn-heap-stack-octets profile)
                   *fn-heap-thread-runtime-octets* cache-limit fd-limit
                   (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers)))))
 :hints (("Goal" :in-theory (union-theories '(fn-prstartup-default-plan) (theory 'minimal-theory)))))

; DEFAULT's fixed backing is a real launcher contribution. The existing base
; already reserves its direct-worker threads; add only the selected heap
; minimum, before the independent explicit output contribution.
;
; The launched owner checks the Store's protected runtime against its own
; heap (fn-prstartup-protected) over ITS image observation, while the base
; figure was solved over the probe's: each is the calling process's dynamic
; usage, and the owner's is the larger (scenarios-2, set 6107ceb56: 23 of 23
; installed starts refused).  So the served run's figure is first raised to
; the protected runtime at the image FILE's bound, an observation every
; process of the image shares and no dynamic usage exceeds
; (fn-heap-core-dynamic-is-at-most-the-file), for the store the probe
; OBSERVED (PROFILE, OBSERVED: the base decision's own arguments).
(defun fn-prstartup-image-bound (core)
 (declare (xargs :guard t))
 (cons (fn-heap-core-file core) (fn-heap-core-file core)))

(defun fn-prstartup-launch-floor (profile core observed)
 (declare (xargs :guard t))
 (fn-heap-with-nursery
  (fn-heap-store-base-octets profile (fn-prstartup-image-bound core) observed)
  (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))

; What the served run adds to its figure for the pool: the smallest table
; the plan admits and its workers' reads in flight (the plan's two checks,
; fn-prstartup-plan).
(defun fn-prstartup-launch-extra (profile workers cache-limit root)
 (declare (xargs :guard t))
 (+ (fn-prstartup-required-heap (max 8 (+ 1 (nfix cache-limit))) workers root)
    (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers)))

(defun fn-prstartup-extend-default-reservation
 (base cold root workers cache-limit core observations profile observed)
 (declare (xargs :guard t))
 (cond (cold base)
       ((not (eq (fn-prstartup-nth 0 base) :heap)) base)
       ((not (and (stringp root) (posp workers) (natp cache-limit)
                  (fn-crl-table-supportedp (max 8 (+ 1 cache-limit)))))
        (list :refused :invalid-default-pool-capture 0 (fn-prstartup-nth 3 base)))
       (t
        (let* ((octets (fn-heap-grow-runtime-dynamic
                          (max (* *fn-heap-mib* (nfix (fn-prstartup-nth 1 base)))
                               (fn-prstartup-launch-floor profile core observed))
                          (fn-prstartup-launch-extra profile workers cache-limit root)
                          (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))
               (mb (fn-heap-mb-of octets))
               (stack (nfix (fn-prstartup-nth 4 base)))
               (threads (nfix (fn-prstartup-nth 5 base)))
               (total (fn-heap-reservation-octets mb core stack threads)))
         (if (<= total (fn-heap-machine-octets observations))
             (list :heap mb (fn-prstartup-nth 2 base) (fn-prstartup-nth 3 base) stack threads)
           (list :refused :machine-cannot-hold-threads (fn-heap-mb-of total)
                 (fn-prstartup-nth 3 base)))))))

(defthm fn-prstartup-nursery-trigger-at-least-the-least
 (<= *fn-heap-nursery-least-octets* (fn-heap-nursery-trigger d nursery))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-heap-nursery-trigger))))

(defthm fn-prstartup-launch-floor-holds-owner
 (implies (and (natp dyn)
               (<= (fn-prstartup-launch-floor profile core observed) dyn)
               (equal (fn-heap-core-file owner-core) (fn-heap-core-file core)))
          (<= (fn-prstartup-protected
               profile owner-core
               (fn-heap-nursery-trigger dyn (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))
               nil max-connections observed)
              dyn))
 :rule-classes nil
 :hints (("Goal"
          :in-theory (e/d (fn-prstartup-protected fn-heap-runtime-protected-octets
                           fn-prstartup-launch-floor fn-prstartup-image-bound
                           fn-heap-store-base-octets fn-heap-core-dynamic fn-heap-core-file)
                          (fn-heap-with-nursery fn-heap-nursery-trigger
                           fn-heap-store-state-bound fn-heap-store-open-octets
                           fn-heap-open-octets-bound fn-heap-open-records-bound
                           fn-heap-store-inflight-octets fn-heap-articles-octets))
          :use ((:instance fn-heap-with-nursery-monotone
                 (b1 (fn-heap-store-base-octets profile owner-core observed))
                 (b2 (fn-heap-store-base-octets profile (fn-prstartup-image-bound core) observed))
                 (nursery (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))
                (:instance fn-heap-with-nursery-holds-the-trigger
                 (d dyn)
                 (base (fn-heap-store-base-octets profile owner-core observed))
                 (nursery (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))))))

(defthm fn-prstartup-extended-covers-launch-floor
 (let ((d (fn-prstartup-extend-default-reservation base nil root workers cache-limit
                                                    core observations profile observed)))
  (implies (equal (fn-prstartup-nth 0 d) :heap)
           (and (natp (* *fn-heap-mib* (fn-prstartup-nth 1 d)))
                (<= (fn-prstartup-launch-floor profile core observed)
                    (* *fn-heap-mib* (fn-prstartup-nth 1 d))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-prstartup-extend-default-reservation fn-prstartup-nth)
                                 (fn-prstartup-launch-floor fn-heap-grow-runtime-dynamic
                                  fn-prstartup-required-heap fn-prstartup-launch-extra
                                  fn-heap-reservation-octets
                                  fn-heap-machine-octets fn-crl-table-supportedp fn-heap-mb-of))
          :use ((:instance fn-heap-grow-runtime-dynamic-covers-addition
                 (dynamic (max (* *fn-heap-mib* (nfix (fn-prstartup-nth 1 base)))
                               (fn-prstartup-launch-floor profile core observed)))
                 (extra (fn-prstartup-launch-extra profile workers cache-limit root))
                 (nursery-cap (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))
                (:instance fn-heap-mb-of-covers
                 (octets (fn-heap-grow-runtime-dynamic
                          (max (* *fn-heap-mib* (nfix (fn-prstartup-nth 1 base)))
                               (fn-prstartup-launch-floor profile core observed))
                          (fn-prstartup-launch-extra profile workers cache-limit root)
                          (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))))))))

; KEYSTONE: the launcher's served-run figure admits the launched owner's
; protected-runtime check, for every store the probe observed and every
; image observation the owner takes of the same core file, at the collector
; trigger the owner sets in that heap (host/native/io.lisp
; fnn-gc-nursery-octets).  Scope: absent explicit cold and output policies
; and no peer flight profile (those compose their own allowances).
(defthm fn-prstartup-launch-admits-owner-protected
 (let* ((d (fn-prstartup-extend-default-reservation base nil root workers cache-limit
                                                     core observations profile observed))
        (dyn (* *fn-heap-mib* (fn-prstartup-nth 1 d))))
  (implies (and (equal (fn-prstartup-nth 0 d) :heap)
                (equal (fn-heap-core-file owner-core) (fn-heap-core-file core)))
           (<= (fn-prstartup-protected
                profile owner-core
                (fn-heap-nursery-trigger dyn (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))
                nil max-connections observed)
               dyn)))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-heap-with-nursery fn-heap-grow-runtime-dynamic
                                     fn-heap-store-base-octets fn-prstartup-required-heap fn-prstartup-launch-extra
                                     fn-heap-reservation-octets fn-heap-machine-octets
                                     fn-crl-table-supportedp fn-heap-nursery-trigger)
          :use ((:instance fn-prstartup-extended-covers-launch-floor)
                (:instance fn-prstartup-launch-floor-holds-owner
                 (dyn (* *fn-heap-mib* (fn-prstartup-nth 1
                        (fn-prstartup-extend-default-reservation base nil root workers cache-limit
                                                                 core observations profile observed)))))))))

(defthm fn-prstartup-accepted-default-launch-fits-machine
 (implies (and (not cold)
               (equal (fn-prstartup-nth 0
                        (fn-prstartup-extend-default-reservation base cold root workers cache-limit core observations profile observed)) :heap))
  (let ((d (fn-prstartup-extend-default-reservation base cold root workers cache-limit core observations profile observed)))
   (<= (fn-heap-reservation-octets (fn-prstartup-nth 1 d) core
                                  (fn-prstartup-nth 4 d) (fn-prstartup-nth 5 d))
       (fn-heap-machine-octets observations))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-prstartup-extend-default-reservation fn-prstartup-nth)
                          (fn-heap-mb-of fn-heap-machine-octets fn-heap-reservation-octets
                           fn-prstartup-required-heap fn-prstartup-launch-extra fn-crl-table-supportedp
                           fn-prstartup-launch-floor fn-heap-grow-runtime-dynamic)))))

(defun fn-prstartup-extend-operation-reservation
 (base action cold root workers cache-limit core observations profile observed)
 (declare (xargs :guard t))
 (if (eq action :run)
     (fn-prstartup-extend-default-reservation base cold root workers cache-limit core observations profile observed)
   base))

(defthm fn-prstartup-operation-extension-refines-default-by-definition
 (equal (fn-prstartup-extend-operation-reservation base action cold root workers cache-limit core observations profile observed)
        (if (eq action :run)
            (fn-prstartup-extend-default-reservation base cold root workers cache-limit core observations profile observed)
          base))
 :hints (("Goal" :in-theory (e/d (fn-prstartup-extend-operation-reservation)
                               (fn-prstartup-extend-default-reservation)))))
