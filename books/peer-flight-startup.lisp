; Composition of independent peer authority with the real DEFAULT pool.
(in-package "ACL2")
(include-book "page-read-startup")
(include-book "peer-flight-reservation")
(include-book "heap-command")

(defun fn-prstartup-protected-with-peer (profile core nursery output max-connections peer observed)
 (declare (xargs :guard t))
 (+ (fn-prstartup-protected profile core nursery output max-connections observed)
    (if (fn-pfr-policy-p peer) (nfix (fn-pfr-at 0 peer)) 0)))

; THE SERVED RUN'S PROTECTED RUNTIME (L-RUN-LAUNCH).  The store's runtime heap has two bounds: the
; profile's whole store (fn-prstartup-protected: every store the profile admits) and the run's launch
; (fn-mm-launch-dynamic: the core's content and the resident LIMIT the memory gate keeps every
; admitted store within, books/heap-command.lisp fn-mo-serve-holds-every-admitted-store).  The owner
; protects the smaller, each with the output pool's heap.  LIMIT is the configure's (the least
; resident observation less the pools, fn-mo-serve-limit); with no resident observation only the
; profile's bound remains.  The launcher's figure holds it (fn-mo-serve-startup-admits-the-pool).
(defun fn-prstartup-serve-limit (profile output peer workers cache-limit root resident)
 (declare (xargs :guard t))
 (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)))

(defun fn-prstartup-serve-protected (profile core nursery output max-connections observed limit)
 (declare (xargs :guard t))
 (let ((bound (fn-prstartup-protected profile core nursery output max-connections observed)))
  (if (natp limit)
      (min bound (+ (fn-mm-launch-dynamic limit core nursery) (nfix (fn-crv-nth 0 output))))
    bound)))

(defun fn-prstartup-default-plan-with-peer
 (dynamic occupied profile core nursery cold output max-connections root workers cache-limit fd-limit peer
  observed resident)
 (declare (xargs :guard t))
 (cond ((and peer (not (fn-pfr-policy-p peer))) (list :refused :invalid-peer-flight-profile))
       (cold (list :refused :unpriced-complete-cold-profile))
       ((not (or (not output) (fn-orv-policy-p output)))
        (list :refused :invalid-output-resource-profile))
       (t (fn-prstartup-plan dynamic occupied
              (+ (fn-prstartup-serve-protected
                  profile core nursery output max-connections observed
                  (fn-prstartup-serve-limit profile output peer workers cache-limit root resident))
                 (if peer (nfix (fn-pfr-at 0 peer)) 0))
              root workers (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*
              cache-limit fd-limit
              (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers)))))

; Pool budget includes native bytes already reserved outside the heap.
; Its remaining heap allowance is exclusive of the peer heap slice.
(defun fn-prstartup-peer-protected (profile core nursery output max-connections plan observed limit)
 (declare (xargs :guard t))
 (+ (fn-prstartup-serve-protected profile core nursery output max-connections observed limit)
    (nfix (- (nfix (fn-prstartup-nth 0 (fn-prstartup-nth 1 plan)))
             (* (fn-prstartup-decoded-workers plan)
                (+ (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*))))))
(defun fn-pfr-operation-observes-p (action)
 (declare (xargs :guard t)) (eq action :run))
(defun fn-prstartup-peer-grant (dynamic profile core nursery output max-connections plan peer observed limit)
 (declare (xargs :guard t))
 (if (not (fn-prstartup-planp plan)) (list :refused :default-pool-not-held)
   (fn-pfr-startup-grant dynamic
     (fn-prstartup-peer-protected profile core nursery output max-connections plan observed limit) peer)))

; Carry this exact parent capture until the retained service publishes its bank.
(defun fn-prstartup-peer-native-capture
 (dynamic profile core nursery output max-connections plan peer observed limit)
 (declare (xargs :guard t))
 (if (not (eq (fn-pfr-at 0 (fn-prstartup-peer-grant dynamic profile core nursery
                              output max-connections plan peer observed limit)) :hold)) nil
   (list dynamic
         (fn-prstartup-peer-protected profile core nursery output max-connections plan observed limit)
         peer (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*)))

; Revalidate the current file capture against the whole native reservation.
; A file changed after launch cannot obtain extra unfunded worker authority.
; ADDRESS: the address-space observations (RLIMIT_DATA, RLIMIT_AS), the only
; limits a reservation is compared with (L-RUN-LAUNCH: memory.max and physical
; memory bound resident memory, which the memory gate keeps within LIMIT).
(defun fn-prstartup-peer-native-grant
 (dynamic profile core nursery output max-connections plan peer address observed
  workers cache-limit root resident)
 (declare (xargs :guard t))
 (let* ((limit (fn-prstartup-serve-limit profile output peer workers cache-limit root resident))
        (grant (fn-prstartup-peer-grant dynamic profile core nursery output
                                        max-connections plan peer observed limit))
        (addr (fn-mm-least-observation address)))
  (if (not (eq (fn-pfr-at 0 grant) :hold)) grant
    (if (and (natp addr)
             (< addr
                (fn-heap-reservation-octets (fn-heap-mb-of dynamic) core
                  (fn-heap-stack-kib profile)
                  (+ (fn-heap-thread-count max-connections) (nfix (fn-pfr-at 3 peer))))))
        (list :refused :peer-native-reservation-not-held)
      (list :hold (fn-prstartup-peer-native-capture dynamic profile core nursery output
                                                  max-connections plan peer observed limit))))))

(defun fn-prstartup-peer-native-refusal-line (grant)
 (declare (xargs :guard t))
 (case (fn-pfr-at 1 grant)
  (:peer-native-reservation-not-held "Peer flight startup refused: native worker reservation is not held.")
  (:peer-flight-pool-not-held "Peer flight startup refused: independent pool is not held.")
  (:invalid-peer-flight-profile "Peer flight startup refused: invalid resource profile.")
  (:default-pool-not-held "Peer flight startup refused: parent DEFAULT pool is not held.")
  (otherwise "Peer flight startup refused: unsupported resource allowance.")))

; The served run's protected runtime is within the profile's: protecting the smaller of the two
; bounds never asks the heap for more than the profile's bound alone did.
(defthm fn-prstartup-serve-protected-within-the-profile-bound
 (<= (fn-prstartup-serve-protected profile core nursery output max-connections observed limit)
     (fn-prstartup-protected profile core nursery output max-connections observed))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-prstartup-serve-protected) (fn-prstartup-protected fn-mm-launch-dynamic)))))

; THE ARITHMETIC OF K-L4.  The owner's protected runtime, at the collector trigger it sets in the
; probe's dynamic space, is within the launch the probe decided; the plan then has the room.
(defthm fn-mo-serve-with-nursery-monotone-in-the-cap
  (implies (<= (max *fn-heap-nursery-least-octets* (nfix n1))
               (max *fn-heap-nursery-least-octets* (nfix n2)))
           (<= (fn-heap-with-nursery b n1) (fn-heap-with-nursery b n2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-with-nursery))))

(defthm fn-mo-serve-nursery-trigger-within-the-cap
  (<= (max *fn-heap-nursery-least-octets* (nfix (fn-heap-nursery-trigger d n)))
      (max *fn-heap-nursery-least-octets* (nfix n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-nursery-trigger))))

(defthm fn-mo-serve-launch-dynamic-monotone
  (implies (and (<= (nfix l1) (nfix l2))
                (<= (fn-heap-core-dynamic c1) (fn-heap-core-dynamic c2))
                (<= (max *fn-heap-nursery-least-octets* (nfix n1))
                    (max *fn-heap-nursery-least-octets* (nfix n2))))
           (<= (fn-mm-launch-dynamic l1 c1 n1) (fn-mm-launch-dynamic l2 c2 n2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mm-launch-dynamic) (fn-heap-with-nursery fn-heap-core-dynamic))
           :use ((:instance fn-heap-with-nursery-monotone
                  (b1 (+ (fn-heap-core-dynamic c1) (nfix l1)))
                  (b2 (+ (fn-heap-core-dynamic c2) (nfix l2)))
                  (nursery n1))
                 (:instance fn-mo-serve-with-nursery-monotone-in-the-cap
                  (b (+ (fn-heap-core-dynamic c2) (nfix l2))))))))

(defthm fn-mo-serve-protected-within-the-launch
  (implies (natp limit)
           (<= (fn-prstartup-serve-protected profile core nursery output max-connections observed limit)
               (+ (fn-mm-launch-dynamic limit core nursery) (nfix (fn-crv-nth 0 output)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prstartup-serve-protected) (fn-prstartup-protected fn-mm-launch-dynamic)))))

(defthm fn-mo-serve-affordable-capacity-in-range
  (implies (and (natp lo) (natp hi) (natp fuel) (<= lo hi))
           (and (natp (fn-prstartup-affordable-capacity lo hi fuel available workers root))
                (<= lo (fn-prstartup-affordable-capacity lo hi fuel available workers root))
                (<= (fn-prstartup-affordable-capacity lo hi fuel available workers root) hi)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-prstartup-affordable-capacity lo hi fuel available workers root)
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-prstartup-affordable-capacity)))))

(defthm fn-mo-serve-minimum-in-range
  (implies (and (natp c) (natp fd) (<= (max 8 (+ 1 c)) fd) (fn-crl-table-supportedp (max 8 (+ 1 c))))
           (<= (max 8 (+ 1 c)) (min fd (expt 2 24))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-crl-table-supportedp fn-crl-table-capacity))))

(defthm fn-mo-serve-table-supported-within-range
  (implies (and (natp f) (<= f (expt 2 24))) (fn-crl-table-supportedp f))
  :hints (("Goal" :in-theory (enable fn-crl-table-supportedp fn-crl-table-capacity))))

(defthm fn-mo-serve-table-supported-within-range
  (implies (and (natp f) (<= f (expt 2 24))) (fn-crl-table-supportedp f))
  :hints (("Goal" :in-theory (enable fn-crl-table-supportedp fn-crl-table-capacity))))

(defthm fn-mo-serve-capacity-stays-affordable
  (implies (and (natp lo) (natp hi) (natp fuel)
                (<= (fn-prstartup-required-heap lo workers root) (nfix available)))
           (<= (fn-prstartup-required-heap
                (fn-prstartup-affordable-capacity lo hi fuel available workers root) workers root)
               (nfix available)))
  :hints (("Goal" :induct (fn-prstartup-affordable-capacity lo hi fuel available workers root)
           :in-theory (union-theories (theory 'ground-zero)
                                      '(fn-prstartup-affordable-capacity)))))

(defthm fn-mo-serve-held-list-is-planp
  (implies (and (equal plan (list :admitted
                                  (list (+ avail native) 0 f w 18446744073709551615)
                                  (list (+ (fn-prstartup-baseline-heap f w) native) 0 0 0 0)
                                  0 (fn-prstartup-fd-bookkeeping) 18446744073709551615 w (fn-cgb-capacity)))
                (natp avail) (natp native) (posp w) (natp f) (<= 8 f) (<= f 16777216)
                (<= (fn-prstartup-baseline-heap f w) avail))
           (and (fn-prstartup-planp plan)
                (equal (fn-prstartup-decoded-workers plan) w)
                (equal (fn-prstartup-nth 0 (fn-prstartup-nth 1 plan)) (+ avail native))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prstartup-planp fn-prstartup-decoded-workers fn-prstartup-nth
                                   fn-prstartup-file-capacity fn-prstartup-baseline-heap-natp)
                                  (fn-prstartup-baseline-heap fn-crl-table-supportedp fn-cgb-capacity
                                   fn-prstartup-fd-bookkeeping))
           :use ((:instance fn-mo-serve-table-supported-within-range)
                 (:instance fn-prstartup-baseline-heap-natp (files f) (workers w))))))

(defthm fn-mo-serve-affordable-capacity-funded
  (implies (and (natp lo) (natp hi) (<= lo hi) (natp reserve) (natp fuel) (integerp available)
                (<= (+ (fn-prstartup-required-heap lo workers root) reserve) available))
           (let ((files (fn-prstartup-affordable-capacity lo hi fuel (nfix (- available reserve))
                                                          workers root)))
             (and (natp files) (<= lo files) (<= files hi)
                  (<= (+ (fn-prstartup-required-heap files workers root) reserve) available))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-mo-serve-capacity-stays-affordable
                         (available (nfix (- available reserve))))
                        (:instance fn-mo-serve-affordable-capacity-in-range
                         (available (nfix (- available reserve))))
                        (:instance fn-prstartup-required-heap-natp (files lo)))
           :in-theory (disable fn-prstartup-required-heap fn-prstartup-affordable-capacity
                               fn-mo-serve-capacity-stays-affordable))))

(defthm fn-mo-serve-baseline-within-required
  (<= (fn-prstartup-baseline-heap files workers) (fn-prstartup-required-heap files workers root))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prstartup-required-heap fn-prstartup-registration-reserve))))

(defthm fn-mo-serve-plan-unfolds-when-funded
  (let ((minimum (max 8 (+ 1 (nfix cache-limit)))))
    (implies (and (natp dynamic) (natp occupied) (natp protected) (<= occupied dynamic)
                  (<= protected dynamic)
                  (stringp root) (posp workers) (natp stack) (natp runtime) (natp cache-limit)
                  (natp fd-limit) (<= minimum fd-limit) (fn-crl-table-supportedp minimum)
                  (natp reserve)
                  (<= (+ (fn-prstartup-required-heap minimum workers root) reserve)
                      (fn-prstartup-available dynamic occupied protected)))
             (equal (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                       cache-limit fd-limit reserve)
                    (list :admitted
                          (list (+ (fn-prstartup-available dynamic occupied protected)
                                   (* workers (+ stack runtime)))
                                0
                                (fn-prstartup-affordable-capacity
                                 minimum (min fd-limit (expt 2 24)) 25
                                 (nfix (- (fn-prstartup-available dynamic occupied protected) reserve))
                                 workers root)
                                workers 18446744073709551615)
                          (list (+ (fn-prstartup-baseline-heap
                                    (fn-prstartup-affordable-capacity
                                     minimum (min fd-limit (expt 2 24)) 25
                                     (nfix (- (fn-prstartup-available dynamic occupied protected) reserve))
                                     workers root)
                                    workers)
                                   (* workers (+ stack runtime)))
                                0 0 0 0)
                          0 (fn-prstartup-fd-bookkeeping) 18446744073709551615
                          workers (fn-cgb-capacity)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-prstartup-plan)
                           (fn-prstartup-available fn-prstartup-required-heap fn-prstartup-affordable-capacity
                            fn-prstartup-baseline-heap fn-crl-table-supportedp fn-cgb-capacity
                            fn-prstartup-fd-bookkeeping))
           :use ((:instance fn-prstartup-required-heap-natp
                  (files (max 8 (+ 1 (nfix cache-limit)))))))))

(defthm fn-mo-serve-plan-is-held-when-funded
  (let ((minimum (max 8 (+ 1 (nfix cache-limit))))
        (plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                 cache-limit fd-limit reserve)))
    (implies (and (natp dynamic) (natp occupied) (natp protected) (<= occupied dynamic)
                  (<= protected dynamic)
                  (stringp root) (posp workers) (natp stack) (natp runtime) (natp cache-limit)
                  (natp fd-limit) (<= minimum fd-limit) (fn-crl-table-supportedp minimum)
                  (natp reserve)
                  (<= (+ (fn-prstartup-required-heap minimum workers root) reserve)
                      (fn-prstartup-available dynamic occupied protected)))
             (and (equal (car plan) :admitted)
                  (fn-prstartup-planp plan)
                  (equal (fn-prstartup-decoded-workers plan) workers)
                  (equal (fn-prstartup-nth 0 (fn-prstartup-nth 1 plan))
                         (+ (fn-prstartup-available dynamic occupied protected)
                            (* workers (+ stack runtime)))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-prstartup-plan fn-prstartup-available fn-prstartup-required-heap
                               fn-prstartup-affordable-capacity fn-prstartup-baseline-heap
                               fn-crl-table-supportedp fn-cgb-capacity fn-prstartup-fd-bookkeeping
                               fn-prstartup-planp fn-prstartup-decoded-workers fn-prstartup-nth)
           :use ((:instance fn-mo-serve-plan-unfolds-when-funded)
                 (:instance fn-mo-serve-minimum-in-range (c (nfix cache-limit)) (fd fd-limit))
                 (:instance fn-mo-serve-affordable-capacity-funded
                  (lo (max 8 (+ 1 (nfix cache-limit)))) (hi (min fd-limit (expt 2 24))) (fuel 25)
                  (available (fn-prstartup-available dynamic occupied protected)))
                 (:instance fn-mo-serve-baseline-within-required
                  (files (fn-prstartup-affordable-capacity
                          (max 8 (+ 1 (nfix cache-limit))) (min fd-limit (expt 2 24)) 25
                          (nfix (- (fn-prstartup-available dynamic occupied protected) reserve))
                          workers root)))
                 (:instance fn-mo-serve-held-list-is-planp
                  (plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime
                                           cache-limit fd-limit reserve))
                  (avail (fn-prstartup-available dynamic occupied protected))
                  (native (* workers (+ stack runtime)))
                  (w workers)
                  (f (fn-prstartup-affordable-capacity
                      (max 8 (+ 1 (nfix cache-limit))) (min fd-limit (expt 2 24)) 25
                      (nfix (- (fn-prstartup-available dynamic occupied protected) reserve))
                      workers root)))))))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-mo-serve-mb-of-whole-mebibytes
    (implies (natp m)
             (equal (fn-heap-mb-of (* *fn-heap-mib* m)) m))
    :hints (("Goal" :in-theory (enable fn-heap-mb-of)))))

(defthm fn-mo-serve-read-reserve-is-natp
  (natp (fn-prstartup-read-reserve extent workers))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-prstartup-read-reserve fn-cwq-queue-octets))))

(defthm fn-mo-serve-launch-extra-is-the-plans-need
  (equal (fn-prstartup-launch-extra profile workers cache-limit root)
         (+ (fn-prstartup-required-heap (max 8 (+ 1 (nfix cache-limit))) workers root)
            (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers)))
  :hints (("Goal" :in-theory (enable fn-prstartup-launch-extra))))

(defthm fn-mo-serve-launch-dynamic-is-natp
  (natp (fn-mm-launch-dynamic limit core nursery))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-mm-launch-dynamic))))

(defthm fn-mo-serve-protected-is-natp
  (natp (fn-prstartup-serve-protected profile core nursery output max-connections observed limit))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-prstartup-serve-protected fn-prstartup-protected
                                     fn-prstartup-protected-at))))

(defthm fn-mo-serve-startup-room
  (implies (and (natp dyn) (natp occ) (natp p) (natp peer0) (natp out0) (natp extra)
                (natp ldo) (natp ldp) (natp file)
                (<= (+ ldp extra out0 peer0) dyn)
                (<= p (+ ldo out0))
                (<= ldo ldp)
                (<= occ file) (<= file ldp))
           (and (<= occ dyn)
                (<= (+ p peer0) dyn)
                (<= extra (fn-prstartup-available dyn occ (+ p peer0)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prstartup-available))))

(defthm fn-mo-serve-peer-room
  (implies (and (natp dyn) (natp occ) (natp p) (natp peer0) (<= (+ p peer0) dyn))
           (<= (+ p (fn-prstartup-available dyn occ (+ p peer0)) peer0) dyn))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prstartup-available))))

(defthm fn-mo-serve-pfr-at-is-nth
  (equal (fn-pfr-at n x) (nth n x))
  :hints (("Goal" :in-theory (enable fn-pfr-at) :induct (fn-pfr-at n x))))

(defthm fn-mo-serve-policy-is-a-list
  (implies (fn-pfr-policy-p peer)
           (and (consp peer) (true-listp peer) (natp (car peer)) (natp (nth 3 peer))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pfr-policy-p) (fn-pfr-fixed-backing fn-pfr-bookkeeping fn-pfr-slots)))))

(defthm fn-mo-serve-output-pool-heap
  (equal (nfix (fn-crv-nth 0 output)) (if (consp output) (nfix (car output)) 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-crv-nth))))

(defthm fn-mo-serve-peer-grant-holds
  (implies (and (fn-pfr-policy-p peer)
                (natp dynamic) (natp avail) (natp w)
                (fn-prstartup-planp plan)
                (equal (fn-prstartup-decoded-workers plan) w)
                (equal (fn-prstartup-nth 0 (fn-prstartup-nth 1 plan))
                       (+ avail (* w (+ (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*))))
                (<= (+ (fn-prstartup-serve-protected profile core nursery output max-connections observed limit)
                       avail (nfix (fn-pfr-at 0 peer)))
                    dynamic))
           (equal (fn-pfr-at 0 (fn-prstartup-peer-grant dynamic profile core nursery output
                                                       max-connections plan peer observed limit))
                  :hold))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-prstartup-peer-grant fn-prstartup-peer-protected fn-pfr-startup-grant)
                           (fn-prstartup-planp fn-prstartup-decoded-workers
                            fn-prstartup-nth fn-prstartup-serve-protected
                            fn-pfr-policy-p fn-pfr-at fn-heap-stack-octets))
           :use ((:instance fn-mo-serve-protected-is-natp)
                 (:instance fn-mo-serve-policy-is-a-list)))))

(defthm fn-mo-serve-native-grant-holds
  (let ((addr (fn-mm-least-observation address))
        (limit (fn-prstartup-serve-limit profile output peer workers cache-limit root resident)))
    (implies (and (equal (fn-pfr-at 0 (fn-prstartup-peer-grant dynamic profile core nursery output
                                                               max-connections plan peer observed limit))
                         :hold)
                  (or (not (natp addr))
                      (<= (fn-heap-reservation-octets
                           (fn-heap-mb-of dynamic) core (fn-heap-stack-kib profile)
                           (+ (fn-heap-thread-count max-connections) (nfix (fn-pfr-at 3 peer))))
                          addr)))
             (equal (car (fn-prstartup-peer-native-grant dynamic profile core nursery output max-connections
                                                         plan peer address observed workers cache-limit
                                                         root resident))
                    :hold)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-prstartup-peer-native-grant)
                           (fn-prstartup-peer-grant fn-prstartup-serve-limit fn-mm-least-observation
                            fn-heap-reservation-octets fn-heap-mb-of fn-prstartup-peer-native-capture
                            fn-pfr-at)))))

(defthm fn-mo-serve-decided-space-covers-the-launch
  (let ((d (fn-mo-serve-decide profile img trigger live cold config resident address core nursery tot
                               pools pool-threads))
        (limit (fn-mo-serve-limit resident pools)))
    (implies (equal (car d) :heap)
             (and (natp limit)
                  (natp (cadr d))
                  (<= (+ (fn-mm-launch-dynamic limit (fn-prstartup-image-bound core) nursery) (nfix pools))
                      (* *fn-heap-mib* (cadr d))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-mo-serve-dynamic)
                           (fn-mo-serve-decide fn-mo-serve-limit fn-mm-launch-dynamic fn-heap-mb-of))
           :use ((:instance fn-mo-serve-decide-heap-mb)
                 (:instance fn-mo-serve-decide-heap-limit)
                 (:instance fn-heap-mb-of-covers
                  (octets (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools)))
                 (:instance fn-heap-mb-of-natp
                  (octets (fn-mo-serve-dynamic (fn-mo-serve-limit resident pools) core nursery pools)))))))

(defthm fn-mo-serve-owner-limit-is-within
  (implies (and (natp (fn-mo-serve-limit resident pools))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident)))
           (and (natp (fn-mo-serve-limit resident-o pools))
                (<= (fn-mo-serve-limit resident-o pools) (fn-mo-serve-limit resident pools))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-mo-serve-limit))))

(defthm fn-mo-serve-owner-launch-is-within
  (implies (and (natp lo) (natp lp) (<= lo lp)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core)))
           (<= (fn-mm-launch-dynamic lo owner (fn-heap-nursery-trigger dyn nursery))
               (fn-mm-launch-dynamic lp (fn-prstartup-image-bound core) nursery)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-mm-launch-dynamic fn-heap-core-dynamic fn-heap-core-file
                               fn-heap-nursery-trigger fn-prstartup-image-bound)
           :use ((:instance fn-mo-serve-launch-dynamic-monotone
                  (l1 lo) (c1 owner) (n1 (fn-heap-nursery-trigger dyn nursery))
                  (l2 lp) (c2 (fn-prstartup-image-bound core)) (n2 nursery))
                 (:instance fn-mo-serve-nursery-trigger-within-the-cap (d dyn) (n nursery))
                 (:instance fn-mo-serve-image-bound-dynamic-is-the-file)
                 (:instance fn-heap-core-dynamic-is-at-most-the-file (core owner))))))

(defthm fn-mo-serve-default-plan-with-peer-is-the-plan
  (implies (and (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output)))
           (equal (fn-prstartup-default-plan-with-peer dynamic occupied profile core nursery nil output
                                                       max-connections root workers cache-limit fd-limit
                                                       peer observed resident)
                  (fn-prstartup-plan dynamic occupied
                                     (+ (fn-prstartup-serve-protected
                                         profile core nursery output max-connections observed
                                         (fn-prstartup-serve-limit profile output peer workers cache-limit root
                                                                   resident))
                                        (if peer (nfix (fn-pfr-at 0 peer)) 0))
                                     root workers (fn-heap-stack-octets profile)
                                     *fn-heap-thread-runtime-octets* cache-limit fd-limit
                                     (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers))))
  :hints (("Goal" :in-theory (e/d (fn-prstartup-default-plan-with-peer)
                                  (fn-prstartup-read-reserve fn-prstartup-read-extent fn-prstartup-serve-limit
                                   fn-heap-stack-octets fn-prstartup-serve-protected fn-prstartup-plan
                                   fn-pfr-policy-p fn-orv-policy-p fn-pfr-at)))))

(defthm fn-mo-serve-plan-is-admitted-by-the-room
  (implies (and (natp dyn) (natp occ) (natp p) (natp peer0) (natp out0) (natp ldo) (natp ldp)
                (natp file) (natp cache-limit) (natp fd-limit) (stringp root) (posp workers)
                (<= (+ ldp (fn-prstartup-launch-extra profile workers cache-limit root) out0 peer0) dyn)
                (<= p (+ ldo out0)) (<= ldo ldp) (<= occ file) (<= file ldp)
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit))))
           (and (equal (car (fn-prstartup-plan dyn occ (+ p peer0) root workers
                                               (fn-heap-stack-octets profile)
                                               *fn-heap-thread-runtime-octets* cache-limit fd-limit
                                               (fn-prstartup-read-reserve (fn-prstartup-read-extent profile)
                                                                          workers)))
                       :admitted)
                (fn-prstartup-planp (fn-prstartup-plan dyn occ (+ p peer0) root workers
                                                       (fn-heap-stack-octets profile)
                                                       *fn-heap-thread-runtime-octets* cache-limit fd-limit
                                                       (fn-prstartup-read-reserve (fn-prstartup-read-extent profile)
                                                                                  workers)))
                (equal (fn-prstartup-decoded-workers
                        (fn-prstartup-plan dyn occ (+ p peer0) root workers (fn-heap-stack-octets profile)
                                           *fn-heap-thread-runtime-octets* cache-limit fd-limit
                                           (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers)))
                       workers)
                (equal (fn-prstartup-nth 0 (fn-prstartup-nth 1
                        (fn-prstartup-plan dyn occ (+ p peer0) root workers (fn-heap-stack-octets profile)
                                           *fn-heap-thread-runtime-octets* cache-limit fd-limit
                                           (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers))))
                       (+ (fn-prstartup-available dyn occ (+ p peer0))
                          (* workers (+ (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*))))
                (<= (+ p (fn-prstartup-available dyn occ (+ p peer0)) peer0) dyn)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-prstartup-plan fn-prstartup-launch-extra fn-prstartup-available
                               fn-prstartup-required-heap fn-crl-table-supportedp fn-prstartup-read-reserve
                               fn-prstartup-read-extent fn-heap-stack-octets fn-prstartup-planp
                               fn-prstartup-decoded-workers fn-prstartup-nth)
           :use ((:instance fn-mo-serve-launch-extra-is-the-plans-need)
                 (:instance fn-mo-serve-startup-room (extra (fn-prstartup-launch-extra profile workers cache-limit root)))
                 (:instance fn-mo-serve-peer-room)
                 (:instance fn-mo-serve-read-reserve-is-natp
                  (extent (fn-prstartup-read-extent profile)))
                 (:instance fn-mo-serve-plan-is-held-when-funded
                  (dynamic dyn) (occupied occ) (protected (+ p peer0))
                  (stack (fn-heap-stack-octets profile)) (runtime *fn-heap-thread-runtime-octets*)
                  (reserve (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers)))))))

(defthm fn-mo-serve-prstartup-limit-is-the-serve-limit
  (equal (fn-prstartup-serve-limit profile output peer workers cache-limit root resident)
         (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)))
  :hints (("Goal" :in-theory (enable fn-prstartup-serve-limit))))

(defthm fn-mo-serve-peer-pool-heap
  (implies (or (not peer) (fn-pfr-policy-p peer))
           (equal (if peer (nfix (fn-pfr-at 0 peer)) 0)
                  (if (consp peer) (nfix (car peer)) 0)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-mo-serve-policy-is-a-list))
           :in-theory (disable fn-pfr-policy-p))))

(defthm fn-mo-serve-peer-pool-threads
  (implies (fn-pfr-policy-p peer)
           (equal (fn-mo-serve-pool-threads nil peer) (nfix (fn-pfr-at 3 peer))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-mo-serve-policy-is-a-list))
           :in-theory (e/d (fn-mo-serve-pool-threads) (fn-pfr-policy-p)))))

(defthm fn-mo-serve-launch-extra-natp
  (natp (fn-prstartup-launch-extra profile workers cache-limit root))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-prstartup-launch-extra))))

(defthm fn-mo-serve-pools-are-the-three-pools
  (implies (and (or (not peer) (fn-pfr-policy-p peer)))
           (equal (fn-mo-serve-pools profile nil output peer workers cache-limit root)
                  (+ (fn-prstartup-launch-extra profile workers cache-limit root)
                     (nfix (fn-crv-nth 0 output))
                     (if peer (nfix (fn-pfr-at 0 peer)) 0))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-mo-serve-peer-pool-heap)
                        (:instance fn-mo-serve-output-pool-heap)
                        (:instance fn-mo-serve-launch-extra-natp))
           :in-theory (union-theories '(fn-mo-serve-pools nfix natp) (theory 'minimal-theory)))))

(defthm fn-mo-serve-owner-reservation-is-the-decided-one
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (fn-pfr-policy-p peer))
           (equal (fn-heap-reservation-octets
                   (fn-heap-mb-of (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) owner (fn-heap-stack-kib profile)
                   (+ (fn-heap-thread-count max-connections) (nfix (fn-pfr-at 3 peer))))
                  (fn-mo-serve-reservation profile core
                                           (fn-mo-serve-dynamic (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)) core nursery (fn-mo-serve-pools profile nil output peer workers cache-limit root))
                                           (fn-mo-serve-pool-threads nil peer))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-mo-serve-reservation fn-mo-serve-threads fn-heap-thread-count fn-heap-reservation-octets)
                           (fn-mo-serve-decide fn-mo-serve-dynamic fn-mo-serve-limit fn-mo-serve-pools
                            fn-heap-mb-of fn-heap-core-file fn-mo-serve-pool-threads fn-pfr-policy-p))
           :use ((:instance fn-mo-serve-decide-heap-mb (cold nil) (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (pool-threads (fn-mo-serve-pool-threads nil peer)))
                 (:instance fn-mo-serve-peer-pool-threads)
                 (:instance fn-mo-serve-mb-of-whole-mebibytes
                  (m (fn-heap-mb-of (fn-mo-serve-dynamic (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)) core nursery (fn-mo-serve-pools profile nil output peer workers cache-limit root)))))
                 (:instance fn-heap-mb-of-natp
                  (octets (fn-mo-serve-dynamic (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)) core nursery (fn-mo-serve-pools profile nil output peer workers cache-limit root))))))))

(defthm fn-mo-serve-available-is-natp
  (natp (fn-prstartup-available dynamic occupied protected))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-prstartup-available))))

; The room the plan and the peer grant need, at the probe's decided space (the lemmas below carry the
; keystone's hypotheses and each states one step of it).
(defthm fn-mo-serve-room-natp
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp occupied) (<= occupied (fn-heap-core-dynamic owner))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))
                (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output))
                (stringp root) (posp workers) (natp cache-limit) (natp fd-limit)
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit))))
           (and (natp (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) (natp (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o))) (natp (if peer (nfix (fn-pfr-at 0 peer)) 0)) (natp (nfix (fn-crv-nth 0 output)))
                (natp (fn-mm-launch-dynamic (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o) owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery))) (natp (fn-mm-launch-dynamic (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (fn-prstartup-image-bound core) nursery)) (natp (fn-heap-core-file core))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-mo-serve-decide fn-mo-serve-pools fn-mo-serve-pool-threads fn-mo-serve-limit
                               fn-prstartup-serve-protected fn-mm-launch-dynamic fn-heap-nursery-trigger
                               fn-pfr-policy-p fn-pfr-at fn-heap-core-file fn-prstartup-serve-limit)
           :use ((:instance fn-mo-serve-decided-space-covers-the-launch
                  (cold nil) (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (pool-threads (fn-mo-serve-pool-threads nil peer)))
                 (:instance fn-mo-serve-policy-is-a-list)))))

(defthm fn-mo-serve-room-covers
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp occupied) (<= occupied (fn-heap-core-dynamic owner))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))
                (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output))
                (stringp root) (posp workers) (natp cache-limit) (natp fd-limit)
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit))))
           (<= (+ (fn-mm-launch-dynamic (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (fn-prstartup-image-bound core) nursery) (fn-prstartup-launch-extra profile workers cache-limit root)
                  (nfix (fn-crv-nth 0 output)) (if peer (nfix (fn-pfr-at 0 peer)) 0))
               (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories '(nfix natp) (theory 'minimal-theory))
           :use ((:instance fn-mo-serve-decided-space-covers-the-launch
                  (cold nil) (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (pool-threads (fn-mo-serve-pool-threads nil peer)))
                 (:instance fn-mo-serve-pools-are-the-three-pools)
                 (:instance fn-mo-serve-room-natp)
                 (:instance fn-mo-serve-launch-extra-natp)))))

(defthm fn-mo-serve-room-protected
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp occupied) (<= occupied (fn-heap-core-dynamic owner))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))
                (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output))
                (stringp root) (posp workers) (natp cache-limit) (natp fd-limit)
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit))))
           (<= (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (+ (fn-mm-launch-dynamic (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o) owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery)) (nfix (fn-crv-nth 0 output)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-mo-serve-decide fn-mo-serve-pools fn-mo-serve-pool-threads fn-mo-serve-limit
                               fn-prstartup-serve-protected fn-mm-launch-dynamic fn-heap-nursery-trigger
                               fn-pfr-policy-p fn-pfr-at fn-heap-core-file fn-prstartup-serve-limit)
           :use ((:instance fn-mo-serve-decided-space-covers-the-launch
                  (cold nil) (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (pool-threads (fn-mo-serve-pool-threads nil peer)))
                 (:instance fn-mo-serve-owner-limit-is-within (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)))
                 (:instance fn-mo-serve-protected-within-the-launch
                  (core owner) (nursery (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery)) (limit (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)))))))

(defthm fn-mo-serve-room-owner-launch
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp occupied) (<= occupied (fn-heap-core-dynamic owner))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))
                (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output))
                (stringp root) (posp workers) (natp cache-limit) (natp fd-limit)
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit))))
           (<= (fn-mm-launch-dynamic (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o) owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery)) (fn-mm-launch-dynamic (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (fn-prstartup-image-bound core) nursery)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-mo-serve-decide fn-mo-serve-pools fn-mo-serve-pool-threads fn-mo-serve-limit
                               fn-prstartup-serve-protected fn-mm-launch-dynamic fn-heap-nursery-trigger
                               fn-pfr-policy-p fn-pfr-at fn-heap-core-file fn-prstartup-serve-limit)
           :use ((:instance fn-mo-serve-decided-space-covers-the-launch
                  (cold nil) (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (pool-threads (fn-mo-serve-pool-threads nil peer)))
                 (:instance fn-mo-serve-owner-limit-is-within (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)))
                 (:instance fn-mo-serve-owner-launch-is-within
                  (lo (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (lp (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root))) (dyn (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))))))))

(defthm fn-mo-serve-room-file
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp occupied) (<= occupied (fn-heap-core-dynamic owner))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))
                (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output))
                (stringp root) (posp workers) (natp cache-limit) (natp fd-limit)
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit))))
           (and (<= occupied (fn-heap-core-file core))
                (<= (fn-heap-core-file core) (fn-mm-launch-dynamic (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (fn-prstartup-image-bound core) nursery))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-mo-serve-decide fn-mo-serve-pools fn-mo-serve-pool-threads fn-mo-serve-limit
                               fn-mm-launch-dynamic fn-pfr-policy-p fn-pfr-at fn-heap-core-file
                               fn-heap-core-dynamic fn-prstartup-image-bound)
           :use ((:instance fn-mo-serve-decided-space-covers-the-launch
                  (cold nil) (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (pool-threads (fn-mo-serve-pool-threads nil peer)))
                 (:instance fn-mm-launch-dynamic-holds-the-core-and-the-limit
                  (limit (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root))) (core (fn-prstartup-image-bound core)))
                 (:instance fn-mo-serve-image-bound-dynamic-is-the-file)
                 (:instance fn-heap-core-dynamic-is-at-most-the-file (core owner))))))

(defthm fn-mo-serve-startup-room-facts
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp occupied) (<= occupied (fn-heap-core-dynamic owner))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))
                (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output))
                (stringp root) (posp workers) (natp cache-limit) (natp fd-limit)
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit))))
           (and (equal (car (fn-prstartup-plan (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0)) root workers (fn-heap-stack-octets profile)
                        *fn-heap-thread-runtime-octets* cache-limit fd-limit
                        (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers))) :admitted)
                (fn-prstartup-planp (fn-prstartup-plan (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0)) root workers (fn-heap-stack-octets profile)
                        *fn-heap-thread-runtime-octets* cache-limit fd-limit
                        (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers)))
                (equal (fn-prstartup-decoded-workers (fn-prstartup-plan (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0)) root workers (fn-heap-stack-octets profile)
                        *fn-heap-thread-runtime-octets* cache-limit fd-limit
                        (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers))) workers)
                (equal (fn-prstartup-nth 0 (fn-prstartup-nth 1 (fn-prstartup-plan (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0)) root workers (fn-heap-stack-octets profile)
                        *fn-heap-thread-runtime-octets* cache-limit fd-limit
                        (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers))))
                       (+ (fn-prstartup-available (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0))) (* workers (+ (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*))))
                (<= (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (fn-prstartup-available (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0))) (if peer (nfix (fn-pfr-at 0 peer)) 0)) (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories '(natp posp) (theory 'minimal-theory))
           :use ((:instance fn-mo-serve-room-natp)
                 (:instance fn-mo-serve-room-covers)
                 (:instance fn-mo-serve-room-protected)
                 (:instance fn-mo-serve-room-owner-launch)
                 (:instance fn-mo-serve-room-file)
                 (:instance fn-mo-serve-plan-is-admitted-by-the-room
                  (dyn (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) (occ occupied) (p (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o))) (peer0 (if peer (nfix (fn-pfr-at 0 peer)) 0))
                  (out0 (nfix (fn-crv-nth 0 output))) (ldo (fn-mm-launch-dynamic (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o) owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery))) (ldp (fn-mm-launch-dynamic (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (fn-prstartup-image-bound core) nursery))
                  (file (fn-heap-core-file core)))))))

(defthm fn-mo-serve-startup-peer-grant-holds
  (implies (and (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp occupied) (<= occupied (fn-heap-core-dynamic owner))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))
                (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output))
                (stringp root) (posp workers) (natp cache-limit) (natp fd-limit)
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit)))) peer)
           (equal (fn-pfr-at 0 (fn-prstartup-peer-grant (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections
                                                       (fn-prstartup-plan (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0)) root workers (fn-heap-stack-octets profile)
                        *fn-heap-thread-runtime-octets* cache-limit fd-limit
                        (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers)) peer observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)))
                  :hold))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories '(natp posp) (theory 'minimal-theory))
           :use ((:instance fn-mo-serve-startup-room-facts)
                 (:instance fn-mo-serve-room-natp)
                 (:instance fn-mo-serve-available-is-natp
                  (dynamic (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) (occupied occupied) (protected (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0))))
                 (:instance fn-mo-serve-peer-grant-holds
                  (plan (fn-prstartup-plan (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0)) root workers (fn-heap-stack-octets profile)
                        *fn-heap-thread-runtime-octets* cache-limit fd-limit
                        (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers))) (dynamic (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) (core owner) (nursery (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery)) (limit (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o))
                  (avail (fn-prstartup-available (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0)))) (w workers))))))

(defthm fn-mo-serve-startup-native-grant-holds
  (implies (and (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp occupied) (<= occupied (fn-heap-core-dynamic owner))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))
                (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output))
                (stringp root) (posp workers) (natp cache-limit) (natp fd-limit)
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit)))) peer)
           (equal (car (fn-prstartup-peer-native-grant (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections
                                                       (fn-prstartup-plan (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0)) root workers (fn-heap-stack-octets profile)
                        *fn-heap-thread-runtime-octets* cache-limit fd-limit
                        (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers)) peer address observed workers cache-limit root
                                                       resident-o))
                  :hold))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories '(natp posp) (theory 'minimal-theory))
           :use ((:instance fn-mo-serve-startup-peer-grant-holds)
                 (:instance fn-mo-serve-native-grant-holds
                  (plan (fn-prstartup-plan (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) occupied (+ (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) output max-connections observed (fn-prstartup-serve-limit profile output peer workers cache-limit root resident-o)) (if peer (nfix (fn-pfr-at 0 peer)) 0)) root workers (fn-heap-stack-octets profile)
                        *fn-heap-thread-runtime-octets* cache-limit fd-limit
                        (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers))) (dynamic (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) (core owner) (nursery (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery)) (resident resident-o))
                 (:instance fn-mo-serve-owner-reservation-is-the-decided-one)
                 (:instance fn-mo-serve-decide-heap-reservation
                  (cold nil) (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (pool-threads (fn-mo-serve-pool-threads nil peer)))))))

; KEYSTONE K-L4 (L-RUN-LAUNCH): the owner starts what the probe launched.  At the dynamic space the
; probe decided for the observed store (fn-mo-serve-decide over the pools of this run: the DEFAULT
; pool, the output pool, the peer flight), an owner of the same core file, whose content at startup is
; at most its observation and whose least resident observation is at most the probe's, admits its
; DEFAULT pool plan at the collector trigger it sets in that space, and with a peer flight holds its
; native grant against the same address-space observations.
(defthm fn-mo-serve-startup-admits-the-pool
 (let* ((pools (fn-mo-serve-pools profile nil output peer workers cache-limit root))
        (d (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot
                               pools (fn-mo-serve-pool-threads nil peer)))
        (dyn (* *fn-heap-mib* (cadr d)))
        (trigger (fn-heap-nursery-trigger dyn nursery))
        (plan (fn-prstartup-default-plan-with-peer dyn occupied profile owner trigger nil output
                                                   max-connections root workers cache-limit fd-limit
                                                   peer observed resident-o)))
  (implies (and (equal (car d) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp occupied) (<= occupied (fn-heap-core-dynamic owner))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))
                (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output))
                (stringp root) (posp workers) (natp cache-limit) (natp fd-limit)
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit))))
           (and (equal (car plan) :admitted)
                (implies peer
                         (equal (car (fn-prstartup-peer-native-grant
                                      dyn profile owner trigger output max-connections plan peer
                                      address observed workers cache-limit root resident-o))
                                :hold)))))
   :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories '(natp posp fn-mo-serve-default-plan-with-peer-is-the-plan)
                                      (theory 'minimal-theory))
           :use ((:instance fn-mo-serve-startup-room-facts)
                 (:instance fn-mo-serve-startup-native-grant-holds)))))

; THE OUTPUT POOL'S STORE NEED (L-RUN-LAUNCH).  The output startup grant (books/output-reservation.lisp
; fn-orv-startup-grant: the dynamic space holds the store's need, the cold pool and the output pool;
; host/native/mux.lisp fnn-mux-budget-install) is given the served run's protected runtime without the
; output pool, the smaller of the profile's store and the run's launch, at the run's LIMIT.
(defun fn-prstartup-serve-store-need (profile core nursery output peer workers cache-limit root resident)
 (declare (xargs :guard t))
 (fn-prstartup-serve-protected profile core nursery nil nil nil
                               (fn-prstartup-serve-limit profile output peer workers cache-limit root
                                                         resident)))

(defthm fn-mo-serve-output-within-the-pools
 (<= (nfix (fn-crv-nth 0 output)) (fn-mo-serve-pools profile nil output peer workers cache-limit root))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories '(fn-mo-serve-pools nfix natp) (theory 'minimal-theory))
          :use ((:instance fn-mo-serve-output-pool-heap)
                (:instance fn-mo-serve-launch-extra-natp)))))

(defthm fn-mo-serve-pools-is-natp
 (natp (fn-mo-serve-pools profile cold output peer workers cache-limit root))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn-mo-serve-pools))))

(defthm fn-mo-serve-output-room
 (implies (and (rationalp sn) (rationalp l1) (rationalp l2) (rationalp pools) (rationalp dyn)
               (rationalp o) (<= sn l1) (<= l1 l2) (<= (+ l2 pools) dyn) (<= o pools))
          (<= (+ sn o) dyn))
 :rule-classes nil)
; KEYSTONE K-L4c: the owner's output pool is held where the probe launched: the store's need at the
; owner's observations (same core file, least resident observation at most the probe's, at the
; trigger it sets in that space) and the output pool fit the decided dynamic space.
(defthm fn-mo-serve-output-pool-is-held
 (let* ((pools (fn-mo-serve-pools profile nil output peer workers cache-limit root))
        (d (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot
                               pools (fn-mo-serve-pool-threads nil peer)))
        (dyn (* *fn-heap-mib* (cadr d))))
  (implies (and (equal (car d) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (natp (fn-mm-least-observation resident-o))
                (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))
                (or (not peer) (fn-pfr-policy-p peer)))
           (<= (+ (fn-prstartup-serve-store-need profile owner (fn-heap-nursery-trigger dyn nursery)
                                                 output peer workers cache-limit root resident-o)
                  (nfix (fn-crv-nth 0 output)))
               dyn)))
 :rule-classes nil
 :hints (("Goal"
          :in-theory (union-theories '(fn-prstartup-serve-store-need fn-mo-serve-prstartup-limit-is-the-serve-limit
                                       natp nfix fn-mo-serve-pools-is-natp fn-mo-serve-protected-is-natp
                                       fn-mo-serve-launch-dynamic-is-natp (:executable-counterpart fn-crv-nth))
                                     (theory 'minimal-theory))
          :use ((:instance fn-mo-serve-decided-space-covers-the-launch
                           (cold nil) (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (pool-threads (fn-mo-serve-pool-threads nil peer)))
                (:instance fn-mo-serve-owner-limit-is-within (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)))
                (:instance fn-mo-serve-protected-within-the-launch
                           (core owner) (output nil) (max-connections nil) (observed nil)
                           (nursery (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery)) (limit (fn-mo-serve-limit resident-o (fn-mo-serve-pools profile nil output peer workers cache-limit root))))
                (:instance fn-mo-serve-owner-launch-is-within (lo (fn-mo-serve-limit resident-o (fn-mo-serve-pools profile nil output peer workers cache-limit root))) (lp (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root))) (dyn (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))))
                (:instance fn-mo-serve-output-within-the-pools)
                (:instance fn-mo-serve-launch-dynamic-is-natp (limit (fn-mo-serve-limit resident-o (fn-mo-serve-pools profile nil output peer workers cache-limit root))) (core owner) (nursery (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery)))
                (:instance fn-mo-serve-output-room
                           (sn (fn-prstartup-serve-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery) nil nil nil (fn-mo-serve-limit resident-o (fn-mo-serve-pools profile nil output peer workers cache-limit root))))
                           (l1 (fn-mm-launch-dynamic (fn-mo-serve-limit resident-o (fn-mo-serve-pools profile nil output peer workers cache-limit root)) owner (fn-heap-nursery-trigger (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))) nursery)))
                           (l2 (fn-mm-launch-dynamic (fn-mo-serve-limit resident (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (fn-prstartup-image-bound core) nursery))
                           (pools (fn-mo-serve-pools profile nil output peer workers cache-limit root)) (dyn (* *fn-heap-mib* (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) (o (nfix (fn-crv-nth 0 output))))))))
