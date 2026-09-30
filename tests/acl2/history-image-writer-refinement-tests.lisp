(in-package "ACL2")
(include-book "../../books/history-image-writer-refinement")
(include-book "history-image-producer-tests")
(include-book "../../host/history-image-effect-host")

; Proof/test-only trajectory: exactly the existing actual writer driver,
; stopping at an issued operation. It never executes on a served path.
(defun hpiw-test-until (fuel stop c observation ledger pages spools rows source pool key
                    fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
                  :verify-guards nil :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-hpi-tick fn-hpi-offer
                     fn-omk-at hpi-test-buffer pgs-words-le-octets)))))
  (if (zp fuel)
      (mv (list :fuel c pages spools rows) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (mv-let (v effect next ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (let ((tag (fn-omk-at 0 effect)))
        (cond
         ((eq tag stop)
          (mv (list :stopped v effect next ledger pages spools rows)
              fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
         ((eq v :prepared)
          (mv (list :prepared next pages spools rows) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
         ((eq v :need-row)
          (mv-let (offered next)
            (fn-hpi-offer next rows source (fn-omk-at 1 effect) key)
            (if (not (eq offered :started))
                (mv (list :offer-refused offered next) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
              (hpiw-test-until (1- fuel) stop next nil ledger pages spools rows source pool key
                            fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
         ((member-eq v '(:funded :continue :written :row-done :need-byte :write :io))
          (let* ((rows (if (eq v :row-done) (+ 1 rows) rows))
                 (pages (if (eq tag :write-page)
                            (acons (fn-omk-at 6 effect)
                                   (hpi-test-buffer (fn-omk-at 0 (fn-omk-at 17 next))
                                                    fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                                   pages) pages))
                 (spools (if (eq tag :write-spool)
                             (acons (cons (fn-omk-at 4 effect) (fn-omk-at 5 effect))
                                    (fn-omk-at 9 effect) spools) spools))
                 (obs
                   (cond
                    ((eq v :need-byte)
                     (list :supply (fn-omk-at 1 effect) (nth (fn-omk-at 1 effect) pool)))
                    ((eq tag :write-page)
                     (list :written (fn-omk-at 1 effect) (fn-omk-at 2 effect)
                           (fn-omk-at 3 effect) (fn-omk-at 9 effect) :ok))
                    ((eq tag :write-spool)
                     (list :spool-written (fn-omk-at 1 effect) (fn-omk-at 2 effect)
                           (fn-omk-at 3 effect) (fn-omk-at 4 effect) (fn-omk-at 5 effect)
                           (fn-omk-at 8 effect) :ok))
                    ((member-eq tag '(:read-stage :read-spool))
                     (let* ((offset (fn-omk-at 6 effect))
                            (bytes (if (eq tag :read-stage)
                                       (pgs-words-le-octets
                                         (cdr (assoc-equal (floor (- offset 16384) 16384) pages)))
                                     (cdr (assoc-equal (cons (fn-omk-at 4 effect)
                                                            (fn-omk-at 5 effect)) spools))))
                            (offset (if (eq tag :read-stage) (mod offset 16384) 0)))
                       (list (if (eq tag :read-stage) :image-read :spool-read)
                             (fn-omk-at 1 effect) (fn-omk-at 2 effect)
                             (fn-omk-at 3 effect) (fn-omk-at 4 effect) (fn-omk-at 5 effect)
                             (fn-omk-at 8 effect) :ok
                             (take (fn-omk-at 7 effect) (nthcdr offset bytes)))))
                    (t nil))))
            (hpiw-test-until (1- fuel) stop next obs ledger pages spools rows source pool key
                          fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
         (t (mv (list :unexpected v next effect) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))

(defun hpiw-test-buffer-array (i fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil :measure (nfix (- 2048 i))))
 (if (or (not (natp i)) (<= 2048 i)) nil
  (cons (fn-hpb-wi i fn-hpb) (hpiw-test-buffer-array (+ 1 i) fn-hpb))))

(defun hpiw-test-buffer-model (fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (list (hpiw-test-buffer-array 0 fn-hpb) (fn-hpb-used fn-hpb)
       (fn-hpb-epoch fn-hpb) (fn-hpb-lease fn-hpb)))

(defun hpiw-test-digest-frames (i pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil :measure (nfix (- 64 i))))
 (if (or (not (natp i)) (<= 64 i)) nil
  (cons (pgs-dc-framesi i pgs-digest-state)
        (hpiw-test-digest-frames (+ 1 i) pgs-digest-state))))

(defun hpiw-test-full-model (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (list (hpiw-test-buffer-model fn-hpq0) (hpiw-test-buffer-model fn-hpq1)
       (hpiw-test-buffer-model fn-hpq2) (hpiw-test-buffer-model fn-hpq3)
       (hpiw-test-buffer-model fn-hpb)
       (list (pgs-dc-mode pgs-digest-state) (pgs-dc-sel pgs-digest-state)
             (pgs-dc-base pgs-digest-state) (pgs-dc-total pgs-digest-state)
             (pgs-dc-start pgs-digest-state) (pgs-dc-end pgs-digest-state)
             (pgs-dc-pos pgs-digest-state) (pgs-dc-counter pgs-digest-state)
             (pgs-dc-power pgs-digest-state) (pgs-dc-depth pgs-digest-state)
             (pgs-dc-cv pgs-digest-state) (pgs-dc-output pgs-digest-state)
             (pgs-dc-capture pgs-digest-state) (pgs-dc-lease pgs-digest-state)
             (pgs-dc-answer pgs-digest-state) (hpiw-test-digest-frames 0 pgs-digest-state))))

; Every point is reached by the actual complete row/page/spool driver from
; actual ledger admission. Each removal falsifies only the named hypothesis.
; Corrupted phase witnesses also construct an observation that retains the
; literal phase-selected matching hypothesis; no executor emits that message.
(defun hpiw-test-uncertain-point (stop mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance (fn-omk-at 1 maintenance)
                  10000000 "node" 17 "trail")))
   (mv-let (r fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (hpiw-test-until 50000 stop initial nil ledger nil nil 0 '(:decoded (:span 3 0 1 3))
      '(0 65 66 67) (fn-hp-mkey "ABC" 17)
      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (let* ((effect (nth 2 r)) (original (nth 3 r)) (old-ledger (nth 4 r))
           (c (case mode (:width (append original '(:extra)))
                         (:phase (fn-hpi-set 0 :zero original)) (otherwise original)))
           (ledger (if (eq mode :grant) nil old-ledger))
           (offset (fn-omk-at 6 effect))
           (bytes (case stop
             (:read-stage (take (fn-omk-at 7 effect)
               (nthcdr (mod offset 16384)
                (pgs-words-le-octets (cdr (assoc-equal (floor (- offset 16384) 16384) (nth 5 r)))))))
             (:read-spool (cdr (assoc-equal (cons (fn-omk-at 4 effect) (fn-omk-at 5 effect)) (nth 6 r))))
             (otherwise nil)))
           (observation (fn-hie-observation original effect (fn-omk-at 3 original) old-ledger
             (if (eq mode :outcome) (if (eq stop :write-page) 16384 (fn-omk-at 7 effect)) 0)
             :ok (if (eq mode :outcome) bytes nil)))
           (observation (if (eq mode :match)
                          (update-nth 2 (+ 1 (nfix (fn-omk-at 2 observation))) observation) observation))
           (observation (if (and (eq mode :phase) (not (eq stop :write-page)))
                          (update-nth 0 :spool-written (take 9 observation)) observation))
           (pagep (eq stop :write-page))
           (premises
            (if pagep
             (list (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :wait-write)
                   (if (fn-hpi-grant-matchesp c ledger) t nil)
                   (equal (fn-hpi-written-status (fn-omk-at 5 c) observation) :recovery-required))
             (list (fn-omk-widthp c 25)
                   (if (member-eq (fn-omk-at 0 c) '(:wait-stage-read :wait-spool-read :wait-spool-write)) t nil)
                   (if (fn-hpi-grant-matchesp c ledger) t nil)
                   (if (fn-hpi-io-matchp c observation
                     (case (fn-omk-at 0 c) (:wait-stage-read :image-read)
                                          (:wait-spool-read :spool-read) (otherwise :spool-written))
                     (if (equal (fn-omk-at 0 c) :wait-spool-write) 8 9)) t nil)
                   (equal (fn-omk-at 7 observation) :uncertain))))
           (which (case mode (:width 0) (:phase 1) (:grant 2) (:match 3)
                            (:outcome (if pagep 3 4)) (otherwise nil)))
           (expected (if pagep '(t t t t) '(t t t t t)))
           (expected (if (natp which) (update-nth which nil expected) expected))
           (old-model (hpiw-test-full-model fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
     (mv-let (v e next next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (let ((law (and (equal v (if pagep :recovery-required :uncertain)) (null e)
                 (equal next (fn-hpi-set 0 :recovery-required c))
                 (equal next-ledger ledger)
                 (equal (hpiw-test-full-model fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) old-model))))
       (mv (and (eq admitted :admitted) (eq (car r) :stopped)
                (eq (car effect) stop) (member-eq (nth 1 r) '(:write :io))
                (equal premises expected) (equal law (eq mode :positive)))
           fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))))

(defun hpiw-test-local-point (stop mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpiw-test-uncertain-point stop mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result)))

; Complete reachable positive at actual write-page point.
(assert-event (hpiw-test-local-point :write-page :positive))

; Literal hypothesis removal width (corrupted state) at actual write-page point.
(assert-event (hpiw-test-local-point :write-page :width))

; Literal hypothesis removal phase (corrupted state) at actual write-page point.
(assert-event (hpiw-test-local-point :write-page :phase))

; Literal hypothesis removal grant (corrupted state) at actual write-page point.
(assert-event (hpiw-test-local-point :write-page :grant))

; Literal hypothesis removal outcome (successful returned I/O) at actual write-page point.
(assert-event (hpiw-test-local-point :write-page :outcome))

; Complete reachable positive at actual read-stage point.
(assert-event (hpiw-test-local-point :read-stage :positive))

; Literal hypothesis removal width (corrupted state) at actual read-stage point.
(assert-event (hpiw-test-local-point :read-stage :width))

; Literal hypothesis removal phase (corrupted state) at actual read-stage point.
(assert-event (hpiw-test-local-point :read-stage :phase))

; Literal hypothesis removal grant (corrupted state) at actual read-stage point.
(assert-event (hpiw-test-local-point :read-stage :grant))

; Literal hypothesis removal outcome (successful returned I/O) at actual read-stage point.
(assert-event (hpiw-test-local-point :read-stage :outcome))

; Literal hypothesis removal match (corrupted state) at actual read-stage point.
(assert-event (hpiw-test-local-point :read-stage :match))

; Complete reachable positive at actual write-spool point.
(assert-event (hpiw-test-local-point :write-spool :positive))

; Literal hypothesis removal width (corrupted state) at actual write-spool point.
(assert-event (hpiw-test-local-point :write-spool :width))

; Literal hypothesis removal phase (corrupted state) at actual write-spool point.
(assert-event (hpiw-test-local-point :write-spool :phase))

; Literal hypothesis removal grant (corrupted state) at actual write-spool point.
(assert-event (hpiw-test-local-point :write-spool :grant))

; Literal hypothesis removal outcome (successful returned I/O) at actual write-spool point.
(assert-event (hpiw-test-local-point :write-spool :outcome))

; Literal hypothesis removal match (corrupted state) at actual write-spool point.
(assert-event (hpiw-test-local-point :write-spool :match))

; Complete reachable positive at actual read-spool point.
(assert-event (hpiw-test-local-point :read-spool :positive))

; Literal hypothesis removal width (corrupted state) at actual read-spool point.
(assert-event (hpiw-test-local-point :read-spool :width))

; Literal hypothesis removal phase (corrupted state) at actual read-spool point.
(assert-event (hpiw-test-local-point :read-spool :phase))

; Literal hypothesis removal grant (corrupted state) at actual read-spool point.
(assert-event (hpiw-test-local-point :read-spool :grant))

; Literal hypothesis removal outcome (successful returned I/O) at actual read-spool point.
(assert-event (hpiw-test-local-point :read-spool :outcome))

; Literal hypothesis removal match (corrupted state) at actual read-spool point.
(assert-event (hpiw-test-local-point :read-spool :match))

; Complete captured-authority boundary, including failed initial admission.
; The model is the theorem's whole conclusion, not only its live predicate.
(defun hpiw-test-authority-point (mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 10 4 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance (fn-omk-at 1 maintenance)
                  10000000 "node" 17 "trail")))
   (mv-let (r fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (if (member-eq mode '(:initial :initial-removal))
      (mv (list :initial nil nil initial ledger) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
     (hpiw-test-until 50000 :write-page initial nil ledger nil nil 0 '(:decoded (:span 3 0 1 3))
      '(0 65 66 67) (fn-hp-mkey "ABC" 17)
      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
    (let* ((original (nth 3 r)) (old-ledger (nth 4 r))
           (old-ledger (if (member-eq mode '(:initial-removal :retained-removal :nongrowth-grant)) nil old-ledger)))
     (mv-let (second second-maintenance extra-ledger)
      (fn-pmn-admit old-ledger 8 2 '(1000000 16384 3 1 1))
      (declare (ignore second-maintenance))
      (let* ((ledger (if (eq mode :nongrowth-phase) extra-ledger old-ledger))
             (c (if (eq mode :nongrowth-phase) (fn-hpi-set 0 :need-growth original) original))
             (live (if (fn-hpi-grant-matchesp c ledger) t nil))
             (nongrowth (not (equal (fn-omk-at 0 c) :need-growth))))
       (mv-let (v e next next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (fn-hpi-tick c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (declare (ignore e))
        (let* ((frame (equal (fn-hpiv-capture next) (fn-hpiv-capture c)))
               (retained (and (equal next-ledger ledger) (equal (nth 22 next) (nth 22 c))))
               (next-live (if (fn-hpi-grant-matchesp next next-ledger) t nil))
               (antecedent (or (and live nongrowth) (and (not nongrowth) (equal v :funded))))
               (conclusion (and frame next-live (if nongrowth retained t)))
               (nongrowth-law (and frame retained next-live)))
         (mv (and (equal admitted :admitted)
               (case mode
                (:initial (and (equal (car r) :initial) (not live) (not nongrowth)
                               (equal v :funded) antecedent conclusion))
                (:initial-removal (and (equal (car r) :initial) (not antecedent) (not conclusion)))
                (:retained (and (equal (car r) :stopped) live nongrowth antecedent conclusion nongrowth-law))
                (:retained-removal (and (equal (car r) :stopped) (not antecedent) (not conclusion)))
                (:nongrowth-grant (and (equal (car r) :stopped) (not live) nongrowth (not nongrowth-law)))
                (:nongrowth-phase (and (equal (car r) :stopped) (equal second :admitted)
                                      live (not nongrowth) (not nongrowth-law)))
                (otherwise nil)))
             fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))))))

(defun hpiw-test-local-authority (mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpiw-test-authority-point mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result)))

; Literal captured-authority witness: initial.
(assert-event (hpiw-test-local-authority :initial))

; Literal captured-authority witness: initial-removal.
(assert-event (hpiw-test-local-authority :initial-removal))

; Literal captured-authority witness: retained.
(assert-event (hpiw-test-local-authority :retained))

; Literal captured-authority witness: retained-removal.
(assert-event (hpiw-test-local-authority :retained-removal))

; Literal captured-authority witness: nongrowth-grant.
(assert-event (hpiw-test-local-authority :nongrowth-grant))

; Literal captured-authority witness: nongrowth-phase.
(assert-event (hpiw-test-local-authority :nongrowth-phase))


(defun hpiw-test-issued-point (stop mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance (fn-omk-at 1 maintenance)
                  10000000 "node" 17 "trail")))
   (mv-let (r fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (hpiw-test-until 50000 stop initial nil ledger nil nil 0 '(:decoded (:span 3 0 1 3))
      '(0 65 66 67) (fn-hp-mkey "ABC" 17)
      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (let ((forged '(:write-page nil nil 999 nil nil nil nil nil nil)))
     (mv-let (v effect next ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (if (eq mode :status-removal)
       ; Corrupted terminal metadata imitates a tag but was never issued.
       (fn-hpi-tick (fn-hpi-set 0 :prepared (fn-hpi-set 24 forged (nth 3 r))) nil (nth 4 r)
         fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
       (mv (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r)
         fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
      (declare (ignore ledger))
      (let ((antecedent (if (member-eq v '(:write :io)) t nil))
            (conclusion (and (fn-hpiv-io-effectp effect) (fn-hpiv-issued-effectp next effect))))
       (mv (and (eq admitted :admitted) (eq (car r) :stopped)
                (if (eq mode :positive) (and antecedent conclusion)
                 (and (eq mode :status-removal) (not antecedent)
                      (fn-hpiv-io-effectp effect) (not conclusion))))
        fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))))

(defun hpiw-test-local-issued (stop mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpiw-test-issued-point stop mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result)))

; Complete actual issuance positive at write-page.
(assert-event (hpiw-test-local-issued :write-page :positive))

; Complete actual issuance positive at read-stage.
(assert-event (hpiw-test-local-issued :read-stage :positive))

; Complete actual issuance positive at write-spool.
(assert-event (hpiw-test-local-issued :write-spool :positive))

; Complete actual issuance positive at read-spool.
(assert-event (hpiw-test-local-issued :read-spool :positive))

; Sole status hypothesis removal, explicitly corrupted terminal metadata.
(assert-event (hpiw-test-local-issued :write-page :status-removal))
