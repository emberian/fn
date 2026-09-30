(in-package "ACL2")
(include-book "../../books/history-image-producer")

; One small nonempty image has six logical data pages, one table and one
; directory page. Page0 plus the FNSI prefix are separate physical extents.
(assert-event
 (let* ((token '(7 (9 1) 0 0))
        (layout (fn-hpi-layout 1 8 1 1 163840))
        (c (fn-hpi-begin 1 8 1 1 token '(:maintenance 19 7 1) 19
                         163840 "node" '(1) "trail")))
   (and (equal layout '(:prepared (:layout 6 1 1 2 8 9) 163840 192 32))
        (equal (car c) :need-growth)
        (equal (fn-omk-at 1 c) token)
        (equal (fn-omk-at 3 c) 19)
        (equal (fn-omk-at 5 c) nil)
        (equal (fn-omk-at 6 c) layout)
        (equal (fn-hpi-growth-request c)
               '(:checkpoint-growth (7 (9 1) 0 0) 19 (:maintenance 19 7 1)
                                     6 1 1 163840 192 32))
        (equal (car (fn-omk-at 14 c)) :need-row)
        (equal (fn-omk-at 6 (fn-omk-at 14 c)) '(7 (9 1) 1 0)))))

; Rounded capacity and physical/file representability are independently
; checked before backing initialization. No u64 caller promise bypasses them.
(assert-event
 (and (equal (fn-hpi-layout 1 8 2 1 1000000) '(:refused :census-domain))
      (equal (fn-hpi-layout 1 8 1 1 163839) '(:refused :file-extent))
      (equal (fn-hpi-layout 0 8 0 1 1000000) '(:refused :census-domain))
      (equal (fn-hpi-layout 1 7 1 1 1000000) '(:refused :census-domain))
      (equal (fn-hpi-layout 2305843009213693951 8 1125899906842624 1
                            36893488147419103232)
             '(:refused :canonical-extent))))

; The exact completed write authorizes reuse; a stale staging attempt, serial
; or buffer identity cannot. A matching ambiguous result is recovery, not reuse.
(assert-event
 (let* ((token '(7 (9 1) 0 0))
        (effect (fn-hpi-write-effect token 19 3 4 5 7 2)))
   (and (equal effect
                '(:write-page (7 (9 1) 0 0) 19 3 4 5 7 131072 16384 2))
        (equal (fn-hpi-written-status effect
                 '(:written (7 (9 1) 0 0) 19 3 2 :ok)) :written)
        (equal (fn-hpi-written-status effect
                 '(:written (7 (9 1) 0 0) 19 3 2 :uncertain))
               :recovery-required)
        (equal (fn-hpi-written-status effect
                 '(:written (7 (9 1) 0 0) 18 3 2 :ok)) :stale)
        (equal (fn-hpi-written-status effect
                 '(:written (7 (9 1) 0 0) 19 2 2 :ok)) :stale)
        (equal (fn-hpi-written-status effect
                 '(:written (7 (9 1) 0 0) 19 3 1 :ok)) :stale))))

; This complete trajectory is a proof/test-only file model. The actual writer
; emits bounded I/O effects; no served path builds these lists or hashes them.
(defun hpi-test-buffer (i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (case i (0 (fn-hpb-prefix fn-hpq0)) (1 (fn-hpb-prefix fn-hpq1))
          (2 (fn-hpb-prefix fn-hpq2)) (3 (fn-hpb-prefix fn-hpq3))
          (otherwise (fn-hpb-prefix fn-hpb))))

(defun hpi-test-run (fuel c observation ledger pages spools rows source pool key
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
         ((eq v :prepared)
          (mv (list :prepared next pages spools rows) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
         ((eq v :need-row)
          (mv-let (offered next)
            (fn-hpi-offer next rows source (fn-omk-at 1 effect) key)
            (if (not (eq offered :started))
                (mv (list :offer-refused offered next) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
              (hpi-test-run (1- fuel) next nil ledger pages spools rows source pool key
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
            (hpi-test-run (1- fuel) next obs ledger pages spools rows source pool key
                          fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
         (t (mv (list :unexpected v next effect) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))))

(defun hpi-test-digests (i n pages base)
  (declare (xargs :verify-guards nil :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i)) nil
    (cons (pgs-octets-be-nat
            (fn-blake3 (pgs-words-le-octets (cdr (assoc-equal (+ base i) pages)))))
          (hpi-test-digests (+ 1 i) n pages base))))

(defun hpi-test-spools-equal (i n kind digests spools)
  (declare (xargs :verify-guards nil :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i)) t
    (and (equal (pgs-octets-be-nat (cdr (assoc-equal (cons kind i) spools)))
                (nth i digests))
         (hpi-test-spools-equal (+ 1 i) n kind digests spools))))

(defun hpi-test-complete ()
  (declare (xargs :verify-guards nil))
(with-local-stobj fn-hpq0
 (mv-let (result fn-hpq0)
(with-local-stobj fn-hpq1
 (mv-let (result fn-hpq0 fn-hpq1)
(with-local-stobj fn-hpq2
 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2)
(with-local-stobj fn-hpq3
 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
(with-local-stobj fn-hpb
 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
(with-local-stobj pgs-digest-state
 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
(mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1
                '(1000000 16384 3 1 1))
  (let* ((source '(7 (9 1) 0 0))
         (c (fn-hpi-begin 1 8 1 1 source maintenance (fn-omk-at 1 maintenance)
                          10000000 "node" 17 "trail")))
    (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (hpi-test-run 50000 c nil ledger nil nil 0 '(:decoded (:span 3 0 1 3))
                    '(0 65 66 67) (fn-hp-mkey "ABC" 17)
                    fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (mv (list admitted maintenance result) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
(mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
(mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)))
(mv result fn-hpq0 fn-hpq1 fn-hpq2)))
(mv result fn-hpq0 fn-hpq1)))
(mv result fn-hpq0)))
result)))

; Independent concrete reference: the production page-store record writer,
; on its actual two stobjs. It hashes the sixteen persisted body words.
(defun hpi-test-reference-root (count digest)
  (declare (xargs :verify-guards nil))
  (with-local-stobj pgs-mem
    (mv-let (root pgs-mem)
      (with-local-stobj fn-octets-pg
        (mv-let (root pgs-mem fn-octets-pg)
          (let ((pgs-mem (resize-pgs-m 20 pgs-mem)))
            (pgs-x-write-rec 0 1 1 count digest pgs-mem fn-octets-pg))
          (mv root pgs-mem)))
      root)))

; Full literal positive: actual live ledger admission, decoded source, all
; canonical data/metadata pages, both digest spools and the terminal binding.
(assert-event
 (let* ((r (hpi-test-complete)) (maintenance (nth 1 r)) (run (nth 2 r))
        (c (nth 1 run)) (pages (nth 2 run)) (spools (nth 3 run))
        (digests (hpi-test-digests 0 6 pages 2))
        (table-digests (hpi-test-digests 0 1 pages 8))
        (directory (cdr (assoc-equal 1 pages)))
        (root (hpi-test-reference-root 6
                 (pgs-octets-be-nat (fn-blake3 (pgs-words-le-octets directory))))))
   (and (equal (car r) :admitted)
        (equal maintenance '(:maintenance 0 7 1))
        (equal (car run) :prepared) (equal (nth 4 run) 1)
        (equal (len pages) 9) (equal (len spools) 7)
        (equal (cdr (assoc-equal 0 pages)) (adt-zeros 2048))
        (equal (cdr (assoc-equal 2 pages))
               (fn-hp-hdr2 1 (fn-hcc-lens 1 8) (fn-hcc-starts 1) 6))
        (equal (cdr (assoc-equal 3 pages)) (cons (fn-hp-mkey "ABC" 17) (adt-zeros 2047)))
        (equal (cdr (assoc-equal 4 pages)) (cons (len (fn-scc-encode "ABC")) (adt-zeros 2047)))
        (equal (cdr (assoc-equal 5 pages)) (adt-zeros 2048))
        (equal (cdr (assoc-equal 6 pages)) (cons 8 (adt-zeros 2047)))
        (equal (cdr (assoc-equal 7 pages)) (append (fn-hp-pack8 1 (fn-scc-encode "ABC")) (adt-zeros 2047)))
        (hpi-test-spools-equal 0 6 :data digests spools)
        (hpi-test-spools-equal 0 1 :table table-digests spools)
        (equal (cdr (assoc-equal 8 pages)) (pgs-encode-table (fn-hpm-model-entries digests 2)))
        (equal directory (pgs-encode-run (fn-hpm-model-entries table-digests 8) 1))
        (equal (fn-omk-at 24 c)
               (list :image-complete '(7 (9 1) 0 0) 0 "node" 17 1 "trail" root 163840)))))

; Mutation witnesses: stale stage, ambiguous completion, corrupted read byte.
; Every retained identity/demand/live-receipt antecedent is checked first.
(defun hpi-test-bad-completions ()
  (declare (xargs :verify-guards nil))
(with-local-stobj fn-hpq0
 (mv-let (result fn-hpq0)
(with-local-stobj fn-hpq1
 (mv-let (result fn-hpq0 fn-hpq1)
(with-local-stobj fn-hpq2
 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2)
(with-local-stobj fn-hpq3
 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
(with-local-stobj fn-hpb
 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
(with-local-stobj pgs-digest-state
 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
(mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((c (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance
                         (fn-omk-at 1 maintenance) 10000000 "node" 17 "trail")))
    (mv-let (funded request c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (fn-hpi-tick c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (declare (ignore request))
      (mv-let (begun c pgs-digest-state) (fn-hpi-digest-begin :data 0 c pgs-digest-state)
        (mv-let (issued effect c)
          (fn-hpi-issue-io :read-stage :data 0 49152 64 nil :wait-stage-read c)
          (let* ((good (list :image-read (nth 1 effect) (nth 2 effect) (nth 3 effect)
                             :data 0 (nth 8 effect) :ok (adt-zeros 64)))
                 (stale (update-nth 2 999 good))
                 (uncertain (update-nth 7 :uncertain good))
                 (bad (update-nth 8 (cons 256 (adt-zeros 63)) good))
                 (antecedent
                   (and (eq admitted :admitted) (eq funded :funded) (eq begun :continue)
                        (eq issued :io) (fn-hpi-grant-matchesp c ledger)
                        (fn-hpi-digest-validp 16384 c pgs-digest-state)
                        (fn-hpi-io-matchp c good :image-read 9)
                        (not (fn-hpi-io-matchp c stale :image-read 9))
                        (fn-hpi-io-matchp c uncertain :image-read 9)
                        (fn-hpi-io-matchp c bad :image-read 9)
                        (not (fn-hpi-octets-p 64 (nth 8 bad))))))
            (mv-let (sv se sc sl fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
              (fn-hpi-tick c stale ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
              (let ((stale-ok (and (eq sv :stale) (null se) (equal sc c) (equal sl ledger))))
                (mv-let (uv ue uc ul fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
                  (fn-hpi-tick c uncertain ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
                  (let ((uncertain-ok (and (eq uv :uncertain) (null ue) (equal ul ledger)
                                           (equal uc (fn-hpi-set 0 :recovery-required c)))))
                    (mv-let (bv be bc bl fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
                      (fn-hpi-tick c bad ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
                      (mv (and antecedent stale-ok uncertain-ok
                               (equal bv '(:refused :stage-response)) (null be) (equal bl ledger)
                               (equal bc (fn-hpi-set 0 :refused c))
                               (equal (fn-hpb-used fn-hpq0) 0) (equal (fn-hpb-used fn-hpq1) 0)
                               (equal (fn-hpb-used fn-hpq2) 0) (equal (fn-hpb-used fn-hpq3) 0)
                               (equal (fn-hpb-used fn-hpb) 0) (equal (pgs-dc-pos pgs-digest-state) 0))
                          fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))))))))
(mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
(mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)))
(mv result fn-hpq0 fn-hpq1 fn-hpq2)))
(mv result fn-hpq0 fn-hpq1)))
(mv result fn-hpq0)))
result)))
(assert-event (hpi-test-bad-completions))
