; Definite padding page ACK retains complete original canonical regions.
; Proof-only carry; actual private-file and INITIAL obligations remain separate.
(in-package "ACL2")
(include-book "history-image-padding-refinement")
(local
 (defun fn-hpizp-field-ind (j k c)
  (if (or (zp j) (zp k)) (list j k c)
    (fn-hpizp-field-ind (1- j) (1- k) (if (consp c) (cdr c) nil)))))

(local
 (defthm fn-hpizp-set-field
  (implies (and (natp k) (< k 25) (natp j) (< j 25))
   (equal (fn-omk-at j (fn-hpi-set k value c))
          (if (equal j k) value (fn-omk-at j c))))
  :hints (("Goal" :induct (fn-hpizp-field-ind j k c)
           :expand ((fn-hpi-set k value c)
                    (fn-omk-at j c)
                    (fn-omk-at j (fn-hpi-set k value c))
                    (:free (a d) (fn-omk-at j (cons a d))))
           :in-theory (e/d (fn-omk-at fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))


(local (defthm fn-hpizp-mv-zero (equal (mv-nth 0 x) (car x))
 :hints (("Goal" :in-theory (enable mv-nth)))))

(defun fn-hpizp-ack-contextp (c)
 (declare (xargs :guard t :verify-guards nil))
 (let ((region (fn-omk-at 0 (fn-omk-at 17 c))))
  (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :wait-write)
       (natp region) (< region 5)
       (equal (fn-omk-at 1 (fn-omk-at 17 c)) :pad)
       (equal (fn-omk-at 4 (fn-omk-at 5 c)) region))))

(defthm fn-hpi-written-padding-page-resets-only-matched-region
 (let* ((region (fn-omk-at 0 (fn-omk-at 17 c)))
        (old (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpizp-ack-contextp c) (equal (car r) :written))
   (and (equal (fn-hpi-written-status (fn-omk-at 5 c) observation) :written)
        (equal (fn-omk-at 0 (mv-nth 2 r)) :pad)
        (equal (fn-omk-at 9 (mv-nth 2 r)) (fn-omk-at 9 c))
(equal (fn-omk-at 10 (mv-nth 2 r)) (fn-omk-at 10 c))
(equal (fn-omk-at 12 (mv-nth 2 r)) (fn-omk-at 12 c))
(equal (fn-omk-at 14 (mv-nth 2 r)) (fn-omk-at 14 c))
(equal (fn-omk-at 18 (mv-nth 2 r)) (fn-omk-at 18 c))
        (equal (fn-omk-at 15 (mv-nth 2 r))
               (fn-hpi-set region (+ 1 (nfix (fn-omk-at region (fn-omk-at 15 c)))) (fn-omk-at 15 c)))
        (equal (fn-omk-at 16 (mv-nth 2 r))
               (fn-hpi-set region (+ 1 (nfix (fn-omk-at region (fn-omk-at 16 c)))) (fn-omk-at 16 c)))
        (equal (fn-omk-at 5 (mv-nth 2 r)) nil)
        (equal (fn-omk-at 17 (mv-nth 2 r)) nil)
        (equal (mv-nth (+ 4 region) r) (fn-hpb-begin (fn-omk-at 1 c) (fn-omk-at 2 c) old))
        (implies (and (natp other) (< other 5) (not (equal region other)))
         (equal (mv-nth (+ 4 other) r) (fn-hpq-model-select other fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
        (equal (mv-nth 1 r) nil) (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-omk-at 0 (fn-omk-at 17 c)) 0)
          (equal (fn-omk-at 0 (fn-omk-at 17 c)) 1)
          (equal (fn-omk-at 0 (fn-omk-at 17 c)) 2)
          (equal (fn-omk-at 0 (fn-omk-at 17 c)) 3)
          (equal (fn-omk-at 0 (fn-omk-at 17 c)) 4)
          (equal other 0) (equal other 1) (equal other 2) (equal other 3) (equal other 4))
  :in-theory (e/d (fn-hpizp-ack-contextp fn-hpi-tick fn-hpi-written fn-hpi-reset-buffer fn-hpq-model-select fn-hpi-written-status)
    (fn-hpi-grant-matchesp fn-hpi-written-matchp fn-hpb-begin fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
     fn-hpi-buffer-step fn-hpi-stream-step fn-hpi-supply fn-osj-native-grow mv-nth)))))


(local (defthm fn-hpizp-begin-used-zero
 (equal (fn-hpb-used (fn-hpb-begin source maintenance fn-hpb)) 0)
 :hints (("Goal" :in-theory (enable fn-hpb-begin fn-hpb-used)))))

(defthm fn-hpi-reset-full-padded-region-establishes-next-canonical-suffix
 (implies (and (fn-hpiz-region-invariantp raw page cap fn-hpb)
               (equal (fn-hpb-used fn-hpb) 2048))
  (fn-hpiz-region-invariantp raw (+ 1 page) cap (fn-hpb-begin source maintenance fn-hpb)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpiz-region-invariantp)
    (fn-hpb-used fn-hpb-begin fn-hpb-prefix adt-cap fn-hp-wpad nthcdr mv-nth)))))

(local (defthm fn-hpizp-at-is-nth-by-definition
 (equal (fn-omk-at n xs) (nth n xs))
 :hints (("Goal" :induct (fn-omk-at n xs) :in-theory (enable fn-omk-at nth)))))
(local (defthm fn-hpizp-nth-set-field
 (implies (and (natp j) (< j 25) (natp k) (< k 25))
  (equal (nth j (fn-hpi-set k value c)) (if (equal j k) value (nth j c))))
 :hints (("Goal" :in-theory (enable fn-hpi-set-is-update-by-definition)))))

(defun fn-hpizp-five-invariantp (h salt pages colcap poolcap fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (let ((raw (fn-hp-regs h salt)))
  (and (fn-hpiz-region-invariantp (nth 0 raw) (nfix (nth 0 pages)) (nfix colcap) fn-hpq0)
       (fn-hpiz-region-invariantp (nth 1 raw) (nfix (nth 1 pages)) (nfix colcap) fn-hpq1)
       (fn-hpiz-region-invariantp (nth 2 raw) (nfix (nth 2 pages)) (nfix colcap) fn-hpq2)
       (fn-hpiz-region-invariantp (nth 3 raw) (nfix (nth 3 pages)) (nfix colcap) fn-hpq3)
       (fn-hpiz-region-invariantp (nth 4 raw) (nfix (nth 4 pages)) (nfix poolcap) fn-hpb))))

(local (defthm fn-hpizp-nfix-next-page
 (equal (nfix (+ 1 (nfix page))) (+ 1 (nfix page)))
 :hints (("Goal" :in-theory (enable nfix)))))

(defthm fn-hpizp-reset-preserves-complete-canonical-padding-carry
 (let ((next-pages (fn-hpi-set region (+ 1 (nfix (nth region pages))) pages)))
  (implies (and (natp region) (< region 5)
                (fn-hpizp-five-invariantp h salt pages colcap poolcap fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (equal (fn-hpb-used (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) 2048))
   (fn-hpizp-five-invariantp h salt next-pages colcap poolcap
     (if (equal region 0) (fn-hpb-begin source maintenance fn-hpq0) fn-hpq0)
     (if (equal region 1) (fn-hpb-begin source maintenance fn-hpq1) fn-hpq1)
     (if (equal region 2) (fn-hpb-begin source maintenance fn-hpq2) fn-hpq2)
     (if (equal region 3) (fn-hpb-begin source maintenance fn-hpq3) fn-hpq3)
     (if (equal region 4) (fn-hpb-begin source maintenance fn-hpb) fn-hpb))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal region 0) (equal region 1) (equal region 2) (equal region 3) (equal region 4))
  :use ((:instance fn-hpi-reset-full-padded-region-establishes-next-canonical-suffix (raw (nth 0 (fn-hp-regs h salt))) (page (nfix (nth 0 pages))) (cap (nfix colcap)) (fn-hpb fn-hpq0))
        (:instance fn-hpi-reset-full-padded-region-establishes-next-canonical-suffix (raw (nth 1 (fn-hp-regs h salt))) (page (nfix (nth 1 pages))) (cap (nfix colcap)) (fn-hpb fn-hpq1))
        (:instance fn-hpi-reset-full-padded-region-establishes-next-canonical-suffix (raw (nth 2 (fn-hp-regs h salt))) (page (nfix (nth 2 pages))) (cap (nfix colcap)) (fn-hpb fn-hpq2))
        (:instance fn-hpi-reset-full-padded-region-establishes-next-canonical-suffix (raw (nth 3 (fn-hp-regs h salt))) (page (nfix (nth 3 pages))) (cap (nfix colcap)) (fn-hpb fn-hpq3))
        (:instance fn-hpi-reset-full-padded-region-establishes-next-canonical-suffix (raw (nth 4 (fn-hp-regs h salt))) (page (nfix (nth 4 pages))) (cap (nfix poolcap))))
  :in-theory (union-theories
    '(fn-hpizp-five-invariantp fn-hpq-model-select fn-hpizp-nth-set-field fn-hpizp-nfix-next-page
      (:type-prescription nfix) pgs-x-nfix-when-natp
      (:e nfix) (:e natp) (:e binary-+) (:e equal) (:e <) (:e not))
    (theory 'minimal-theory)))))

(defthm fn-hpi-written-padding-page-preserves-complete-canonical-carry
 (let* ((region (fn-omk-at 0 (fn-omk-at 17 c)))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpizp-ack-contextp c)
                (fn-hpizp-five-invariantp h (fn-omk-at 12 c) (fn-omk-at 15 c) (fn-omk-at 9 c) (fn-omk-at 10 c)
                  fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (equal (fn-hpb-used (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) 2048)
                (equal (car r) :written))
   (and (fn-hpizp-five-invariantp h (fn-omk-at 12 (mv-nth 2 r)) (fn-omk-at 15 (mv-nth 2 r))
          (fn-omk-at 9 (mv-nth 2 r)) (fn-omk-at 10 (mv-nth 2 r))
          (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))
        (equal (fn-omk-at 0 (mv-nth 2 r)) :pad)
        (equal (fn-omk-at 18 (mv-nth 2 r)) (fn-omk-at 18 c))
        (equal (fn-omk-at 14 (mv-nth 2 r)) (fn-omk-at 14 c))
        (equal (mv-nth 1 r) nil) (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-omk-at 0 (fn-omk-at 17 c)) 0) (equal (fn-omk-at 0 (fn-omk-at 17 c)) 1)
          (equal (fn-omk-at 0 (fn-omk-at 17 c)) 2) (equal (fn-omk-at 0 (fn-omk-at 17 c)) 3)
          (equal (fn-omk-at 0 (fn-omk-at 17 c)) 4))
  :use ((:instance fn-hpizp-at-is-nth-by-definition (n (fn-omk-at 0 (fn-omk-at 17 c))) (xs (fn-omk-at 15 c)))
        (:instance fn-hpi-written-padding-page-resets-only-matched-region (other 0))
        (:instance fn-hpi-written-padding-page-resets-only-matched-region (other 1))
        (:instance fn-hpi-written-padding-page-resets-only-matched-region (other 2))
        (:instance fn-hpi-written-padding-page-resets-only-matched-region (other 3))
        (:instance fn-hpi-written-padding-page-resets-only-matched-region (other 4))
        (:instance fn-hpizp-reset-preserves-complete-canonical-padding-carry
          (region (fn-omk-at 0 (fn-omk-at 17 c))) (salt (fn-omk-at 12 c)) (pages (fn-omk-at 15 c))
          (colcap (fn-omk-at 9 c)) (poolcap (fn-omk-at 10 c))
          (source (fn-omk-at 1 c)) (maintenance (fn-omk-at 2 c))))
  :in-theory (e/d (fn-hpizp-ack-contextp fn-hpq-model-select)
   (fn-hpi-tick fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-hpizp-at-is-nth-by-definition
    fn-hpizp-five-invariantp fn-hpiz-region-invariantp fn-hpb-used fn-hpb-begin fn-hp-regs nthcdr nth mv-nth)))))
