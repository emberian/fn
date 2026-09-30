; Actual scalar-column page ownership and canonical continuation.
; Proof-only observations; whole pool/private-stage/INITIAL remain separate.
(in-package "ACL2")
(include-book "history-image-body-refinement")

(local
 (defun fn-hpicp-field-ind (j k c)
  (if (or (zp j) (zp k)) (list j k c)
    (fn-hpicp-field-ind (1- j) (1- k) (if (consp c) (cdr c) nil)))))

(local
 (defthm fn-hpicp-set-field
  (implies (and (natp k) (< k 25) (natp j) (< j 25))
   (equal (fn-omk-at j (fn-hpi-set k value c))
          (if (equal j k) value (fn-omk-at j c))))
  :hints (("Goal" :induct (fn-hpicp-field-ind j k c)
           :expand ((fn-hpi-set k value c)
                    (fn-omk-at j c)
                    (fn-omk-at j (fn-hpi-set k value c))
                    (:free (a d) (fn-omk-at j (cons a d))))
           :in-theory (e/d (fn-omk-at fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))


(local (defthm fn-hpicp-mv-zero (equal (mv-nth 0 x) (car x))
 :hints (("Goal" :in-theory (enable mv-nth)))))

(defun fn-hpicp-ack-contextp (c)
 (declare (xargs :guard t :verify-guards nil))
 (let ((region (fn-omk-at 0 (fn-omk-at 17 c))))
  (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :wait-write)
       (natp region) (< region 4)
       (equal (fn-omk-at 1 (fn-omk-at 17 c)) :body)
       (equal (fn-omk-at 4 (fn-omk-at 5 c)) region))))

(defthm fn-hpi-written-column-page-resets-only-matched-region
 (let* ((region (fn-omk-at 0 (fn-omk-at 17 c)))
        (old (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpicp-ack-contextp c) (equal (car r) :written))
   (and (equal (fn-hpi-written-status (fn-omk-at 5 c) observation) :written)
        (equal (fn-omk-at 0 (mv-nth 2 r)) :body)
        (equal (fn-omk-at 14 (mv-nth 2 r)) (fn-omk-at 14 c))
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
          (equal other 0) (equal other 1) (equal other 2) (equal other 3) (equal other 4))
  :in-theory (e/d (fn-hpicp-ack-contextp fn-hpi-tick fn-hpi-written fn-hpi-reset-buffer fn-hpq-model-select fn-hpi-written-status)
    (fn-hpi-grant-matchesp fn-hpi-written-matchp fn-hpb-begin fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
     fn-hpi-buffer-step fn-hpi-stream-step fn-hpi-supply fn-osj-native-grow mv-nth)))))

(local (defthm fn-hpicp-prefix-aux-length
 (implies (natp k) (equal (len (fn-hpb-prefix-aux i k fn-hpb)) k))
 :hints (("Goal" :induct (fn-hpb-prefix-aux i k fn-hpb)
  :in-theory (e/d (fn-hpb-prefix-aux) (fn-hpb-wi))))))
(local (defthm fn-hpicp-prefix-length
 (implies (natp (fn-hpb-used fn-hpb))
  (equal (len (fn-hpb-prefix fn-hpb)) (fn-hpb-used fn-hpb)))
 :hints (("Goal" :in-theory (e/d (fn-hpb-prefix) (fn-hpb-used fn-hpb-prefix-aux))))))

(local (defthm fn-hpicp-nthcdr-length
 (implies (and (natp n) (<= n (len xs)))
  (equal (len (nthcdr n xs)) (- (len xs) n)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr len)))))
(local (defthm fn-hpicp-nthcdr-past-end
 (implies (and (true-listp xs) (natp n) (<= (len xs) n))
  (equal (nthcdr n xs) nil))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr len true-listp)))))

(local (defthm fn-hpicp-history-model-is-true-list
 (true-listp (fn-hpicol-history-model region h salt))
 :hints (("Goal" :in-theory (e/d (fn-hpicol-history-model) (fn-hpicol-select fn-hp-rows adt-rows-cells))))))

(local (defthm fn-hpicp-at-is-nth-by-definition
 (equal (fn-omk-at n xs) (nth n xs))
 :hints (("Goal" :induct (fn-omk-at n xs) :in-theory (enable fn-omk-at nth)))))

(local (defthm fn-hpicp-nth-set-field
 (implies (and (natp j) (< j 25) (natp k) (< k 25))
  (equal (nth j (fn-hpi-set k value c)) (if (equal j k) value (nth j c))))
 :hints (("Goal" :in-theory (enable fn-hpi-set-is-update-by-definition)))))

(local (defthm fn-hpicp-begin-used-zero
 (equal (fn-hpb-used (fn-hpb-begin source maintenance fn-hpb)) 0)
 :hints (("Goal" :in-theory (enable fn-hpb-begin fn-hpb-used)))))

(defthm fn-hpi-reset-full-column-establishes-next-canonical-suffix
 (let* ((page (nfix (nth region pages)))
        (next-pages (fn-hpi-set region (+ 1 page) pages)))
  (implies (and (natp region) (< region 4)
                (fn-hpicol-region-invariantp region h row salt body pages fn-hpb)
                (equal (fn-hpb-used fn-hpb) 2048))
   (fn-hpicol-region-invariantp region h row salt body next-pages
      (fn-hpb-begin source maintenance fn-hpb))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpicp-prefix-length)
        (:instance fn-hpicp-nthcdr-length
          (n (* 2048 (nfix (nth region pages))))
          (xs (fn-hpicol-history-model region (fn-hpicol-carried-history region h row body) salt))))
  :in-theory (e/d (fn-hpicol-region-invariantp)
    (fn-hpb-used fn-hpb-begin fn-hpb-prefix fn-hpi-set fn-hpi-set-is-update-by-definition
     fn-hpicol-carried-history fn-hpicol-history-model fn-hpb-prefix-aux
     fn-hpicp-prefix-length fn-hpicp-nthcdr-length pgs-len-of-nthcdr nthcdr nth mv-nth)))))

(local (defthm fn-hpicp-other-column-page-count-frame
 (implies (and (natp region) (< region 4) (natp other) (< other 4)
               (not (equal region other)))
  (equal (fn-hpicol-region-invariantp other h row salt body (fn-hpi-set region value pages) fn-hpb)
         (fn-hpicol-region-invariantp other h row salt body pages fn-hpb)))
 :hints (("Goal" :in-theory (e/d (fn-hpicol-region-invariantp)
  (fn-hpb-used fn-hpb-prefix fn-hpi-set fn-hpi-set-is-update-by-definition
   fn-hpicol-carried-history fn-hpicol-history-model nthcdr nth mv-nth))))))

(defthm fn-hpicp-reset-preserves-full-canonical-column-carry
 (let ((next-pages (fn-hpi-set region (+ 1 (nfix (nth region pages))) pages)))
  (implies (and (natp region) (< region 4)
                (fn-hpicol-four-invariantp h row salt body pages fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
                (equal (fn-hpb-used (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) 2048))
   (fn-hpicol-four-invariantp h row salt body next-pages
     (if (equal region 0) (fn-hpb-begin source maintenance fn-hpq0) fn-hpq0)
     (if (equal region 1) (fn-hpb-begin source maintenance fn-hpq1) fn-hpq1)
     (if (equal region 2) (fn-hpb-begin source maintenance fn-hpq2) fn-hpq2)
     (if (equal region 3) (fn-hpb-begin source maintenance fn-hpq3) fn-hpq3))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal region 0) (equal region 1) (equal region 2) (equal region 3))
  :use ((:instance fn-hpi-reset-full-column-establishes-next-canonical-suffix (region 0) (fn-hpb fn-hpq0))
        (:instance fn-hpi-reset-full-column-establishes-next-canonical-suffix (region 1) (fn-hpb fn-hpq1))
        (:instance fn-hpi-reset-full-column-establishes-next-canonical-suffix (region 2) (fn-hpb fn-hpq2))
        (:instance fn-hpi-reset-full-column-establishes-next-canonical-suffix (region 3) (fn-hpb fn-hpq3)))
  :in-theory (e/d (fn-hpicol-four-invariantp fn-hpq-model-select)
   (fn-hpcx-shapep fn-hrcur-field fn-hp-mkey fn-scc-encode fn-scc-encode-is-program fn-hp-pes-len
    fn-hpb-begin fn-hpb-used fn-hpb-prefix fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-hpicol-region-invariantp fn-hpicol-carried-history fn-hpicol-history-model nthcdr nth mv-nth)))))

(local (defthm fn-hpicp-written-keeps-salt
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpicp-ack-contextp c) (equal (car r) :written))
   (equal (fn-omk-at 12 (mv-nth 2 r)) (fn-omk-at 12 c))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpicp-ack-contextp fn-hpi-tick fn-hpi-written fn-hpi-written-status)
   (fn-hpi-grant-matchesp fn-hpi-written-matchp fn-hpi-reset-buffer fn-hpb-begin fn-hpi-set
    fn-hpi-set-is-update-by-definition fn-omk-at fn-hpi-buffer-step fn-hpi-stream-step
    fn-hpi-supply fn-osj-native-grow fn-hpicp-at-is-nth-by-definition mv-nth))))))

(defthm fn-hpi-written-page-preserves-full-canonical-column-carry
 (let* ((region (fn-omk-at 0 (fn-omk-at 17 c)))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpicp-ack-contextp c)
                (fn-hpicol-four-invariantp h row salt (fn-omk-at 14 c) (fn-omk-at 15 c)
                  fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
                (equal (fn-hpb-used (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) 2048)
                (equal (car r) :written))
   (and (fn-hpicol-four-invariantp h row salt (fn-omk-at 14 (mv-nth 2 r)) (fn-omk-at 15 (mv-nth 2 r))
           (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r))
        (equal (fn-omk-at 0 (mv-nth 2 r)) :body)
        (equal (fn-omk-at 12 (mv-nth 2 r)) (fn-omk-at 12 c))
        (equal (fn-omk-at 14 (mv-nth 2 r)) (fn-omk-at 14 c))
        (equal (mv-nth 8 r) fn-hpb)
        (equal (mv-nth 1 r) nil) (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-omk-at 0 (fn-omk-at 17 c)) 0)
          (equal (fn-omk-at 0 (fn-omk-at 17 c)) 1)
          (equal (fn-omk-at 0 (fn-omk-at 17 c)) 2)
          (equal (fn-omk-at 0 (fn-omk-at 17 c)) 3))
  :use ((:instance fn-hpicp-at-is-nth-by-definition (n (fn-omk-at 0 (fn-omk-at 17 c))) (xs (fn-omk-at 15 c)))
        (:instance fn-hpi-written-column-page-resets-only-matched-region (other 0))
        (:instance fn-hpi-written-column-page-resets-only-matched-region (other 1))
        (:instance fn-hpi-written-column-page-resets-only-matched-region (other 2))
        (:instance fn-hpi-written-column-page-resets-only-matched-region (other 3))
        (:instance fn-hpi-written-column-page-resets-only-matched-region (other 4))
        (:instance fn-hpicp-reset-preserves-full-canonical-column-carry
          (region (fn-omk-at 0 (fn-omk-at 17 c))) (body (fn-omk-at 14 c)) (pages (fn-omk-at 15 c))
          (source (fn-omk-at 1 c)) (maintenance (fn-omk-at 2 c))))
  :in-theory (e/d (fn-hpicp-ack-contextp fn-hpq-model-select)
   (fn-hpi-tick fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-hpicp-at-is-nth-by-definition
    fn-hpicol-four-invariantp fn-hpicol-region-invariantp fn-hpb-used fn-hpb-begin
    fn-hpicol-history-model fn-hpicol-carried-history nthcdr nth mv-nth)))))
