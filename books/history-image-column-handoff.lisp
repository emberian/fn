; Actual canonical column page issuance and retained continuation.
; Proof-only; complete image/progress/INITIAL remain open.
(in-package "ACL2")
(include-book "history-image-column-pages")

(local
 (defun fn-hpich-field-ind (j k c)
  (if (or (zp j) (zp k)) (list j k c)
    (fn-hpich-field-ind (1- j) (1- k) (if (consp c) (cdr c) nil)))))

(local
 (defthm fn-hpich-set-field
  (implies (and (natp k) (< k 25) (natp j) (< j 25))
   (equal (fn-omk-at j (fn-hpi-set k value c))
          (if (equal j k) value (fn-omk-at j c))))
  :hints (("Goal" :induct (fn-hpich-field-ind j k c)
           :expand ((fn-hpi-set k value c)
                    (fn-omk-at j c)
                    (fn-omk-at j (fn-hpi-set k value c))
                    (:free (a d) (fn-omk-at j (cons a d))))
           :in-theory (e/d (fn-omk-at fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpich-mv-zero (equal (mv-nth 0 x) (car x))
 :hints (("Goal" :in-theory (enable mv-nth)))))

(local (defthm fn-hpich-column-output-classes
 (implies (equal (fn-hrcur-field 0 c) :columns)
  (member-equal (car (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
   '(:column-stored :row-done :page-full (:refused :cursor) (:refused :census) (:refused :cell))))
 :hints (("Goal" :in-theory (e/d (fn-hpcx-tick)
   (fn-hpcx-shapep fn-hpcx-with fn-hrcur-field fn-hcl-cell fn-hpq-put fn-hcc-row fn-hpe-tick mv-nth))))))

(local (defthm fn-hpich-inner-page-full-fields
 (let* ((column (fn-hrcur-field 9 body))
        (r (fn-hpcx-tick body fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (equal (fn-hrcur-field 0 body) :columns) (equal (car r) :page-full))
   (and (natp column) (< column 4) (equal (mv-nth 1 r) column)
        (<= 2048 (fn-hpb-used (fn-hpq-model-select column fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-hrcur-field 9 body) 0) (equal (fn-hrcur-field 9 body) 1)
          (equal (fn-hrcur-field 9 body) 2) (equal (fn-hrcur-field 9 body) 3))
  :in-theory (e/d (fn-hpcx-tick fn-hpcx-shapep fn-hpq-put fn-hpb-put fn-hpq-model-select)
   (fn-hpcx-with fn-hrcur-field fn-hcl-cell fn-hcc-row fn-hpe-tick fn-hpe-shapep fn-hpb-used
    fn-hpb-wi update-fn-hpb-wi update-fn-hpb-used fn-omk-tokenp mv-nth))))))

(local (defthm fn-hpich-outer-write-complete-output
 (let* ((body (fn-omk-at 14 c))
        (inner (fn-hpcx-tick body fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :body)
                (equal (fn-hrcur-field 0 body) :columns) (equal (car r) :write))
   (and (equal (car inner) :page-full)
        (equal (car (fn-hpi-await-region (mv-nth 1 inner) :body (fn-hpi-set 14 (mv-nth 2 inner) c))) :write)
        (equal r
          (mv :write
              (mv-nth 1 (fn-hpi-await-region (mv-nth 1 inner) :body (fn-hpi-set 14 (mv-nth 2 inner) c)))
              (mv-nth 2 (fn-hpi-await-region (mv-nth 1 inner) :body (fn-hpi-set 14 (mv-nth 2 inner) c))) ledger
              (mv-nth 3 inner) (mv-nth 4 inner) (mv-nth 5 inner) (mv-nth 6 inner) (mv-nth 7 inner)
              pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpich-column-output-classes (c (fn-omk-at 14 c)))
        (:instance fn-hpich-inner-page-full-fields (body (fn-omk-at 14 c))))
  :in-theory (e/d (fn-hpi-tick fn-hpi-buffer-step fn-hpi-supply fn-hpcx-supply fn-hsrcb-demandp)
   (fn-hpi-written fn-hpi-stream-step fn-hpcx-tick fn-hpcx-shapep fn-hpcx-with fn-hrcur-field
    fn-hpi-grant-matchesp fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpi-await-region fn-hpi-await-page fn-hpi-reset-buffer fn-osj-native-grow
    fn-hpe-supply fn-hpe-tick fn-hpq-put fn-hpb-put fn-hcl-cell fn-hcc-row
    fn-hpb-used fn-hpi-region-cap fn-hpi-region-used mv-nth fn-hpich-column-output-classes)))))
)

(local (defthm fn-hpich-selected-carry
 (implies (and (fn-hpicol-four-invariantp h row salt body pages fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
               (natp column) (< column 4))
  (fn-hpicol-region-invariantp column h row salt body pages
   (fn-hpq-model-select column fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
 :rule-classes nil
 :hints (("Goal" :cases ((equal column 0) (equal column 1) (equal column 2) (equal column 3))
  :in-theory (e/d (fn-hpicol-four-invariantp fn-hpq-model-select)
   (fn-hpicol-region-invariantp fn-hpcx-shapep fn-hrcur-field fn-hp-mkey fn-scc-encode fn-scc-encode-is-program fn-hp-pes-len))))))

(local (defthm fn-hpich-region-used-bound
 (implies (fn-hpicol-region-invariantp column h row salt body pages fn-hpb)
  (<= (fn-hpb-used fn-hpb) 2048))
 :hints (("Goal" :in-theory (e/d (fn-hpicol-region-invariantp)
   (fn-hpb-used fn-hpb-prefix fn-hpicol-carried-history fn-hpicol-history-model nthcdr nth))))))

(local (defthm fn-hpich-prefix-aux-length
 (implies (natp k) (equal (len (fn-hpb-prefix-aux i k fn-hpb)) k))
 :hints (("Goal" :induct (fn-hpb-prefix-aux i k fn-hpb)
  :in-theory (e/d (fn-hpb-prefix-aux) (fn-hpb-wi))))))
(local (defthm fn-hpich-prefix-length
 (implies (natp (fn-hpb-used fn-hpb))
  (equal (len (fn-hpb-prefix fn-hpb)) (fn-hpb-used fn-hpb)))
 :hints (("Goal" :in-theory (e/d (fn-hpb-prefix) (fn-hpb-used fn-hpb-prefix-aux))))))

(local (defthm fn-hpich-update-keeps-width
 (implies (and (natp n) (<= n 25) (natp k) (< k n) (fn-omk-widthp c n))
  (fn-omk-widthp (fn-hpi-set k value c) n))
 :hints (("Goal" :induct (fn-hpich-field-ind n k c)
  :expand ((fn-hpi-set k value c) (fn-omk-widthp c n)
           (fn-omk-widthp (fn-hpi-set k value c) n))
  :in-theory (e/d (fn-omk-widthp fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpich-at-cons-by-definition
 (equal (fn-omk-at n (cons a d)) (if (zp n) a (fn-omk-at (1- n) d)))
 :hints (("Goal" :expand ((fn-omk-at n (cons a d))) :in-theory (disable fn-omk-at)))))

(local (defthm fn-hpich-await-establishes-ack-context
 (let ((r (fn-hpi-await-region column :body c)))
  (implies (and (fn-omk-widthp c 25) (natp column) (< column 4) (equal (car r) :write))
   (fn-hpicp-ack-contextp (mv-nth 2 r))))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-region fn-hpi-await-page fn-hpi-write-effect fn-hpicp-ack-contextp)
  (fn-hpi-region-cap fn-hpi-region-start fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at mv-nth))))))

(defthm fn-hpi-column-page-handoff-is-complete-canonical-page
 (let* ((body (fn-omk-at 14 c)) (column (fn-hrcur-field 9 body))
        (selected (fn-hpq-model-select column fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (await (fn-hpi-await-region column :body (fn-hpi-set 14 body c)))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpicol-writer-ready-p h row salt c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
                (equal (car r) :write))
   (and (natp column) (< column 4)
        (equal (fn-hpb-used selected) 2048) (equal (len (fn-hpb-prefix selected)) 2048)
        (equal (fn-hpb-prefix selected)
          (nthcdr (* 2048 (nfix (nth column (fn-omk-at 15 c))))
           (fn-hpicol-history-model column (fn-hpicol-carried-history column h row body) salt)))
        (fn-hpicp-ack-contextp (mv-nth 2 r))
        (equal r (mv :write (mv-nth 1 await) (mv-nth 2 await) ledger
                     fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpich-outer-write-complete-output
        (:instance fn-hpich-prefix-length
         (fn-hpb (fn-hpq-model-select (fn-hrcur-field 9 (fn-omk-at 14 c)) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
        (:instance fn-hpich-inner-page-full-fields (body (fn-omk-at 14 c)))
        (:instance fn-hpcx-page-full-is-unchanged (c (fn-omk-at 14 c)))
        (:instance fn-hpich-selected-carry (body (fn-omk-at 14 c)) (pages (fn-omk-at 15 c))
         (column (fn-hrcur-field 9 (fn-omk-at 14 c))))
        (:instance fn-hpich-await-establishes-ack-context
         (column (fn-hrcur-field 9 (fn-omk-at 14 c))) (c (fn-hpi-set 14 (fn-omk-at 14 c) c))))
  :in-theory (e/d (fn-hpicol-writer-ready-p fn-hpicol-region-invariantp)
   (fn-hpi-tick fn-hpcx-tick fn-hpi-await-region fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-omk-at fn-hrcur-field fn-hpicol-four-invariantp fn-hpq-model-select fn-hpb-used fn-hpb-prefix
    fn-hpicol-history-model fn-hpicol-carried-history fn-hpich-prefix-length fn-hpicp-ack-contextp nthcdr nth mv-nth)))))
