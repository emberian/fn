; Actual four-column body carry, projected from the existing FNADTSN2 model.
; Proof observers only. Pool/source/INITIAL joins remain explicit obligations.
(in-package "ACL2")
(include-book "history-image-writer-refinement")

(defun fn-hpicol-select (column rows)
 (declare (xargs :guard t :verify-guards nil))
 (if (atom rows) nil
  (cons (nth column (car rows)) (fn-hpicol-select column (cdr rows)))))

(defun fn-hpicol-history-model (column h salt)
 (declare (xargs :guard t :verify-guards nil))
 (fn-hpicol-select column (adt-rows-cells *fn-hp-schema* (fn-hp-rows h salt) 0)))

(local (defthm fn-hpicol-cars-append
 (equal (adt-cars (append x y)) (append (adt-cars x) (adt-cars y)))
 :hints (("Goal" :induct (adt-cars x) :in-theory (enable adt-cars)))))
(local (defthm fn-hpicol-cdrs-append
 (equal (adt-cdrs (append x y)) (append (adt-cdrs x) (adt-cdrs y)))
 :hints (("Goal" :induct (adt-cdrs x) :in-theory (enable adt-cdrs)))))
(local (defthm fn-hpicol-select-append
 (equal (fn-hpicol-select column (append x y))
        (append (fn-hpicol-select column x) (fn-hpicol-select column y)))
 :hints (("Goal" :induct (fn-hpicol-select column x) :in-theory (enable fn-hpicol-select)))))

(local (defthm fn-hpicol-select-zero
 (equal (fn-hpicol-select 0 rows) (adt-cars rows))
 :hints (("Goal" :induct (fn-hpicol-select 0 rows)
  :in-theory (e/d (fn-hpicol-select adt-cars nth) (adt-row-cells adt-rows-cells))))))
(local (defthm fn-hpicol-select-next
 (implies (and (natp column) (< 0 column))
  (equal (fn-hpicol-select column rows)
         (fn-hpicol-select (1- column) (adt-cdrs rows))))
 :hints (("Goal" :induct (fn-hpicol-select column rows)
  :in-theory (e/d (fn-hpicol-select adt-cdrs nth) (adt-row-cells adt-rows-cells))))))

(local (defthm fn-hpicol-transpose-four-unfolds
 (equal (adt-transpose 4 rows) (list (adt-cars rows) (adt-cars (adt-cdrs rows)) (adt-cars (adt-cdrs (adt-cdrs rows))) (adt-cars (adt-cdrs (adt-cdrs (adt-cdrs rows))))))
 :hints (("Goal" :expand ((adt-transpose 4 rows) (adt-transpose 3 (adt-cdrs rows)) (adt-transpose 2 (adt-cdrs (adt-cdrs rows))) (adt-transpose 1 (adt-cdrs (adt-cdrs (adt-cdrs rows)))) (adt-transpose 0 (adt-cdrs (adt-cdrs (adt-cdrs (adt-cdrs rows))))))
  :in-theory (disable adt-transpose adt-cars adt-cdrs)))))

(defthm fn-hpicol-history-model-is-existing-canonical-column
 (implies (and (natp column) (< column 4))
  (equal (fn-hpicol-history-model column h salt)
         (nth column (adt-transpose 4 (adt-rows-cells *fn-hp-schema* (fn-hp-rows h salt) 0)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :cases ((equal column 0) (equal column 1) (equal column 2) (equal column 3))
  :in-theory (e/d (fn-hpicol-history-model adt-transpose nth)
   (fn-hpicol-select adt-cars adt-cdrs fn-hp-rows fn-hp-row adt-rows-cells adt-row-cells)))))

(local (defthm fn-hpicol-rows-cells-append
 (implies (natp pos)
  (equal (adt-rows-cells s (append xs ys) pos)
         (append (adt-rows-cells s xs pos)
          (adt-rows-cells s ys (+ pos (len (adt-rows-pool s xs)))))))
 :hints (("Goal" :induct (adt-rows-cells s xs pos)
  :in-theory (e/d (adt-rows-cells adt-rows-pool) (adt-row-cells adt-row-pool))))))

(local (defthm fn-hpicol-actual-row-cells
 (equal (car (adt-row-cells *fn-hp-schema* (fn-hp-row ev salt) pos))
        (fn-hp-cells-of ev salt pos))
 :hints (("Goal" :in-theory (e/d (adt-row-cells adt-enc fn-hp-row fn-hp-cells-of)
   (fn-scc-encode fn-scc-program fn-hp-mkey fn-hp-pad8))))))

(local (defthm fn-hpicol-single-row
 (equal (adt-rows-cells *fn-hp-schema* (fn-hp-rows (list ev) salt) pos)
        (list (fn-hp-cells-of ev salt pos)))
 :hints (("Goal" :expand ((fn-hp-rows (list ev) salt)
                         (fn-hp-rows nil salt)
                         (adt-rows-cells *fn-hp-schema* (list (fn-hp-row ev salt)) pos))
  :in-theory (e/d (adt-rows-cells) (fn-hp-row adt-row-cells fn-hp-cells-of))))))

(defthm fn-hpicol-appended-history-adds-canonical-row-cell
 (equal (fn-hpicol-history-model column (append h (list ev)) salt)
        (append (fn-hpicol-history-model column h salt)
                (list (nth column (fn-hp-cells-of ev salt (fn-hp-pes-len h))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpicol-rows-cells-append (s *fn-hp-schema*) (xs (fn-hp-rows h salt))
                    (ys (list (fn-hp-row ev salt))) (pos 0)))
  :in-theory (e/d (fn-hpicol-history-model fn-hpicol-select)
    (fn-hp-rows fn-hp-row adt-rows-cells adt-row-cells fn-hp-cells-of
     adt-rows-pool fn-hp-pes fn-hp-pes-len nth)))))

(local (defthm fn-hpicol-select-length
 (equal (len (fn-hpicol-select column rows)) (len rows))
 :hints (("Goal" :induct (fn-hpicol-select column rows) :in-theory (enable fn-hpicol-select)))))

(defthm fn-hpicol-history-model-length
 (equal (len (fn-hpicol-history-model column h salt)) (len h))
 :hints (("Goal" :in-theory (e/d (fn-hpicol-history-model) (fn-hpicol-select adt-rows-cells fn-hp-rows)))))

(local (defthm fn-hpicol-nthcdr-append-one
 (implies (and (natp n) (<= n (len xs)))
  (equal (nthcdr n (append xs (list word))) (append (nthcdr n xs) (list word))))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr len)))))

(defthm fn-hpcx-column-write-extends-canonical-history-suffix
 (let* ((column (fn-hrcur-field 9 c))
        (old (fn-hpq-model-select column fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (r (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (natp page-base) (<= page-base (len h))
                (natp (fn-hpb-used old))
                (equal (fn-hpb-prefix old) (nthcdr page-base (fn-hpicol-history-model column h salt)))
                (equal (fn-hrcur-field 7 c) (fn-hp-mkey row salt))
                (equal (fn-hrcur-field 8 c) (len (fn-scc-encode row)))
                (equal (fn-hrcur-field 3 c) (fn-hp-pes-len h))
                (member-eq (car r) '(:column-stored :row-done)))
   (equal (fn-hpb-prefix (mv-nth (+ 3 column) r))
          (nthcdr page-base (fn-hpicol-history-model column (append h (list row)) salt)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpcx-column-selected-prefix)
        (:instance fn-hpicol-appended-history-adds-canonical-row-cell (ev row) (column (fn-hrcur-field 9 c)))
        (:instance fn-hpicol-nthcdr-append-one (n page-base)
                   (xs (fn-hpicol-history-model (fn-hrcur-field 9 c) h salt))
                   (word (nth (fn-hrcur-field 9 c) (fn-hp-cells-of row salt (fn-hp-pes-len h))))))
  :in-theory (e/d (mv-nth) (fn-hpcx-tick fn-hpq-model-select fn-hpb-used fn-hpb-prefix
    fn-hrcur-field fn-hp-mkey fn-scc-encode fn-hp-cells-of fn-hp-pes-len
    fn-hpicol-history-model nthcdr nth fn-hpicol-nthcdr-append-one)))))

(local (defthm fn-hpicol-tick-frames-other-column
 (let ((r (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (member-eq (car r) '(:column-stored :row-done))
                (natp other) (< other 5) (not (equal other (fn-hrcur-field 9 c))))
   (equal (mv-nth (+ 3 other) r)
          (fn-hpq-model-select other fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpq-put-frames-other-regions
          (region (fn-hrcur-field 9 c))
          (word (mv-nth 1 (fn-hcl-cell (fn-hrcur-field 9 c) (fn-hrcur-field 7 c)
                                      (fn-hrcur-field 8 c) (fn-hrcur-field 3 c))))))
  :cases ((equal other 0) (equal other 1) (equal other 2) (equal other 3) (equal other 4))
  :in-theory (e/d (fn-hpcx-tick fn-hpcx-shapep) (fn-hpcx-with fn-hpe-tick fn-hcl-cell
        fn-hpq-put fn-hcc-row fn-hrcur-field fn-hpq-model-select fn-hpb-used fn-hp-pad8-count
        fn-hpe-shapep fn-omk-tokenp fn-hpq-put-frames-other-regions mv-nth))))))

(local (defthm fn-hpicol-with-fields-by-definition
 (let ((next (fn-hpcx-with phase ordinal offset child token key encoded column c)))
  (and (equal (fn-hrcur-field 0 next) phase)
       (equal (fn-hrcur-field 2 next) ordinal)
       (equal (fn-hrcur-field 3 next) offset)
       (equal (fn-hrcur-field 6 next) token)
       (equal (fn-hrcur-field 7 next) key)
       (equal (fn-hrcur-field 8 next) encoded)
       (equal (fn-hrcur-field 9 next) column)
       (equal (fn-hrcur-field 10 next) (fn-hrcur-field 10 c))
       (equal (fn-hrcur-field 11 next) (fn-hrcur-field 11 c))))
 :hints (("Goal" :in-theory (enable fn-hpcx-with fn-hrcur-field)))))

(local (defthm fn-hpicol-column-progress-fields
 (let ((r (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (member-eq (car r) '(:column-stored :row-done))
   (and (equal (fn-hrcur-field 0 c) :columns)
        (natp (fn-hrcur-field 9 c)) (< (fn-hrcur-field 9 c) 4)
        (equal (fn-hrcur-field 6 (mv-nth 2 r)) (fn-hrcur-field 6 c))
        (equal (fn-hrcur-field 10 (mv-nth 2 r)) (fn-hrcur-field 10 c))
        (equal (fn-hrcur-field 11 (mv-nth 2 r)) (fn-hrcur-field 11 c))
        (equal (mv-nth 1 r) (if (equal (car r) :row-done) (fn-hrcur-field 8 c) (fn-hrcur-field 9 c)))
        (implies (equal (car r) :column-stored)
         (and (equal (fn-hrcur-field 0 (mv-nth 2 r)) :columns)
              (equal (fn-hrcur-field 2 (mv-nth 2 r)) (fn-hrcur-field 2 c))
              (equal (fn-hrcur-field 3 (mv-nth 2 r)) (fn-hrcur-field 3 c))
              (equal (fn-hrcur-field 7 (mv-nth 2 r)) (fn-hrcur-field 7 c))
              (equal (fn-hrcur-field 8 (mv-nth 2 r)) (fn-hrcur-field 8 c))
              (equal (fn-hrcur-field 9 (mv-nth 2 r)) (+ 1 (fn-hrcur-field 9 c)))))
        (implies (equal (car r) :row-done)
         (and (equal (fn-hrcur-field 9 c) 3)
              (member-eq (fn-hrcur-field 0 (mv-nth 2 r)) '(:need-row :prepared))
              (equal (fn-hrcur-field 9 (mv-nth 2 r)) 0))))))
 :hints (("Goal" :in-theory (e/d (fn-hpcx-tick fn-hpcx-shapep)
   (fn-hpcx-with fn-hrcur-field fn-hpe-tick fn-hcl-cell fn-hpq-put fn-hcc-row fn-hpe-shapep fn-omk-tokenp fn-hp-pad8-count mv-nth))))))

(defun fn-hpicol-carried-history (region h row c)
 (declare (xargs :guard t :verify-guards nil))
 (if (and (equal (fn-hrcur-field 0 c) :columns) (< region (fn-hrcur-field 9 c)))
     (append h (list row)) h))

(defun fn-hpicol-region-invariantp (region h row salt c pages fn-hpb)
 (declare (xargs :guard t :stobjs fn-hpb :verify-guards nil))
 (let* ((page-base (* 2048 (nfix (nth region pages))))
        (history (fn-hpicol-carried-history region h row c)))
  (and (natp (fn-hpb-used fn-hpb)) (<= (fn-hpb-used fn-hpb) 2048)
       (<= page-base (len history))
       (equal (fn-hpb-prefix fn-hpb)
              (nthcdr page-base (fn-hpicol-history-model region history salt))))))

(local (defthm fn-hpicol-put-used-increments
 (implies (equal (car (fn-hpb-put word buffer)) :stored)
  (equal (fn-hpb-used (mv-nth 1 (fn-hpb-put word buffer))) (+ 1 (fn-hpb-used buffer))))
 :hints (("Goal" :in-theory (enable fn-hpb-put fn-hpb-used)))))

(local (defthm fn-hpicol-selected-used-increments
 (let ((r (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (member-eq (car r) '(:column-stored :row-done))
   (and (< (fn-hpb-used (fn-hpq-model-select (fn-hrcur-field 9 c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) 2048)
        (equal (fn-hpb-used (mv-nth (+ 3 (fn-hrcur-field 9 c)) r))
               (+ 1 (fn-hpb-used (fn-hpq-model-select (fn-hrcur-field 9 c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))))
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-hrcur-field 9 c) 0) (equal (fn-hrcur-field 9 c) 1) (equal (fn-hrcur-field 9 c) 2) (equal (fn-hrcur-field 9 c) 3))
  :in-theory (e/d (fn-hpcx-tick fn-hpq-put fn-hpq-model-select fn-hpb-put fn-hpb-used fn-hpcx-shapep)
    (fn-hpcx-with fn-hpe-tick fn-hcl-cell fn-hcc-row fn-hrcur-field mv-nth fn-hpe-shapep fn-omk-tokenp fn-hp-pad8-count))))))

(defthm fn-hpcx-column-write-preserves-canonical-region
 (let* ((old (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (r (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (natp region) (< region 4)
                (fn-hpicol-region-invariantp region h row salt c pages old)
                (equal (fn-hrcur-field 7 c) (fn-hp-mkey row salt))
                (equal (fn-hrcur-field 8 c) (len (fn-scc-encode row)))
                (equal (fn-hrcur-field 3 c) (fn-hp-pes-len h))
                (member-eq (car r) '(:column-stored :row-done)))
   (fn-hpicol-region-invariantp region
        (if (equal (car r) :row-done) (append h (list row)) h) row salt
        (mv-nth 2 r) pages (mv-nth (+ 3 region) r))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal region (fn-hrcur-field 9 c)) (equal (car (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :row-done))
  :use (fn-hpicol-column-progress-fields fn-hpicol-selected-used-increments
        (:instance fn-hpcx-column-write-extends-canonical-history-suffix
           (page-base (* 2048 (nfix (nth region pages))))))
  :in-theory (e/d (fn-hpicol-region-invariantp fn-hpicol-carried-history)
    (fn-hpcx-tick fn-hpcx-with fn-hpq-model-select fn-hpb-used fn-hpb-prefix
     fn-hrcur-field fn-hp-mkey fn-scc-encode fn-hp-cells-of fn-hp-pes-len
     fn-hpicol-history-model fn-hpicol-column-progress-fields fn-hpicol-selected-used-increments fn-scc-encode-is-program nthcdr nth mv-nth)))))

(local (defthm fn-hpicol-pes-len-append
 (equal (fn-hp-pes-len (append h tail)) (+ (fn-hp-pes-len h) (fn-hp-pes-len tail)))
 :hints (("Goal" :induct (fn-hp-pes-len h) :in-theory (e/d (fn-hp-pes-len) (fn-hp-pe))))))

(local (defthm fn-hpicol-one-row-pool
 (equal (fn-hp-pes-len (list row)) (+ (len (fn-scc-encode row)) (fn-hp-pad8-count (len (fn-scc-encode row)))))
 :hints (("Goal" :in-theory (e/d (fn-hp-pes-len fn-hp-pe)
   (fn-hp-pe-is-pad8 fn-hp-pad8-count fn-scc-encode fn-scc-encode-is-program fn-scc-program fn-hp-pad8))))))

(defun fn-hpicol-four-invariantp (h row salt c pages fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) :verify-guards nil))
 (and (fn-hpcx-shapep c)
      (member-eq (fn-hrcur-field 0 c) '(:columns :need-row :prepared))
      (equal (fn-hrcur-field 2 c) (len h))
      (equal (fn-hrcur-field 3 c) (fn-hp-pes-len h))
      (implies (equal (fn-hrcur-field 0 c) :columns)
       (and (equal (fn-hrcur-field 7 c) (fn-hp-mkey row salt))
            (equal (fn-hrcur-field 8 c) (len (fn-scc-encode row)))))
      (fn-hpicol-region-invariantp 0 h row salt c pages fn-hpq0)
      (fn-hpicol-region-invariantp 1 h row salt c pages fn-hpq1)
      (fn-hpicol-region-invariantp 2 h row salt c pages fn-hpq2)
      (fn-hpicol-region-invariantp 3 h row salt c pages fn-hpq3)))

(local (defthm fn-hpicol-mv-zero (equal (mv-nth 0 x) (car x))
 :hints (("Goal" :in-theory (enable mv-nth)))))

(defthm fn-hpcx-column-write-preserves-full-canonical-column-carry
 (let ((r (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (fn-hpicol-four-invariantp h row salt c pages fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
                (member-eq (car r) '(:column-stored :row-done)))
   (and (fn-hpicol-four-invariantp
          (if (equal (car r) :row-done) (append h (list row)) h) row salt
          (mv-nth 2 r) pages (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))
        (equal (mv-nth 7 r) fn-hpb)
        (equal (fn-hrcur-field 6 (mv-nth 2 r)) (fn-hrcur-field 6 c))
        (equal (fn-hrcur-field 10 (mv-nth 2 r)) (fn-hrcur-field 10 c))
        (equal (fn-hrcur-field 11 (mv-nth 2 r)) (fn-hrcur-field 11 c))
        (equal (mv-nth 1 r) (if (equal (car r) :row-done) (len (fn-scc-encode row)) (fn-hrcur-field 9 c)))
        (implies (equal (car r) :column-stored)
          (and (equal (fn-hrcur-field 2 (mv-nth 2 r)) (fn-hrcur-field 2 c))
               (equal (fn-hrcur-field 3 (mv-nth 2 r)) (fn-hrcur-field 3 c))
               (equal (fn-hrcur-field 9 (mv-nth 2 r)) (+ 1 (fn-hrcur-field 9 c)))))
        (implies (equal (car r) :row-done)
          (and (equal (fn-hrcur-field 2 (mv-nth 2 r)) (+ 1 (len h)))
               (equal (fn-hrcur-field 3 (mv-nth 2 r)) (fn-hp-pes-len (append h (list row)))))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal (car (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :row-done))
  :use (fn-hpicol-column-progress-fields fn-hpcx-row-done-advances-once
        (:instance fn-hpicol-tick-frames-other-column (other 4))
        (:instance fn-hpcx-column-write-preserves-canonical-region (region 0))
        (:instance fn-hpcx-column-write-preserves-canonical-region (region 1))
        (:instance fn-hpcx-column-write-preserves-canonical-region (region 2))
        (:instance fn-hpcx-column-write-preserves-canonical-region (region 3)))
  :in-theory (e/d (fn-hpicol-four-invariantp fn-hpq-model-select)
    (fn-hpcx-tick fn-hpcx-shapep fn-hpb-used fn-hpb-prefix
     fn-hrcur-field fn-hp-mkey fn-scc-encode fn-scc-encode-is-program fn-hp-pe fn-hp-pad8-count
     fn-hp-pes-len fn-hpicol-column-progress-fields fn-hpicol-history-model fn-hpicol-region-invariantp nthcdr nth mv-nth)))))

(local (defthm fn-hpicol-column-output-classes
 (implies (equal (fn-hrcur-field 0 c) :columns)
  (member-equal (car (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
   '(:column-stored :row-done :page-full (:refused :cursor) (:refused :census) (:refused :cell))))
 :hints (("Goal" :in-theory (e/d (fn-hpcx-tick)
   (fn-hpcx-shapep fn-hpcx-with fn-hrcur-field fn-hcl-cell fn-hpq-put fn-hcc-row fn-hpe-tick mv-nth))))))

(local (defthm fn-hpicol-selector-equivalence-by-definition
 (equal (fn-omk-at n x) (fn-hrcur-field n x))
 :rule-classes nil
 :hints (("Goal" :induct (fn-omk-at n x) :in-theory (enable fn-omk-at fn-hrcur-field)))))

(local (defthm fn-hpicol-token-selector-by-definition
 (equal (fn-omk-at 6 x) (fn-hrcur-field 6 x))
 :hints (("Goal" :use ((:instance fn-hpicol-selector-equivalence-by-definition (n 6)))
                 :in-theory (disable fn-omk-at fn-hrcur-field)))))

(local (defthm fn-hpicol-await-region-is-not-column-progress
 (and (not (equal (car (fn-hpi-await-region region resume c)) :continue))
      (not (equal (car (fn-hpi-await-region region resume c)) :row-done)))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-region fn-hpi-await-page)
   (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-hpi-write-effect fn-hpi-region-cap fn-hpi-region-start))))))

(local (defthm fn-hpicol-outer-complete-output
 (let* ((body (fn-omk-at 14 c))
        (inner (fn-hpcx-tick body fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :body)
                (equal (fn-hrcur-field 0 body) :columns)
                (member-eq (car r) '(:continue :row-done)))
   (and (member-eq (car inner) '(:column-stored :row-done))
        (equal (car r) (if (equal (car inner) :row-done) :row-done :continue))
        (equal r
          (mv (if (equal (car inner) :row-done) :row-done :continue)
              (if (equal (car inner) :row-done)
                  (list :row-emitted (fn-hrcur-field 6 (mv-nth 2 inner)) (mv-nth 1 inner)) nil)
              (fn-hpi-set 14 (mv-nth 2 inner) c) ledger
              (mv-nth 3 inner) (mv-nth 4 inner) (mv-nth 5 inner) (mv-nth 6 inner) (mv-nth 7 inner)
              pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpicol-column-output-classes (c (fn-omk-at 14 c))))
  :in-theory (e/d (fn-hpi-tick fn-hpi-buffer-step fn-hpi-supply fn-hpcx-supply fn-hsrcb-demandp)
   (fn-hpi-written fn-hpi-stream-step fn-hpcx-tick fn-hpcx-shapep fn-hpcx-with fn-hrcur-field
    fn-hpi-grant-matchesp fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpi-await-region fn-hpi-await-page fn-hpi-reset-buffer fn-osj-native-grow
    fn-hpe-supply fn-hpe-tick fn-hpq-put fn-hpb-put fn-hcl-cell fn-hcc-row
    fn-hpb-used fn-hpi-region-cap fn-hpi-region-used mv-nth fn-hpicol-column-output-classes)))))
)

(local
 (defun fn-hpicol-field-ind (j k c)
  (if (or (zp j) (zp k)) (list j k c)
    (fn-hpicol-field-ind (1- j) (1- k) (if (consp c) (cdr c) nil)))))

(local
 (defthm fn-hpicol-set-field
  (implies (and (natp k) (< k 25) (natp j) (< j 25))
   (equal (fn-omk-at j (fn-hpi-set k value c))
          (if (equal j k) value (fn-omk-at j c))))
  :hints (("Goal" :induct (fn-hpicol-field-ind j k c)
           :expand ((fn-hpi-set k value c)
                    (fn-omk-at j c)
                    (fn-omk-at j (fn-hpi-set k value c))
                    (:free (a d) (fn-omk-at j (cons a d))))
           :in-theory (e/d (fn-omk-at fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))

(local (defthm fn-hpicol-outer-body-update-fields-by-definition
 (and (equal (fn-omk-at 12 (fn-hpi-set 14 body c)) (fn-omk-at 12 c))
      (equal (fn-omk-at 0 (fn-hpi-set 14 body c)) (fn-omk-at 0 c))
      (equal (fn-omk-at 14 (fn-hpi-set 14 body c)) body)
      (equal (fn-omk-at 15 (fn-hpi-set 14 body c)) (fn-omk-at 15 c)))
 :hints (("Goal" :in-theory (disable fn-hpi-set fn-omk-at fn-hpi-set-is-update-by-definition)))))

(defun fn-hpicol-writer-ready-p (h row salt c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) :verify-guards nil))
 (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :body)
      (equal (fn-omk-at 12 c) salt)
      (equal (fn-hrcur-field 0 (fn-omk-at 14 c)) :columns)
      (fn-hpicol-four-invariantp h row salt (fn-omk-at 14 c) (fn-omk-at 15 c)
                                fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)))

(local (defthm fn-hpicol-four-carry-scalar-positions
 (implies (fn-hpicol-four-invariantp h row salt c pages fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
  (and (equal (fn-hrcur-field 2 c) (len h))
       (equal (fn-hrcur-field 3 c) (fn-hp-pes-len h))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-hpicol-four-invariantp)
  (fn-hpcx-shapep fn-hrcur-field fn-hp-pes-len fn-hpicol-region-invariantp fn-hp-mkey fn-scc-encode fn-scc-encode-is-program))))))

(defthm fn-hpi-column-step-preserves-full-canonical-column-carry
 (let* ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
        (next (mv-nth 2 r))
        (inner (fn-hpcx-tick (fn-omk-at 14 c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (fn-hpicol-writer-ready-p h row salt c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
                (member-eq (car r) '(:continue :row-done)))
   (and (fn-hpicol-four-invariantp
          (if (equal (car r) :row-done) (append h (list row)) h) row salt
          (fn-omk-at 14 next) (fn-omk-at 15 next) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r))
        (equal (fn-omk-at 0 next) :body)
        (equal (fn-omk-at 12 next) salt)
        (equal next (fn-hpi-set 14 (mv-nth 2 inner) c))
        (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 8 r) fn-hpb) (equal (mv-nth 9 r) pgs-digest-state)
        (equal (mv-nth 1 r)
               (if (equal (car r) :row-done)
                   (list :row-emitted (fn-hrcur-field 6 (fn-omk-at 14 c)) (len (fn-scc-encode row))) nil))
        (equal (fn-hrcur-field 10 (fn-omk-at 14 next)) (fn-hrcur-field 10 (fn-omk-at 14 c)))
        (equal (fn-hrcur-field 11 (fn-omk-at 14 next)) (fn-hrcur-field 11 (fn-omk-at 14 c)))
        (implies (equal (car r) :continue)
         (and (equal (fn-hrcur-field 2 (fn-omk-at 14 next)) (len h))
              (equal (fn-hrcur-field 3 (fn-omk-at 14 next)) (fn-hp-pes-len h))
              (equal (fn-hrcur-field 9 (fn-omk-at 14 next)) (+ 1 (fn-hrcur-field 9 (fn-omk-at 14 c))))))
        (implies (equal (car r) :row-done)
         (and (equal (fn-hrcur-field 2 (fn-omk-at 14 next)) (+ 1 (len h)))
              (equal (fn-hrcur-field 3 (fn-omk-at 14 next)) (fn-hp-pes-len (append h (list row)))))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpicol-outer-complete-output
        (:instance fn-hpicol-four-carry-scalar-positions (c (fn-omk-at 14 c)) (pages (fn-omk-at 15 c)))
        (:instance fn-hpcx-column-write-preserves-full-canonical-column-carry
         (c (fn-omk-at 14 c)) (pages (fn-omk-at 15 c))))
  :in-theory (e/d (fn-hpicol-writer-ready-p mv-nth)
    (fn-hpi-tick fn-hpcx-tick fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
     fn-hrcur-field fn-hpicol-four-invariantp fn-hpicol-region-invariantp
     fn-hp-mkey fn-scc-encode fn-scc-encode-is-program fn-hp-pes-len)))))
