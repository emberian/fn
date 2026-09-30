(in-package "ACL2")
(include-book "../../books/history-pool-columns")
(include-book "../../books/history-page-cursor")

(defun hpct-run-pool (fuel c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
  (if (zp fuel) (mv :fuel nil c c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
    (mv-let (v n next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
      (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
      (if (eq v :continue) (hpct-run-pool (1- fuel) next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (mv v n next c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))

(defun hpct-fill (left fn-hpb)
  (declare (xargs :stobjs fn-hpb :verify-guards nil))
  (if (zp left) fn-hpb
    (mv-let (v fn-hpb) (fn-hpb-put 0 fn-hpb)
      (declare (ignore v)) (hpct-fill (1- left) fn-hpb))))

; Literal complete prefix-effect antecedent and conclusion for each actual step.
(defun hpct-column (c row salt fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
  (let* ((column (fn-hrcur-field 9 c))
         (prior (case column (0 (fn-hpb-prefix fn-hpq0)) (1 (fn-hpb-prefix fn-hpq1))
                      (2 (fn-hpb-prefix fn-hpq2)) (otherwise (fn-hpb-prefix fn-hpq3))))
         (used (case column (0 (fn-hpb-used fn-hpq0)) (1 (fn-hpb-used fn-hpq1))
                     (2 (fn-hpb-used fn-hpq2)) (otherwise (fn-hpb-used fn-hpq3))))
         (antecedent (and (natp used)
                          (equal (fn-hrcur-field 7 c) (fn-hp-mkey row salt))
                          (equal (fn-hrcur-field 8 c) (len (fn-scc-encode row))))))
    (mv-let (v n next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
      (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
      (declare (ignore n))
      (mv (and antecedent (member-eq v '(:column-stored :row-done))
               (equal (case column (0 (fn-hpb-prefix fn-hpq0)) (1 (fn-hpb-prefix fn-hpq1))
                    (2 (fn-hpb-prefix fn-hpq2)) (otherwise (fn-hpb-prefix fn-hpq3)))
                      (append prior (list (nth column (fn-hp-cells-of row salt (fn-hrcur-field 3 c))))))
               (equal (fn-hrcur-field 10 next) (fn-hrcur-field 10 c))
               (equal (fn-hrcur-field 11 next) (fn-hrcur-field 11 c)))
          next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))

(defun hpct-row-resume (row)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0
 (mv-let (ok fn-hpq0)
  (with-local-stobj fn-hpq1
 (mv-let (ok fn-hpq0 fn-hpq1)
  (with-local-stobj fn-hpq2
 (mv-let (ok fn-hpq0 fn-hpq1 fn-hpq2)
  (with-local-stobj fn-hpq3
 (mv-let (ok fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
  (with-local-stobj fn-hpb
 (mv-let (ok fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (mv-let (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (fn-hpq-begin 'capture 'resource fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (let* ((fn-hpq1 (hpct-fill 2048 fn-hpq1))
        (encoded (len (fn-scc-encode row)))
        (padded (+ encoded (fn-hp-pad8-count encoded)))
        (token '(7 (9 1) 1 0))
        (initial (fn-hpcx-begin 1 padded token 'capture 'resource))
        (offered (nth 1 (mv-list 2 (fn-hpcx-offer initial 0 (list :resident row) token (fn-hp-mkey row 17))))))
 (mv-let (v n columns before fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (hpct-run-pool 1000 offered fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (let ((prepared-positive
         (and (fn-hpe-invariantp (fn-hrcur-field 5 before))
              (equal (fn-hpe-total (fn-hrcur-field 5 before)) (len (fn-scc-encode row)))
              (equal v :columns) (equal n encoded)
              (fn-hpe-invariantp (fn-hrcur-field 5 columns))
              (equal (fn-hpe-total (fn-hrcur-field 5 columns)) encoded)
              (equal (fn-hrcur-field 8 columns) encoded)
              (equal (fn-hpb-prefix fn-hpb) (fn-hp-pack8 (ceiling padded 8) (fn-hp-pe row))))))
   (mv-let (ok0 c1 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
    (hpct-column columns row 17 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
    (let ((old0 (fn-hpb-prefix fn-hpq0)) (old1 (fn-hpb-prefix fn-hpq1)) (old2 (fn-hpb-prefix fn-hpq2)) (old3 (fn-hpb-prefix fn-hpq3)) (oldpool (fn-hpb-prefix fn-hpb)))
     (mv-let (full col held fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
      (fn-hpcx-tick c1 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
      (let* ((page-positive
              (and (equal (fn-hrcur-field 0 c1) :columns) (equal full :page-full)
                   (equal col 1) (equal held c1)
                   (equal (fn-hpb-prefix fn-hpq0) old0) (equal (fn-hpb-prefix fn-hpq1) old1) (equal (fn-hpb-prefix fn-hpq2) old2)
                   (equal (fn-hpb-prefix fn-hpq3) old3) (equal (fn-hpb-prefix fn-hpb) oldpool)
                   (equal (nth 0 (mv-list 2 (fn-hpcx-offer held 0 (list :resident row) token 0))) :stale)
                   (equal (nth 1 (mv-list 2 (fn-hpcx-offer held 0 (list :resident row) token 0))) held)))
             (fn-hpq1 (fn-hpb-begin 'capture 'resource fn-hpq1)))
       (mv-let (ok1 c2 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (hpct-column held row 17 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (mv-let (ok2 c3 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
         (hpct-column c2 row 17 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
         (let ((antecedent3 (and (natp (fn-hpb-used fn-hpq3))
                                 (equal (fn-hrcur-field 7 c3) (fn-hp-mkey row 17))
                                 (equal (fn-hrcur-field 8 c3) (len (fn-scc-encode row))))))
         (mv-let (done n final fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
          (fn-hpcx-tick c3 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
          (mv (and prepared-positive page-positive ok0 ok1 ok2 antecedent3
                   (equal done :row-done) (equal n encoded)
                   (equal (fn-hrcur-field 0 c3) :columns) (equal (fn-hrcur-field 9 c3) 3)
                   (equal (fn-hrcur-field 2 final) (+ 1 (fn-hrcur-field 2 c3)))
                   (equal (fn-hrcur-field 3 final) (+ (fn-hrcur-field 3 c3) encoded (fn-hp-pad8-count encoded)))
                   (equal (fn-hpb-prefix fn-hpq3) (list padded))
                   (equal (fn-hrcur-field 0 final) :prepared)
                   (equal (nth 0 (mv-list 2 (fn-hpcx-offer final 0 (list :resident row) token 0))) :stale)
                   (equal (nth 1 (mv-list 2 (fn-hpcx-offer final 0 (list :resident row) token 0))) final)
                   (fn-hpbp fn-hpq0) (fn-hpbp fn-hpq1) (fn-hpbp fn-hpq2)
                   (fn-hpbp fn-hpq3) (fn-hpbp fn-hpb))
              fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))))))))))
  (mv ok fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)))
  (mv ok fn-hpq0 fn-hpq1 fn-hpq2)))
  (mv ok fn-hpq0 fn-hpq1)))
  (mv ok fn-hpq0)))
  ok)))
(assert-event (hpct-row-resume '(1 2 3)))
(assert-event (hpct-row-resume "hello"))

; Corrupted state/argument mutation: every retained literal premise is checked.
(defthm hpct-remove-prefix-used-nat
 (let* ((row "hello") (salt 17) (column 0)
        (encoded (len (fn-scc-encode row)))
        (s (update-fn-hpb-used -1 (create-fn-hpb)))
        (c (list :columns 1 0 0 (+ encoded (fn-hp-pad8-count encoded)) nil
                 '(7 (9 1) 1 0) (fn-hp-mkey row salt) encoded column 'capture 'resource))
        (r (fn-hpcx-tick c s s s s s)))
 (and (not (natp (fn-hpb-used s))) (equal (fn-hrcur-field 7 c) (fn-hp-mkey row salt)) (equal (fn-hrcur-field 8 c) (len (fn-scc-encode row))) (member-eq (mv-nth 0 r) '(:column-stored :row-done))
      (not (equal (fn-hpb-prefix (mv-nth (+ 3 column) r))
                  (append (fn-hpb-prefix s)
                          (list (nth column (fn-hp-cells-of row salt 0))))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-tick fn-hpcx-shapep fn-hpcx-with fn-hpq-put fn-hpb-put
    fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-used fn-hcc-row fn-hcl-cell fn-omk-tokenp fn-omk-widthp fn-omk-at))))

; Corrupted state/argument mutation: every retained literal premise is checked.
(defthm hpct-remove-prefix-key
 (let* ((row "hello") (salt 17) (column 0)
        (encoded (len (fn-scc-encode row)))
        (s (create-fn-hpb))
        (c (list :columns 1 0 0 (+ encoded (fn-hp-pad8-count encoded)) nil
                 '(7 (9 1) 1 0) 1 encoded column 'capture 'resource))
        (r (fn-hpcx-tick c s s s s s)))
 (and (natp (fn-hpb-used s)) (not (equal (fn-hrcur-field 7 c) (fn-hp-mkey row salt))) (equal (fn-hrcur-field 8 c) (len (fn-scc-encode row))) (member-eq (mv-nth 0 r) '(:column-stored :row-done))
      (not (equal (fn-hpb-prefix (mv-nth (+ 3 column) r))
                  (append (fn-hpb-prefix s)
                          (list (nth column (fn-hp-cells-of row salt 0))))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-tick fn-hpcx-shapep fn-hpcx-with fn-hpq-put fn-hpb-put
    fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-used fn-hcc-row fn-hcl-cell fn-omk-tokenp fn-omk-widthp fn-omk-at))))

; Corrupted state/argument mutation: every retained literal premise is checked.
(defthm hpct-remove-prefix-encoded
 (let* ((row "hello") (salt 17) (column 1)
        (encoded (len (fn-scc-encode row)))
        (s (create-fn-hpb))
        (c (list :columns 2 0 0 64 nil
                 '(7 (9 2) 1 0) (fn-hp-mkey row salt) (+ 1 encoded) column 'capture 'resource))
        (r (fn-hpcx-tick c s s s s s)))
 (and (natp (fn-hpb-used s)) (equal (fn-hrcur-field 7 c) (fn-hp-mkey row salt)) (not (equal (fn-hrcur-field 8 c) (len (fn-scc-encode row)))) (member-eq (mv-nth 0 r) '(:column-stored :row-done))
      (not (equal (fn-hpb-prefix (mv-nth (+ 3 column) r))
                  (append (fn-hpb-prefix s)
                          (list (nth column (fn-hp-cells-of row salt 0))))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-tick fn-hpcx-shapep fn-hpcx-with fn-hpq-put fn-hpb-put
    fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-used fn-hcc-row fn-hcl-cell fn-omk-tokenp fn-omk-widthp fn-omk-at))))

; Corrupted state/argument mutation: every retained literal premise is checked.
(defthm hpct-remove-prefix-stored
 (let* ((row "hello") (salt 17) (column 0)
        (encoded (len (fn-scc-encode row)))
        (s (create-fn-hpb))
        (c (list :prepared 1 0 0 (+ encoded (fn-hp-pad8-count encoded)) nil
                 '(7 (9 1) 1 0) (fn-hp-mkey row salt) encoded column 'capture 'resource))
        (r (fn-hpcx-tick c s s s s s)))
 (and (natp (fn-hpb-used s)) (equal (fn-hrcur-field 7 c) (fn-hp-mkey row salt)) (equal (fn-hrcur-field 8 c) (len (fn-scc-encode row))) (not (member-eq (mv-nth 0 r) '(:column-stored :row-done)))
      (not (equal (fn-hpb-prefix (mv-nth (+ 3 column) r))
                  (append (fn-hpb-prefix s)
                          (list (nth column (fn-hp-cells-of row salt 0))))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-tick fn-hpcx-shapep fn-hpcx-with fn-hpq-put fn-hpb-put
    fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-used fn-hcc-row fn-hcl-cell fn-omk-tokenp fn-omk-widthp fn-omk-at))))

; Corrupted child/argument mutation: all retained attribution premises checked.
(defthm hpct-remove-attribution-invariant
 (let* ((row "hello") (token '(7 (9 2) 1 0)) (s (create-fn-hpb))
        (n (len (fn-scc-encode row)))
        (child (list :prepared (fn-hrcur-byte-begin (list :resident row) token 'resource) 0 0 0 token 'resource))
        (c (list :pool 2 0 0 64 child token 0 0 0 'capture 'resource))
        (r (fn-hpcx-tick c s s s s s)))
   (declare (ignorable n))
   (and (not (fn-hpe-invariantp (fn-hrcur-field 5 c))) (equal (fn-hpe-total (fn-hrcur-field 5 c)) (len (fn-scc-encode row))) (equal (mv-nth 0 r) :columns)
        (not (equal (fn-hrcur-field 8 (mv-nth 2 r)) (len (fn-scc-encode row))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-tick fn-hpcx-shapep fn-hpcx-with fn-hpe-tick
    fn-hpe-total fn-hpe-invariantp fn-hpe-shapep fn-hrcur-byte-begin fn-hrcur-byte-rest fn-hrcur-byte-invariantp
    fn-hcc-row fn-omk-tokenp fn-omk-widthp fn-omk-at))))

; Corrupted child/argument mutation: all retained attribution premises checked.
(defthm hpct-remove-attribution-total
 (let* ((row "hello") (token '(7 (9 2) 1 0)) (s (create-fn-hpb))
        (n (len (fn-scc-encode row)))
        (child (list :prepared (list :done (list nil token 'resource) nil token 'resource nil) 0 0 0 token 'resource))
        (c (list :pool 2 0 0 64 child token 0 0 0 'capture 'resource))
        (r (fn-hpcx-tick c s s s s s)))
   (declare (ignorable n))
   (and (fn-hpe-invariantp (fn-hrcur-field 5 c)) (not (equal (fn-hpe-total (fn-hrcur-field 5 c)) (len (fn-scc-encode row)))) (equal (mv-nth 0 r) :columns)
        (not (equal (fn-hrcur-field 8 (mv-nth 2 r)) (len (fn-scc-encode row))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-tick fn-hpcx-shapep fn-hpcx-with fn-hpe-tick
    fn-hpe-total fn-hpe-invariantp fn-hpe-shapep fn-hrcur-byte-begin fn-hrcur-byte-rest fn-hrcur-byte-invariantp
    fn-hcc-row fn-omk-tokenp fn-omk-widthp fn-omk-at))))

; Corrupted child/argument mutation: all retained attribution premises checked.
(defthm hpct-remove-attribution-prepared
 (let* ((row "hello") (token '(7 (9 2) 1 0)) (s (create-fn-hpb))
        (n (len (fn-scc-encode row)))
        (child (list :prepared (list :done (list nil token 'resource) nil token 'resource nil) 0 0 n token 'resource))
        (c (list :need-row 2 0 0 64 child token 0 0 0 'capture 'resource))
        (r (fn-hpcx-tick c s s s s s)))
   (declare (ignorable n))
   (and (fn-hpe-invariantp (fn-hrcur-field 5 c)) (equal (fn-hpe-total (fn-hrcur-field 5 c)) (len (fn-scc-encode row))) (not (equal (mv-nth 0 r) :columns))
        (not (equal (fn-hrcur-field 8 (mv-nth 2 r)) (len (fn-scc-encode row))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-tick fn-hpcx-shapep fn-hpcx-with fn-hpe-tick
    fn-hpe-total fn-hpe-invariantp fn-hpe-shapep fn-hrcur-byte-begin fn-hrcur-byte-rest fn-hrcur-byte-invariantp
    fn-hcc-row fn-omk-tokenp fn-omk-widthp fn-omk-at))))

; Reachable full-page positive, with the literal whole-state conclusion.
(defthm hpct-page-full-positive
 (let* ((row "hello") (s (create-fn-hpb)) (full (hpct-fill 2048 s))
        (n (len (fn-scc-encode row))) (token '(7 (9 1) 1 0))
        (initial (fn-hpcx-begin 1 (+ n (fn-hp-pad8-count n)) token 'capture 'resource))
        (offered (mv-nth 1 (fn-hpcx-offer initial 0 (list :resident row) token (fn-hp-mkey row 17))))
        (r0 (hpct-run-pool 1000 offered s full s s s))
        (r1 (fn-hpcx-tick (mv-nth 2 r0) (mv-nth 4 r0) (mv-nth 5 r0) (mv-nth 6 r0) (mv-nth 7 r0) (mv-nth 8 r0)))
        (c (mv-nth 2 r1))
        (r2 (fn-hpcx-tick c (mv-nth 3 r1) (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1) (mv-nth 7 r1))))
   (and (equal (fn-hrcur-field 0 c) :columns)
        (equal (mv-nth 0 r2) :page-full)
        (equal (mv-nth 2 r2) c)
        (equal (mv-nth 3 r2) (mv-nth 3 r1))
        (equal (mv-nth 4 r2) (mv-nth 4 r1))
        (equal (mv-nth 5 r2) (mv-nth 5 r1))
        (equal (mv-nth 6 r2) (mv-nth 6 r1))
        (equal (mv-nth 7 r2) (mv-nth 7 r1))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-begin fn-hpcx-offer fn-hpcx-tick))))

; Removing :page-full allows an actual stored cell to change its selected page.
(defthm hpct-remove-page-full-verdict
 (let* ((row "hello") (n (len (fn-scc-encode row))) (s (create-fn-hpb))
        (c (list :columns 1 0 0 (+ n (fn-hp-pad8-count n)) nil '(7 (9 1) 1 0) 0 n 0 'capture 'resource))
        (r (fn-hpcx-tick c s s s s s)))
   (and (equal (fn-hrcur-field 0 c) :columns)
        (not (equal (mv-nth 0 r) :page-full))
        (not (and (equal (mv-nth 2 r) c) (equal (mv-nth 3 r) s)
                  (equal (mv-nth 4 r) s) (equal (mv-nth 5 r) s)
                  (equal (mv-nth 6 r) s) (equal (mv-nth 7 r) s)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-tick fn-hpcx-shapep fn-hpcx-with fn-hpq-put fn-hpb-put fn-hcc-row fn-hcl-cell))))

; Stale scalar/token offers are refused before a child or page is mutated.
(defthm hpct-stale-offers
 (let* ((token '(7 (9 2) 1 0)) (c (fn-hpcx-begin 2 64 token 'capture 'resource)))
   (and (equal (mv-nth 0 (fn-hpcx-offer c 1 '(:resident nil) token 0)) :stale)
        (equal (mv-nth 1 (fn-hpcx-offer c 1 '(:resident nil) token 0)) c)
        (equal (mv-nth 0 (fn-hpcx-offer c 0 '(:resident nil) '(7 (9 2) 0 0) 0)) :stale)
        (equal (mv-nth 1 (fn-hpcx-offer c 0 '(:resident nil) '(7 (9 2) 0 0) 0)) c)
        (equal (mv-nth 0 (fn-hpcx-offer c 0 '(:resident nil) '(8 (9 2) 1 0) 0)) :stale)
        (equal (mv-nth 1 (fn-hpcx-offer c 0 '(:resident nil) '(8 (9 2) 1 0) 0)) c)
        (equal (mv-nth 0 (fn-hpcx-offer c 0 '(:resident nil) '(7 (10 2) 1 0) 0)) :stale)
        (equal (mv-nth 1 (fn-hpcx-offer c 0 '(:resident nil) '(7 (10 2) 1 0) 0)) c)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-begin fn-hpcx-offer))))

; Logical width-edge mutations, not claims about physically reachable files.
(defthm hpct-width-refusals-before-columns
 (let* ((s (create-fn-hpb)) (token '(7 (9 2) 1 0))
        (child (list :prepared (list :done (list nil token 'resource) nil token 'resource nil)
                     0 0 8 token 'resource))
        (c (list :pool 2 0 18446744073709551612 18446744073709551615 child token 0 0 0 'capture 'resource))
        (r (fn-hpcx-tick c s s s s s)))
   (and (equal (fn-hrcur-field 0 (fn-hpcx-begin 2305843009213693952 0 token 'capture 'resource)) :refused)
        (fn-hpcx-shapep c)
        (equal (mv-nth 0 r) '(:refused :census))
        (equal (fn-hrcur-field 2 (mv-nth 2 r)) 0)
        (equal (fn-hrcur-field 3 (mv-nth 2 r)) 18446744073709551612)
        (equal (mv-nth 3 r) s) (equal (mv-nth 4 r) s) (equal (mv-nth 5 r) s)
        (equal (mv-nth 6 r) s) (equal (mv-nth 7 r) s)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-begin fn-hpcx-tick fn-hpcx-shapep))))

; Argument mutation: removing row-done permits a need-row stationary step.
(defthm hpct-remove-row-done
 (let* ((s (create-fn-hpb)) (c (fn-hpcx-begin 1 8 '(7 (9 1) 1 0) 'capture 'resource))
        (r (fn-hpcx-tick c s s s s s)))
   (and (not (equal (mv-nth 0 r) :row-done))
        (not (and (equal (fn-hrcur-field 0 c) :columns)
                  (equal (fn-hrcur-field 9 c) 3)
                  (equal (fn-hrcur-field 2 (mv-nth 2 r)) (+ 1 (fn-hrcur-field 2 c)))
                  (equal (fn-hrcur-field 3 (mv-nth 2 r))
                         (+ (fn-hrcur-field 3 c) (fn-hrcur-field 8 c)
                            (fn-hp-pad8-count (fn-hrcur-field 8 c))))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-begin fn-hpcx-tick))))

; Complete literal offered-resident boundary on an actual nonempty row.
(defthm hpct-offered-resident-positive
 (let* ((row "hello") (token '(7 (9 1) 1 0)) (n (len (fn-scc-encode row)))
        (c (fn-hpcx-begin 1 (+ n (fn-hp-pad8-count n)) token 'capture 'resource))
        (r (fn-hpcx-offer c 0 (list :resident row) token (fn-hp-mkey row 17))))
   (and (equal (mv-nth 0 r) :started)
        (fn-hrcur-tree-domainp row)
        (< (len (fn-scc-encode row)) 18446744073709551616)
        (fn-hpe-invariantp (fn-hrcur-field 5 (mv-nth 1 r)))
        (equal (fn-hpe-total (fn-hrcur-field 5 (mv-nth 1 r))) (len (fn-scc-encode row)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-hpcx-begin fn-hpcx-offer fn-hpe-invariantp fn-hpe-total fn-hrcur-tree-domainp))))

; Distinct actual descriptor and five-buffer dispatcher APIs coexist.
(assert-event
 (and (fn-hpc-cursorp (fn-hpc-begin nil nil 0 '(3 0)))
      (fn-hpcx-shapep (fn-hpcx-begin 0 0 '(0 (3 0) 0 0) 'capture 'resource))
      (equal (car (fn-hpcx-begin 0 0 '(0 (3 0) 0 0) 'capture 'resource)) :prepared)
      (mv-let (verdict descriptor next)
        (fn-hpc-tick (fn-hpc-begin nil nil 0 '(3 0)))
        (declare (ignore descriptor next))
        (eq verdict :yield))))
