; One pool codec tick or one scalar-column write per scheduling step.
(in-package "ACL2")
(include-book "history-pool-emitter")
(include-book "history-page-buffers")
(include-book "history-image-columns")
(include-book "snapshot-source-token")

; phase,count,ordinal,offset,pool-limit,child,token,key,encoded,column,capture,lease.
(defun fn-hpcx-shapep (c)
  (declare (xargs :guard t))
  (and (fn-hrcur-widthp c 12)
       (member-eq (fn-hrcur-field 0 c) '(:need-row :pool :columns :prepared :refused))
       (unsigned-byte-p 61 (fn-hrcur-field 1 c))
       (natp (fn-hrcur-field 2 c)) (<= (fn-hrcur-field 2 c) (fn-hrcur-field 1 c))
       (unsigned-byte-p 64 (fn-hrcur-field 3 c))
       (unsigned-byte-p 64 (fn-hrcur-field 4 c))
       (<= (fn-hrcur-field 3 c) (fn-hrcur-field 4 c))
       (fn-omk-tokenp (fn-hrcur-field 6 c))
       (equal (fn-omk-at 1 (fn-omk-at 1 (fn-hrcur-field 6 c))) (fn-hrcur-field 1 c))
       (implies (member-eq (fn-hrcur-field 0 c) '(:pool :columns))
                (equal (fn-omk-at 3 (fn-hrcur-field 6 c)) (fn-hrcur-field 2 c)))
       (unsigned-byte-p 64 (fn-hrcur-field 7 c))
       (unsigned-byte-p 64 (fn-hrcur-field 8 c))
       (natp (fn-hrcur-field 9 c)) (< (fn-hrcur-field 9 c) 4)
       (implies (member-eq (fn-hrcur-field 0 c) '(:need-row :pool :columns))
                (< (fn-hrcur-field 2 c) (fn-hrcur-field 1 c)))
       (implies (eq (fn-hrcur-field 0 c) :pool)
                (fn-hpe-shapep (fn-hrcur-field 5 c)))))

(defun fn-hpcx-with (phase ordinal offset child token key encoded column c)
  (declare (xargs :guard t))
  (list phase (fn-hrcur-field 1 c) ordinal offset (fn-hrcur-field 4 c)
        child token key encoded column (fn-hrcur-field 10 c) (fn-hrcur-field 11 c)))

(defun fn-hpcx-begin (count pool token capture lease)
  (declare (xargs :guard t))
  (if (and (unsigned-byte-p 61 count) (unsigned-byte-p 64 pool)
           (fn-omk-tokenp token) (equal (fn-omk-at 3 token) 0)
           (equal (fn-omk-at 1 (fn-omk-at 1 token)) count)
           (or (< 0 count) (equal pool 0)))
      (list (if (zp count) :prepared :need-row) count 0 0 pool nil token 0 0 0 capture lease)
    (list :refused 0 0 0 0 nil '(0 (0 0) 0 0) 0 0 0 capture lease)))

(defun fn-hpcx-offer (c ordinal source token key)
  (declare (xargs :guard t))
  (let* ((oldtoken (fn-hrcur-field 6 c))
         (expected (list (fn-omk-at 0 oldtoken) (fn-omk-at 1 oldtoken)
                         (fn-omk-at 2 oldtoken) (fn-hrcur-field 2 c))))
    (if (not (and (fn-hpcx-shapep c) (eq (fn-hrcur-field 0 c) :need-row)
                  (equal ordinal (fn-hrcur-field 2 c))
                  (fn-omk-token-matchp token expected) (unsigned-byte-p 64 key)))
        (mv :stale c)
      (mv :started
          (fn-hpcx-with :pool ordinal (fn-hrcur-field 3 c)
                       (fn-hpe-begin source token (fn-hrcur-field 11 c))
                       token key 0 0 c)))))

(defun fn-hpcx-tick (c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                  :guard-hints (("Goal" :use
                      ((:instance fn-hcl-cell-is-u64
                          (column (fn-hrcur-field 9 c)) (key (fn-hrcur-field 7 c))
                          (encoded (fn-hrcur-field 8 c)) (offset (fn-hrcur-field 3 c))))
                     :in-theory (e/d (fn-hcc-row) (fn-hcl-cell fn-hcl-cell-is-u64 fn-hpe-tick fn-hpq-put fn-hpe-shapep fn-omk-tokenp fn-hp-pad8-count))))))
  (let ((phase (fn-hrcur-field 0 c)) (ordinal (fn-hrcur-field 2 c))
        (offset (fn-hrcur-field 3 c)) (child (fn-hrcur-field 5 c))
        (token (fn-hrcur-field 6 c)) (key (fn-hrcur-field 7 c))
        (encoded (fn-hrcur-field 8 c)) (column (fn-hrcur-field 9 c)))
    (cond
     ((not (fn-hpcx-shapep c))
      (mv '(:refused :cursor) nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
     ((eq phase :need-row) (mv :need-row ordinal c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
     ((eq phase :prepared) (mv :prepared (list ordinal offset) c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
     ((eq phase :refused) (mv '(:refused :row) nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
     ((eq phase :pool)
      (mv-let (v n next fn-hpb) (fn-hpe-tick child fn-hpb)
        (cond
         ((fn-hsrcb-demandp v)
          (mv v nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
         ((and (eq v :prepared) (unsigned-byte-p 64 n))
          (mv-let (bounds count2 pool2) (fn-hcc-row ordinal offset ordinal n)
            (if (and (eq bounds :counted) (<= count2 (fn-hrcur-field 1 c))
                     (<= pool2 (fn-hrcur-field 4 c))
                     (or (< count2 (fn-hrcur-field 1 c)) (equal pool2 (fn-hrcur-field 4 c))))
                (mv :columns n (fn-hpcx-with :columns ordinal offset next token key n 0 c)
                    fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
              (mv '(:refused :census) nil (fn-hpcx-with :refused ordinal offset next token key 0 0 c)
                  fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))
         ((eq v :page-full)
          (mv :page-full nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
         ((eq v :continue)
          (mv v nil (fn-hpcx-with :pool ordinal offset next token key 0 0 c)
              fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
         (t (mv '(:refused :codec) nil (fn-hpcx-with :refused ordinal offset next token key 0 0 c)
                fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))
     (t
      (mv-let (bounds count2 pool2) (fn-hcc-row ordinal offset ordinal encoded)
        ; Corrupted scalar state is refused before any column effect.
        (if (not (and (eq bounds :counted) (<= count2 (fn-hrcur-field 1 c))
                      (<= pool2 (fn-hrcur-field 4 c))
                      (or (< count2 (fn-hrcur-field 1 c)) (equal pool2 (fn-hrcur-field 4 c)))))
            (mv '(:refused :census) nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
          (mv-let (v word) (fn-hcl-cell column key encoded offset)
            (if (not (eq v :word))
                (mv '(:refused :cell) nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
              (mv-let (stored fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (fn-hpq-put column word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (if (not (eq stored :stored))
                    (mv :page-full column c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                  (if (< column 3)
                      (mv :column-stored column (fn-hpcx-with :columns ordinal offset child token key encoded (+ 1 column) c)
                          fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                    (mv :row-done encoded
                        (fn-hpcx-with (if (equal count2 (fn-hrcur-field 1 c)) :prepared :need-row)
                                     count2 pool2 nil token 0 0 0 c)
                        fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))))))))

(defun fn-hpcx-supply (c position byte fn-hpb)
  (declare (xargs :stobjs fn-hpb))
  (if (not (and (fn-hpcx-shapep c) (eq (fn-hrcur-field 0 c) :pool)))
      (mv '(:refused :no-pool-byte-demand) c fn-hpb)
    (mv-let (v child fn-hpb) (fn-hpe-supply (fn-hrcur-field 5 c) position byte fn-hpb)
      (if (eq v :continue)
          (mv v (fn-hpcx-with :pool (fn-hrcur-field 2 c) (fn-hrcur-field 3 c)
                              child (fn-hrcur-field 6 c) (fn-hrcur-field 7 c) 0 0 c) fn-hpb)
        (mv v c fn-hpb)))))

(defthm fn-hpcx-supply-keeps-shape
  (implies (fn-hpcx-shapep c)
           (fn-hpcx-shapep (mv-nth 1 (fn-hpcx-supply c position byte fn-hpb))))
  :hints (("Goal" :in-theory (e/d (fn-hpcx-shapep fn-hpcx-supply fn-hpcx-with)
                               (fn-hpe-supply fn-hpe-shapep fn-omk-tokenp)))))

(defthm fn-hpcx-begin-keeps-shape
  (fn-hpcx-shapep (fn-hpcx-begin count pool token capture lease))
  :hints (("Goal" :in-theory (enable fn-omk-tokenp fn-omk-widthp fn-omk-at))))

(defthm fn-hpcx-offer-keeps-shape
  (implies (fn-hpcx-shapep c)
           (fn-hpcx-shapep (mv-nth 1 (fn-hpcx-offer c ordinal source token key))))
  :hints (("Goal" :in-theory (e/d (fn-omk-token-matchp fn-omk-at) (fn-hpe-begin fn-omk-tokenp)))))

(defthm fn-hpcx-offer-while-pending-is-stale
  (implies (member-eq (fn-hrcur-field 0 c) '(:pool :columns :prepared :refused))
           (and (equal (mv-nth 0 (fn-hpcx-offer c ordinal source token key)) :stale)
                (equal (mv-nth 1 (fn-hpcx-offer c ordinal source token key)) c)))
  :hints (("Goal" :in-theory (disable fn-hpe-begin fn-omk-token-matchp fn-hpcx-shapep))))

(defthm fn-hpcx-tick-keeps-shape
  (implies (fn-hpcx-shapep c)
           (fn-hpcx-shapep (mv-nth 2 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))
  :hints (("Goal" :in-theory (e/d (fn-hcc-row)
                      (fn-hpe-tick fn-hcl-cell fn-hpq-put fn-hpe-shapep fn-omk-tokenp fn-hp-pad8-count)))))

(defthm fn-hpcx-tick-keeps-capture-and-lease
  (and (equal (fn-hrcur-field 10 (mv-nth 2 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
              (fn-hrcur-field 10 c))
       (equal (fn-hrcur-field 11 (mv-nth 2 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
              (fn-hrcur-field 11 c)))
  :hints (("Goal" :in-theory (disable fn-hpe-tick fn-hcl-cell fn-hpq-put fn-hcc-row fn-hpcx-shapep))))

(defthm fn-hpcx-continuation-keeps-census
  (implies (not (equal (mv-nth 0 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :row-done))
           (and (equal (fn-hrcur-field 2 (mv-nth 2 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                       (fn-hrcur-field 2 c))
                (equal (fn-hrcur-field 3 (mv-nth 2 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                       (fn-hrcur-field 3 c))))
  :hints (("Goal" :in-theory (disable fn-hpe-tick fn-hcl-cell fn-hpq-put fn-hcc-row fn-hpcx-shapep))))



(defthm fn-hpcx-pool-prepared-attribution
  (implies (and (fn-hpe-invariantp (fn-hrcur-field 5 c))
                (equal (fn-hpe-total (fn-hrcur-field 5 c)) (len (fn-scc-encode row)))
                (equal (mv-nth 0 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :columns))
           (equal (fn-hrcur-field 8 (mv-nth 2 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                  (len (fn-scc-encode row))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hpe-tick-preserves-byte-total (c (fn-hrcur-field 5 c))))
           :in-theory (e/d (fn-hpcx-tick fn-hpcx-with) (fn-hpe-tick fn-hpe-invariantp fn-hpe-total fn-hcc-row
                               fn-hcl-cell fn-hpq-put fn-hpcx-shapep fn-scc-encode fn-scc-encode-is-program
                               fn-hpe-tick-preserves-byte-total)))))

(defthm fn-hpcx-row-done-advances-once
  (implies (equal (mv-nth 0 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :row-done)
           (and (equal (fn-hrcur-field 0 c) :columns)
                (equal (fn-hrcur-field 9 c) 3)
                (equal (fn-hrcur-field 2 (mv-nth 2 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                       (+ 1 (fn-hrcur-field 2 c)))
                (equal (fn-hrcur-field 3 (mv-nth 2 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                       (+ (fn-hrcur-field 3 c) (fn-hrcur-field 8 c)
                          (fn-hp-pad8-count (fn-hrcur-field 8 c))))))
  :hints (("Goal" :in-theory (e/d (fn-hpcx-tick fn-hpcx-with fn-hpcx-shapep fn-hcc-row)
                    (fn-hpe-tick fn-hpe-shapep fn-hcl-cell fn-hpq-put fn-hp-pad8-count fn-omk-tokenp)))))

(local
 (defthm fn-hpcx-stored-column-prefix
   (implies (and (natp region) (< region 4)
                 (natp (fn-hpb-used (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                 (equal (mv-nth 0 (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :stored))
            (equal (fn-hpb-prefix (mv-nth (+ 1 region) (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                   (append (fn-hpb-prefix (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) (list word))))
   :hints (("Goal" :use fn-hpq-put-selected-refines-prefix
            :in-theory (e/d (fn-hpq-put fn-hpq-model-select fn-hpb-put)
                             (fn-hpb-prefix fn-hpb-used update-fn-hpb-used update-fn-hpb-wi
                              fn-hpq-put-selected-refines-prefix))))))

(defthm fn-hpcx-column-selected-prefix
  (let ((column (fn-hrcur-field 9 c)))
    (implies (and (natp (fn-hpb-used (fn-hpq-model-select column fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                  (equal (fn-hrcur-field 7 c) (fn-hp-mkey row salt))
                  (equal (fn-hrcur-field 8 c) (len (fn-scc-encode row)))
                  (member-eq (mv-nth 0 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
                             '(:column-stored :row-done)))
             (equal (fn-hpb-prefix (mv-nth (+ 3 column)
                                           (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                    (append (fn-hpb-prefix (fn-hpq-model-select column fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
                            (list (nth column (fn-hp-cells-of row salt (fn-hrcur-field 3 c))))))))
  :rule-classes nil
  :hints (("Goal" :cases ((equal (fn-hrcur-field 9 c) 0) (equal (fn-hrcur-field 9 c) 1)
                                  (equal (fn-hrcur-field 9 c) 2) (equal (fn-hrcur-field 9 c) 3))
           :use ((:instance fn-hcl-cell-refines-current-row
                           (column (fn-hrcur-field 9 c)) (key (fn-hrcur-field 7 c))
                           (encoded (fn-hrcur-field 8 c)) (offset (fn-hrcur-field 3 c)) (ev row))
                       (:instance fn-hpcx-stored-column-prefix
                           (region (fn-hrcur-field 9 c))
                           (word (mv-nth 1 (fn-hcl-cell (fn-hrcur-field 9 c) (fn-hrcur-field 7 c)
                                                      (fn-hrcur-field 8 c) (fn-hrcur-field 3 c))))))
           :in-theory (e/d (fn-hpcx-tick fn-hpcx-with fn-hpcx-shapep)
                      (fn-hpe-tick fn-hcl-cell fn-hcc-row fn-hpq-model-select
                       fn-hpb-prefix fn-hpb-used fn-hpbp fn-hp-mkey fn-scc-encode fn-hp-cells-of
                       fn-hpe-shapep fn-omk-tokenp fn-hcl-cell-refines-current-row
                       fn-hpq-put-selected-refines-prefix fn-hpcx-stored-column-prefix fn-hpq-put fn-hpb-put
                       fn-hrcur-field fn-scc-encode-is-program fn-hpq-put-frames-other-regions)))))



(local
 (defthm fn-hpcx-emitter-page-full-frame
   (implies (equal (mv-nth 0 (fn-hpe-tick child fn-hpb)) :page-full)
            (equal (mv-nth 3 (fn-hpe-tick child fn-hpb)) fn-hpb))
   :hints (("Goal" :in-theory (e/d (fn-hpe-tick)
                (fn-hpe-shapep fn-hrcur-byte-tick fn-hrcur-word-push fn-hrcur-word-finish fn-hpb-put))))))

(defthm fn-hpcx-page-full-is-unchanged
  (implies (equal (mv-nth 0 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) :page-full)
           (and (equal (mv-nth 2 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) c)
                (equal (mv-nth 3 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) fn-hpq0)
                (equal (mv-nth 4 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) fn-hpq1)
                (equal (mv-nth 5 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) fn-hpq2)
                (equal (mv-nth 6 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) fn-hpq3)
                (equal (mv-nth 7 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)) fn-hpb)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hpcx-tick fn-hpq-put fn-hpb-put)
                      (fn-hpcx-shapep fn-hpe-tick fn-hpe-shapep fn-hcl-cell fn-hcc-row fn-hpb-used
                       fn-hrcur-byte-tick fn-hrcur-word-push fn-hrcur-word-finish
                       update-fn-hpb-wi update-fn-hpb-used)))))

(defthm fn-hpcx-tick-keeps-concrete
  (implies (and (fn-hpbp fn-hpq0) (fn-hpbp fn-hpq1) (fn-hpbp fn-hpq2)
                (fn-hpbp fn-hpq3) (fn-hpbp fn-hpb))
           (and (fn-hpbp (mv-nth 3 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                (fn-hpbp (mv-nth 4 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                (fn-hpbp (mv-nth 5 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                (fn-hpbp (mv-nth 6 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
                (fn-hpbp (mv-nth 7 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))
  :hints (("Goal" :use ((:instance fn-hcl-cell-is-u64
                              (column (fn-hrcur-field 9 c)) (key (fn-hrcur-field 7 c))
                              (encoded (fn-hrcur-field 8 c)) (offset (fn-hrcur-field 3 c))))
           :in-theory (e/d (fn-hpcx-tick fn-hpcx-shapep)
                   (fn-hpe-tick fn-hpe-shapep fn-hcl-cell fn-hcl-cell-is-u64 fn-hpq-put
                    fn-hcc-row fn-hpbp fn-omk-tokenp)))))



(defthm fn-hpcx-tick-keeps-region-identities
 (and (equal (fn-hpb-epoch (mv-nth 3 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpb-epoch fn-hpq0))
      (equal (fn-hpb-lease (mv-nth 3 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpb-lease fn-hpq0))
      (equal (fn-hpb-epoch (mv-nth 4 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpb-epoch fn-hpq1))
      (equal (fn-hpb-lease (mv-nth 4 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpb-lease fn-hpq1))
      (equal (fn-hpb-epoch (mv-nth 5 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpb-epoch fn-hpq2))
      (equal (fn-hpb-lease (mv-nth 5 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpb-lease fn-hpq2))
      (equal (fn-hpb-epoch (mv-nth 6 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpb-epoch fn-hpq3))
      (equal (fn-hpb-lease (mv-nth 6 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpb-lease fn-hpq3))
      (equal (fn-hpb-epoch (mv-nth 7 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpb-epoch fn-hpb))
      (equal (fn-hpb-lease (mv-nth 7 (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (fn-hpb-lease fn-hpb)))
 :hints (("Goal" :in-theory (e/d (fn-hpcx-tick fn-hpq-put)
    (fn-hpe-tick fn-hpcx-shapep fn-hcl-cell fn-hcc-row fn-hpb-put fn-hpb-epoch fn-hpb-lease)))))


(defthm fn-hpcx-columns-frame-other-regions
 (implies (and (equal (fn-hrcur-field 0 c) :columns)
               (natp other) (< other 5) (not (equal other (fn-hrcur-field 9 c))))
          (equal (mv-nth (+ 3 other) (fn-hpcx-tick c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
                 (fn-hpq-model-select other fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
 :hints (("Goal" :cases ((equal other 0) (equal other 1) (equal other 2) (equal other 3) (equal other 4))
          :use ((:instance fn-hpq-put-frames-other-regions (region (fn-hrcur-field 9 c))
                   (word (mv-nth 1 (fn-hcl-cell (fn-hrcur-field 9 c) (fn-hrcur-field 7 c)
                                              (fn-hrcur-field 8 c) (fn-hrcur-field 3 c))))))
          :in-theory (e/d (fn-hpcx-tick fn-hpcx-shapep fn-hpq-model-select)
               (fn-hpe-tick fn-hpe-shapep fn-hcc-row fn-hcl-cell fn-hpq-put fn-omk-tokenp
                fn-hpq-put-frames-other-regions fn-hrcur-field fn-omk-at)))))


(defthm fn-hpcx-offered-resident-establishes-total
 (implies (and (equal (mv-nth 0 (fn-hpcx-offer c ordinal (list :resident row) token key)) :started)
               (fn-hrcur-tree-domainp row)
               (< (len (fn-scc-encode row)) 18446744073709551616))
          (let ((next (mv-nth 1 (fn-hpcx-offer c ordinal (list :resident row) token key))))
            (and (fn-hpe-invariantp (fn-hrcur-field 5 next))
                 (equal (fn-hpe-total (fn-hrcur-field 5 next)) (len (fn-scc-encode row))))))
 :hints (("Goal" :use ((:instance fn-hpe-begin-refines-byte-total (capture token) (lease (fn-hrcur-field 11 c))))
          :in-theory (e/d (fn-hpcx-offer fn-hpcx-with)
                (fn-hpe-begin fn-hpe-invariantp fn-hpe-total fn-hpcx-shapep fn-omk-token-matchp
                 fn-omk-at fn-hrcur-tree-domainp fn-scc-encode fn-scc-encode-is-program
                 fn-hpe-begin-refines-byte-total)))))
(in-theory (disable fn-hpcx-shapep fn-hpcx-with fn-hpcx-begin fn-hpcx-offer fn-hpcx-tick))
