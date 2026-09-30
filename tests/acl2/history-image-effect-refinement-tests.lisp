; Constructed supported page-effect phase witnesses, not whole image/native.
(in-package "ACL2")
(include-book "../../books/history-image-effect-refinement")

(local (defun hpib-test-fill (n word fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil :measure (nfix n)
                 :hints (("Goal" :in-theory (disable fn-hpb-put)))))
 (if (zp n) fn-hpb
  (mv-let (v fn-hpb) (fn-hpb-put word fn-hpb)
   (declare (ignore v)) (hpib-test-fill (1- n) word fn-hpb)))))

(local (defun hpib-test-one-byte (c effect stage ledger i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (let* ((context (fn-hpib-page-byte-contextp c effect stage ledger i
                   fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (expected (nth i (pgs-words-le-octets
                    (fn-hpib-selected-prefix (fn-omk-at 5 (fn-hie-plan c effect stage ledger))
                      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))
  (mv-let (status octet) (fn-hie-page-byte c effect stage ledger i
                          fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
   (and context (equal (list status octet) (list :octet expected)))))))

(local (defun hpib-test-page (selector mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) maintenance
                   (fn-omk-at 1 maintenance) 10000000 "node" 17 "trail")))
   (mv-let (funded ignored c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (fn-hpi-tick initial nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (declare (ignore ignored))
    (let* ((fn-hpq0 (hpib-test-fill 2048 #x0102030405060708 fn-hpq0))
           (fn-hpq1 (hpib-test-fill 2048 #x1112131415161718 fn-hpq1))
           (fn-hpq2 (hpib-test-fill 2048 #x8182838485868788 fn-hpq2))
           (fn-hpq3 (hpib-test-fill 2048 #xf1f2f3f4f5f6f7f8 fn-hpq3))
           (fn-hpb (hpib-test-fill 2048 #xffffffffffffffff fn-hpb)))
     (mv-let (issued effect c) (fn-hpi-await-page selector 0 0 selector :metadata c)
      (let* ((stage (fn-omk-at 3 c))
             (original-plan (fn-hie-plan c effect stage ledger))
             (positive
              (and (eq admitted :admitted) (eq funded :funded) (eq issued :write)
                   (fn-hpi-grant-matchesp c ledger)
                   (equal original-plan (list :io :write :target 16384 16384 selector nil))
                   (hpib-test-one-byte c effect stage ledger 0 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                   (hpib-test-one-byte c effect stage ledger 1 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                   (hpib-test-one-byte c effect stage ledger 7 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                   (hpib-test-one-byte c effect stage ledger 8 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                   (hpib-test-one-byte c effect stage ledger 8191 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                   (hpib-test-one-byte c effect stage ledger 16383 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
             (expected (nth 16383 (pgs-words-le-octets
                          (fn-hpib-selected-prefix selector fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))
       (if (eq mode :positive)
        (mv (and positive (unsigned-byte-p 8 expected)) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (let* ((ledger (if (eq mode :revoked) nil ledger))
               (c (if (eq mode :selector) (fn-hpi-set 17 '(5 :metadata) c) c))
               (fn-hpq0 (if (and (eq mode :short) (equal selector 0)) (update-fn-hpb-used 2047 fn-hpq0) fn-hpq0))
               (fn-hpq1 (if (and (eq mode :short) (equal selector 1)) (update-fn-hpb-used 2047 fn-hpq1) fn-hpq1))
               (fn-hpq2 (if (and (eq mode :short) (equal selector 2)) (update-fn-hpb-used 2047 fn-hpq2) fn-hpq2))
               (fn-hpq3 (if (and (eq mode :short) (equal selector 3)) (update-fn-hpb-used 2047 fn-hpq3) fn-hpq3))
               (fn-hpb (if (and (eq mode :short) (equal selector 4)) (update-fn-hpb-used 2047 fn-hpb) fn-hpb))
               (plan (fn-hie-plan c effect stage ledger))
               (mutated-expected (nth 16383 (pgs-words-le-octets
                  (fn-hpib-selected-prefix (fn-omk-at 5 plan) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))
         (mv-let (status octet) (fn-hie-page-byte c effect stage ledger 16383
                                  fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
          (mv (and positive
                   (not (fn-hpib-page-byte-contextp c effect stage ledger 16383
                           fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
                   (equal (fn-omk-at 5 c) effect) (equal (fn-omk-at 3 c) stage)
                   (natp 16383) (< 16383 16384)
                   (not (equal (list status octet) (list :octet mutated-expected)))
                   (case mode
                    (:short (and (equal plan original-plan) (fn-hpi-grant-matchesp c ledger)
                                 (equal (fn-hpi-region-used selector fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) 2047)
                                 (equal (list status octet) '(:unwritten 0))))
                    (:revoked (and (not (fn-hpi-grant-matchesp c ledger))
                                   (equal (fn-omk-at 0 (fn-omk-at 17 c)) selector)
                                   (equal (fn-hpi-region-used selector fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) 2048)
                                   (equal (list status octet) '(:refused 0))))
                    (:selector (and (fn-hpi-grant-matchesp c ledger)
                                    (equal (fn-omk-at 0 (fn-omk-at 17 c)) 5)
                                    (equal (fn-hpi-region-used selector fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) 2048)
                                    (equal (list status octet) '(:refused 0))))
                    (otherwise nil)))
              fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))))))))

(local (defun hpib-test-local (selector mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpib-test-page selector mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result))))
; Full antecedent and complete output, selected buffer 0.
(assert-event (hpib-test-local 0 :positive))
; Full antecedent and complete output, selected buffer 1.
(assert-event (hpib-test-local 1 :positive))
; Full antecedent and complete output, selected buffer 2.
(assert-event (hpib-test-local 2 :positive))
; Full antecedent and complete output, selected buffer 3.
(assert-event (hpib-test-local 3 :positive))
; Full antecedent and complete output, selected buffer 4.
(assert-event (hpib-test-local 4 :positive))
; Explicit short mutation: complete context fails and full conclusion fails.
(assert-event (hpib-test-local 4 :short))
; Explicit revoked mutation: complete context fails and full conclusion fails.
(assert-event (hpib-test-local 4 :revoked))
; Explicit selector mutation: complete context fails and full conclusion fails.
(assert-event (hpib-test-local 4 :selector))
