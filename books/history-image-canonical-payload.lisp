; Actual executor octets from actual original canonical padded page issuance.
; Visible-byte composition only; private FD/INITIAL/runtime remain separate.
(in-package "ACL2")
(include-book "history-image-padding-phase")
(include-book "history-image-effect-refinement")
(local
 (defun fn-hpicb-field-ind (j k c)
  (if (or (zp j) (zp k)) (list j k c)
    (fn-hpicb-field-ind (1- j) (1- k) (if (consp c) (cdr c) nil)))))

(local
 (defthm fn-hpicb-set-field
  (implies (and (natp k) (< k 25) (natp j) (< j 25))
   (equal (fn-omk-at j (fn-hpi-set k value c))
          (if (equal j k) value (fn-omk-at j c))))
  :hints (("Goal" :induct (fn-hpicb-field-ind j k c)
           :expand ((fn-hpi-set k value c)
                    (fn-omk-at j c)
                    (fn-omk-at j (fn-hpi-set k value c))
                    (:free (a d) (fn-omk-at j (cons a d))))
           :in-theory (e/d (fn-omk-at fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))


(local (defthm fn-hpicb-mv-zero (equal (mv-nth 0 x) (car x))
 :hints (("Goal" :in-theory (enable mv-nth)))))



(local (defthm fn-hpicb-at-cons-by-definition
 (equal (fn-omk-at j (cons a b)) (if (zp j) a (fn-omk-at (1- j) b)))
 :hints (("Goal" :in-theory (enable fn-omk-at)))))

(local (defthm fn-hpicb-issued-padding-selects-original-region
 (let ((a (fn-hpi-await-region region :pad c)))
  (implies (and (natp region) (< region 5) (equal (car a) :write))
   (and (equal (fn-omk-at 0 (mv-nth 1 a)) :write-page)
        (equal (fn-omk-at 0 (fn-omk-at 17 (mv-nth 2 a))) region))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-await-region fn-hpi-await-page fn-hpi-write-effect mv-nth)
   (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-hpi-region-cap fn-hpi-region-start))))))
(local (defthm fn-hpicb-page-plan-selects-retained-buffer
 (implies (and (equal (fn-omk-at 0 effect) :write-page)
               (equal (fn-omk-at 0 (fn-hie-plan c effect stage ledger)) :io))
  (equal (fn-omk-at 5 (fn-hie-plan c effect stage ledger)) (fn-omk-at 0 (fn-omk-at 17 c))))
 :hints (("Goal" :in-theory (e/d (fn-hie-plan) (fn-hie-currentp fn-omk-at fn-osj-native-slicep))))))

(local (defthm fn-hpicb-ready-region-issuer-is-write
 (implies (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (equal (car (fn-hpi-await-region (fn-omk-at 18 c) :pad c)) :write))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-hpiz-writer-ready-p fn-hpi-await-region fn-hpi-await-page)
   (nfix fn-hp-regs fn-omk-at fn-hpi-region-cap fn-hpiz-region-invariantp fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-write-effect fn-hpi-region-start))))))
(local (defthm fn-hpicb-actual-padding-issued-region
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (equal (car r) :write))
   (and (equal (fn-omk-at 0 (mv-nth 1 r)) :write-page)
        (equal (fn-omk-at 0 (fn-omk-at 17 (mv-nth 2 r))) (fn-omk-at 18 c))
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3) (equal (mv-nth 8 r) fn-hpb))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpi-padding-page-handoff-is-original-canonical-page fn-hpicb-ready-region-issuer-is-write
        (:instance fn-hpicb-issued-padding-selects-original-region (region (fn-omk-at 18 c))))
  :in-theory (e/d (fn-hpiz-writer-ready-p)
   (nfix fn-hp-regs fn-hpi-tick fn-hpi-await-region fn-hpiz-region-invariantp fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition mv-nth))))))

(local (defthm fn-hpicb-issued-page-byte-is-original-canonical-octet
 (let* ((region (fn-omk-at 18 c))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
        (effect (mv-nth 1 r)) (next (mv-nth 2 r)) (next-ledger (mv-nth 3 r)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (equal (car r) :write)
                (fn-hpib-page-byte-contextp next effect stage next-ledger i
                  (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)))
   (equal (fn-hie-page-byte next effect stage next-ledger i
            (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))
          (mv :octet (nth i (pgs-words-le-octets
           (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at region (fn-omk-at 15 c))))
             (fn-hp-wpad (nth region (fn-hp-regs h (fn-omk-at 12 c))))))))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpi-padding-page-handoff-is-original-canonical-page fn-hpicb-actual-padding-issued-region
        (:instance fn-hpicb-issued-padding-selects-original-region (region (fn-omk-at 18 c)))
        (:instance fn-hie-page-byte-refines-retained-page-serialization
          (c (mv-nth 2 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (effect (mv-nth 1 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (ledger (mv-nth 3 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (fn-hpq0 (mv-nth 4 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (fn-hpq1 (mv-nth 5 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (fn-hpq2 (mv-nth 6 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (fn-hpq3 (mv-nth 7 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (fn-hpb (mv-nth 8 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))
  :cases ((equal (fn-omk-at 18 c) 0) (equal (fn-omk-at 18 c) 1) (equal (fn-omk-at 18 c) 2)
          (equal (fn-omk-at 18 c) 3) (equal (fn-omk-at 18 c) 4))
  :in-theory (e/d (fn-hpib-selected-prefix fn-hpq-model-select fn-hpib-page-byte-contextp fn-hpiz-writer-ready-p)
   (fn-hpi-tick fn-hie-page-byte fn-hie-plan fn-hpi-await-region fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpiz-region-invariantp fn-hpb-prefix fn-hpb-used fn-hp-regs fn-hp-wpad pgs-words-le-octets take nth nthcdr mv-nth)))))
)

(local (defthm fn-hpicb-page-byte-context-is-wait-write
 (implies (fn-hpib-page-byte-contextp c effect stage ledger i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (equal (fn-omk-at 0 c) :wait-write))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-hpib-page-byte-contextp fn-hie-plan)
   (fn-hie-currentp fn-omk-at fn-hpi-region-used fn-osj-native-slicep fn-hpi-octets-p))))))
(local (defthm fn-hpicb-region-wait-write-implies-issued-write
 (let ((a (fn-hpi-await-region region :pad c)))
  (implies (and (natp region) (< region 5)
                (equal (fn-omk-at 0 (mv-nth 2 a)) :wait-write))
   (equal (car a) :write)))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-region fn-hpi-await-page mv-nth)
   (nfix fn-omk-at fn-hpi-region-cap fn-hpi-region-start fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-write-effect))))))
(local (defthm fn-hpicb-padding-next-wait-write-implies-issued-write
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (equal (fn-omk-at 0 (mv-nth 2 r)) :wait-write))
   (equal (car r) :write)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpiz-writer-ready-p fn-hpi-tick fn-hpi-buffer-step fn-hpi-supply)
   (nfix fn-hp-regs fn-hpiz-region-invariantp fn-hpi-grant-matchesp fn-omk-at fn-hpi-region-cap fn-hpi-region-used
    fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-await-region fn-hpi-written fn-hpcx-supply fn-hpcx-tick
    fn-hpi-stream-step fn-hpq-put fn-hpb-put fn-osj-native-grow mv-nth))))))

(defthm fn-hie-padding-page-byte-is-original-canonical-octet
 (let* ((region (fn-omk-at 18 c))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
        (effect (mv-nth 1 r)) (next (mv-nth 2 r)) (next-ledger (mv-nth 3 r)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (fn-hpib-page-byte-contextp next effect stage next-ledger i
                  (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)))
   (equal (fn-hie-page-byte next effect stage next-ledger i
            (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))
          (mv :octet (nth i (pgs-words-le-octets
           (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at region (fn-omk-at 15 c))))
             (fn-hp-wpad (nth region (fn-hp-regs h (fn-omk-at 12 c))))))))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpicb-issued-page-byte-is-original-canonical-octet fn-hpicb-padding-next-wait-write-implies-issued-write
        (:instance fn-hpicb-page-byte-context-is-wait-write
          (c (mv-nth 2 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (effect (mv-nth 1 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (ledger (mv-nth 3 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (fn-hpq0 (mv-nth 4 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (fn-hpq1 (mv-nth 5 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (fn-hpq2 (mv-nth 6 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (fn-hpq3 (mv-nth 7 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
          (fn-hpb (mv-nth 8 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))
  :in-theory (disable fn-hpi-tick fn-hie-page-byte fn-hpib-page-byte-contextp fn-hpiz-writer-ready-p
    fn-hp-regs fn-hp-wpad fn-hpi-set fn-omk-at pgs-words-le-octets take nth nthcdr mv-nth))))
