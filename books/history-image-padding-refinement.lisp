; Actual zero padding over the original FNADTSN2 padded region words.
; Proof-only carry; source/pool/physical/whole-image joins remain separate.
(in-package "ACL2")
(include-book "history-image-column-handoff")
(include-book "history-pages-write")

(local (defun fn-hpiz-unle-ind (w n)
 (if (zp w) (list w n) (fn-hpiz-unle-ind (1- w) (1- n)))))
(local (defthm fn-hpiz-unle-zeroes
 (equal (adt-unle w (adt-zeros n)) 0)
 :hints (("Goal" :induct (fn-hpiz-unle-ind w n) :in-theory (enable adt-unle adt-zeros)))))

(defthm fn-hpiz-original-padded-region-past-used-is-zero
 (implies (and (natp index) (< index (* 2048 (adt-cap (len raw))))
               (<= (len raw) (* 8 index)))
  (equal (nth index (fn-hp-wpad raw)) 0))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hp-nth-pack8 (j index) (n (* 2048 (adt-cap (len raw)))) (b (adt-pad raw))))
  :in-theory (e/d (fn-hp-wpad adt-pad)
   (adt-cap fn-hp-pack8 adt-unle adt-zeros nth nthcdr fn-hp-nth-pack8)))))

(defun fn-hpiz-region-invariantp (raw page cap fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (let ((position (+ (* 2048 page) (fn-hpb-used fn-hpb))))
  (and (natp page) (natp cap) (equal cap (adt-cap (len raw)))
       (natp (fn-hpb-used fn-hpb)) (<= (fn-hpb-used fn-hpb) 2048)
       (<= position (* 2048 cap)) (<= (len raw) (* 8 position))
       (equal (fn-hpb-prefix fn-hpb)
              (take (fn-hpb-used fn-hpb) (nthcdr (* 2048 page) (fn-hp-wpad raw)))))))

(local (defthm fn-hpiz-take-next
 (implies (natp n)
  (equal (append (take n xs) (list (nth n xs))) (take (+ 1 n) xs)))
 :hints (("Goal" :induct (take n xs) :in-theory (enable take nth)))))
(local (defthm fn-hpiz-nth-nthcdr
 (implies (and (natp n) (natp j))
  (equal (nth j (nthcdr n xs)) (nth (+ n j) xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr nth)))))
(local (defthm fn-hpiz-put-used-increments
 (implies (< (fn-hpb-used fn-hpb) 2048)
  (equal (fn-hpb-used (mv-nth 1 (fn-hpb-put w fn-hpb))) (+ 1 (fn-hpb-used fn-hpb))))
 :hints (("Goal" :in-theory (enable fn-hpb-put fn-hpb-used)))))

(local (defthm fn-hpiz-put-status
 (equal (car (fn-hpb-put w fn-hpb)) (if (< (fn-hpb-used fn-hpb) 2048) :stored :full))
 :hints (("Goal" :in-theory (e/d (fn-hpb-put) (fn-hpb-used update-fn-hpb-used update-fn-hpb-wi))))))

(defthm fn-hpiz-zero-put-preserves-original-padded-region
 (let ((r (fn-hpb-put 0 fn-hpb)))
  (implies (and (fn-hpiz-region-invariantp raw page cap fn-hpb)
                (< page cap) (equal (car r) :stored))
   (and (fn-hpiz-region-invariantp raw page cap (mv-nth 1 r))
        (equal (fn-hpb-prefix (mv-nth 1 r)) (append (fn-hpb-prefix fn-hpb) '(0)))
        (equal (fn-hpb-used (mv-nth 1 r)) (+ 1 (fn-hpb-used fn-hpb)))
        (equal (fn-hpb-epoch (mv-nth 1 r)) (fn-hpb-epoch fn-hpb))
        (equal (fn-hpb-lease (mv-nth 1 r)) (fn-hpb-lease fn-hpb)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpiz-take-next (n (fn-hpb-used fn-hpb)) (xs (nthcdr (* 2048 page) (fn-hp-wpad raw))))
        (:instance fn-hpiz-nth-nthcdr (n (* 2048 page)) (j (fn-hpb-used fn-hpb)) (xs (fn-hp-wpad raw)))
        (:instance fn-hpiz-original-padded-region-past-used-is-zero
         (index (+ (* 2048 page) (fn-hpb-used fn-hpb))))
        (:instance fn-hpb-put-refines-prefix (w 0)))
  :in-theory (e/d (fn-hpiz-region-invariantp)
    (adt-cap fn-hpb-put fn-hpb-used fn-hpb-prefix fn-hpb-epoch fn-hpb-lease fn-hp-wpad
     update-fn-hpb-wi update-fn-hpb-used fn-hpb-wi fn-hpb-put-refines-prefix fn-hpiz-take-next fn-hpiz-nth-nthcdr take nth nthcdr mv-nth)))))

(local (defthm fn-hpiz-mv-zero
 (equal (mv-nth 0 x) (car x))
 :hints (("Goal" :in-theory (enable mv-nth)))))

(local (defthm fn-hpiz-put-selected-output
 (implies (and (natp region) (< region 5))
  (let ((r (fn-hpq-put region word fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (p (fn-hpb-put word (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))
   (and (equal (car r) (car p)) (equal (mv-nth (+ 1 region) r) (mv-nth 1 p)))))
 :hints (("Goal" :cases ((equal region 0) (equal region 1) (equal region 2) (equal region 3) (equal region 4))
  :in-theory (e/d (fn-hpq-put fn-hpq-model-select) (fn-hpb-put mv-nth))))))

(defun fn-hpiz-writer-ready-p (h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (let ((region (fn-omk-at 18 c)))
  (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :pad)
       (natp region) (< region 5)
       (< (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c))
       (case region
         (0 (fn-hpiz-region-invariantp (nth region (fn-hp-regs h (fn-omk-at 12 c))) (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c) fn-hpq0))
         (1 (fn-hpiz-region-invariantp (nth region (fn-hp-regs h (fn-omk-at 12 c))) (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c) fn-hpq1))
         (2 (fn-hpiz-region-invariantp (nth region (fn-hp-regs h (fn-omk-at 12 c))) (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c) fn-hpq2))
         (3 (fn-hpiz-region-invariantp (nth region (fn-hp-regs h (fn-omk-at 12 c))) (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c) fn-hpq3))
         (otherwise (fn-hpiz-region-invariantp (nth region (fn-hp-regs h (fn-omk-at 12 c))) (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c) fn-hpb))))))

(local (defthm fn-hpiz-await-has-no-continue-status
 (not (equal (car (fn-hpi-await-region region resume c)) :continue))
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-region fn-hpi-await-page)
   (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-hpi-write-effect fn-hpi-region-cap fn-hpi-region-start))))))

(local (defthm fn-hpiz-actual-padding-continue-output
 (let* ((region (fn-omk-at 18 c))
        (inner (fn-hpq-put region 0 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :pad)
                (natp region) (< region 5)
                (< (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c))
                (equal (car r) :continue))
   (and (equal (car inner) :stored)
        (equal r (mv :continue nil c ledger (mv-nth 1 inner) (mv-nth 2 inner)
                  (mv-nth 3 inner) (mv-nth 4 inner) (mv-nth 5 inner) pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-tick fn-hpi-buffer-step)
   (fn-hpi-grant-matchesp fn-hpi-await-region fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpi-region-cap fn-hpi-region-used fn-hpi-written fn-hpi-stream-step fn-hpi-supply
    fn-hpq-put fn-hpb-put fn-osj-native-grow fn-hpcx-tick fn-hpiv-io-effectp mv-nth))))))

(defthm fn-hpi-padding-step-preserves-original-canonical-region
 (let* ((region (fn-omk-at 18 c))
        (old (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
        (new (mv-nth (+ 4 region) r)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (equal (car r) :continue))
   (and (fn-hpiz-region-invariantp (nth region (fn-hp-regs h (fn-omk-at 12 c)))
          (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c) new)
        (equal (fn-hpb-prefix new) (append (fn-hpb-prefix old) '(0)))
        (equal (fn-hpb-used new) (+ 1 (fn-hpb-used old)))
        (equal (fn-hpb-epoch new) (fn-hpb-epoch old))
        (equal (fn-hpb-lease new) (fn-hpb-lease old))
        (implies (and (natp other) (< other 5) (not (equal other region)))
         (equal (mv-nth (+ 4 other) r) (fn-hpq-model-select other fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
        (equal (mv-nth 1 r) nil) (equal (mv-nth 2 r) c) (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 9 r) pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpiz-actual-padding-continue-output
        (:instance fn-hpiz-zero-put-preserves-original-padded-region
         (raw (nth (fn-omk-at 18 c) (fn-hp-regs h (fn-omk-at 12 c))))
         (page (nfix (fn-omk-at (fn-omk-at 18 c) (fn-omk-at 15 c))))
         (cap (fn-hpi-region-cap (fn-omk-at 18 c) c))
         (fn-hpb (fn-hpq-model-select (fn-omk-at 18 c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))
  :cases ((equal (fn-omk-at 18 c) 0) (equal (fn-omk-at 18 c) 1) (equal (fn-omk-at 18 c) 2)
          (equal (fn-omk-at 18 c) 3) (equal (fn-omk-at 18 c) 4)
          (equal other 0) (equal other 1) (equal other 2) (equal other 3) (equal other 4))
  :in-theory (e/d (fn-hpiz-writer-ready-p fn-hpq-model-select)
   (fn-hpi-tick fn-hpq-put fn-hpb-put fn-omk-at fn-hp-regs fn-hp-wpad
    fn-hpiz-region-invariantp fn-hpb-used fn-hpb-prefix fn-hpb-epoch fn-hpb-lease nth nthcdr mv-nth)))))

(local (defthm fn-hpiz-full-put-is-full-output
 (implies (and (natp region) (< region 5)
               (<= 2048 (fn-hpb-used (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))
  (equal (fn-hpq-put region 0 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
         (mv :full fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
 :hints (("Goal" :cases ((equal region 0) (equal region 1) (equal region 2) (equal region 3) (equal region 4))
  :in-theory (e/d (fn-hpq-put fn-hpb-put fn-hpq-model-select)
   (fn-hpb-used update-fn-hpb-wi update-fn-hpb-used fn-hpb-wi mv-nth))))))

(local (defthm fn-hpiz-actual-padding-write-output
 (let* ((region (fn-omk-at 18 c))
        (await (fn-hpi-await-region region :pad c))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :pad)
                (natp region) (< region 5)
                (< (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c))
                (equal (car r) :write))
   (and (<= 2048 (fn-hpb-used (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
        (equal (car await) :write)
        (equal r (mv :write (mv-nth 1 await) (mv-nth 2 await) ledger
                     fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-tick fn-hpi-buffer-step)
   (fn-hpi-grant-matchesp fn-hpi-await-region fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpi-region-cap fn-hpi-region-used fn-hpi-written fn-hpi-stream-step fn-hpi-supply
    fn-hpq-put fn-hpb-put fn-osj-native-grow fn-hpcx-tick fn-hpiv-io-effectp mv-nth))))))

(local (defthm fn-hpiz-prefix-aux-length
 (implies (natp k) (equal (len (fn-hpb-prefix-aux i k fn-hpb)) k))
 :hints (("Goal" :induct (fn-hpb-prefix-aux i k fn-hpb)
  :in-theory (e/d (fn-hpb-prefix-aux) (fn-hpb-wi))))))
(local (defthm fn-hpiz-prefix-length
 (implies (natp (fn-hpb-used fn-hpb)) (equal (len (fn-hpb-prefix fn-hpb)) (fn-hpb-used fn-hpb)))
 :hints (("Goal" :in-theory (e/d (fn-hpb-prefix) (fn-hpb-used fn-hpb-prefix-aux))))))

(defthm fn-hpi-padding-page-handoff-is-original-canonical-page
 (let* ((region (fn-omk-at 18 c))
        (selected (fn-hpq-model-select region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
        (await (fn-hpi-await-region region :pad c))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (equal (car r) :write))
   (and (equal (fn-hpb-used selected) 2048) (equal (len (fn-hpb-prefix selected)) 2048)
        (equal (fn-hpb-prefix selected)
          (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at region (fn-omk-at 15 c))))
             (fn-hp-wpad (nth region (fn-hp-regs h (fn-omk-at 12 c)))))))
        (equal r (mv :write (mv-nth 1 await) (mv-nth 2 await) ledger
                     fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpiz-actual-padding-write-output
        (:instance fn-hpiz-prefix-length
         (fn-hpb (fn-hpq-model-select (fn-omk-at 18 c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))
  :cases ((equal (fn-omk-at 18 c) 0) (equal (fn-omk-at 18 c) 1) (equal (fn-omk-at 18 c) 2)
          (equal (fn-omk-at 18 c) 3) (equal (fn-omk-at 18 c) 4))
  :in-theory (e/d (fn-hpiz-writer-ready-p fn-hpiz-region-invariantp fn-hpq-model-select)
   (fn-hpi-tick fn-hpi-await-region fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hpiz-prefix-length fn-hp-wpad fn-hp-regs fn-hpb-used fn-hpb-prefix take nth nthcdr mv-nth)))))
