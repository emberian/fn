; Canonical leading zero/header page carried through the actual HPI entry.
; Proof-only phase observers; full image/body/digest/INITIAL remain separate.
(in-package "ACL2")
(include-book "history-image-writer-refinement")

(defun fn-hpif-page-model (c)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-omk-at 0 c) :zero) (adt-zeros 2048)
  (fn-hp-hdr2 (fn-omk-at 7 c) (fn-hcc-lens (fn-omk-at 7 c) (fn-omk-at 8 c))
              (fn-hcc-starts (fn-omk-at 9 c))
              (fn-hcc-pages (fn-omk-at 9 c) (fn-omk-at 10 c)))))

(defun fn-hpif-invariantp (c fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (and (fn-omk-widthp c 25) (member-eq (fn-omk-at 0 c) '(:zero :header))
      (unsigned-byte-p 61 (fn-omk-at 7 c)) (unsigned-byte-p 64 (fn-omk-at 8 c))
      (unsigned-byte-p 51 (fn-omk-at 9 c)) (unsigned-byte-p 51 (fn-omk-at 10 c))
      (natp (fn-hpb-used fn-hpb)) (<= (fn-hpb-used fn-hpb) 2048)
      (equal (fn-hpb-prefix fn-hpb) (take (fn-hpb-used fn-hpb) (fn-hpif-page-model c)))))

(local (defthm fn-hpif-take-next
 (implies (natp n)
  (equal (append (take n xs) (list (nth n xs))) (take (+ 1 n) xs)))
 :hints (("Goal" :induct (take n xs) :in-theory (enable take nth)))))

(local (defun fn-hpif-zero-ind (i n)
 (if (zp i) n (fn-hpif-zero-ind (1- i) (1- n)))))
(local (defthm fn-hpif-nth-zero
 (implies (and (natp i) (natp n) (< i n)) (equal (nth i (adt-zeros n)) 0))
 :hints (("Goal" :induct (fn-hpif-zero-ind i n) :in-theory (enable nth adt-zeros)))))

(local (defthm fn-hpif-hch-used-increments
 (implies (< (fn-hpb-used fn-hpb) 2048)
  (equal (fn-hpb-used (mv-nth 1 (fn-hch-tick count pool column-cap pool-cap fn-hpb)))
         (+ 1 (fn-hpb-used fn-hpb))))
 :hints (("Goal" :in-theory (e/d (fn-hch-tick fn-hpb-put fn-hpb-used) (fn-hch-word))))))

(local (defthm fn-hpif-put-used-increments
 (implies (< (fn-hpb-used fn-hpb) 2048)
  (equal (fn-hpb-used (mv-nth 1 (fn-hpb-put w fn-hpb))) (+ 1 (fn-hpb-used fn-hpb))))
 :hints (("Goal" :in-theory (enable fn-hpb-put fn-hpb-used)))))

(local (defthm fn-hpif-hch-is-stored-or-done
 (equal (car (fn-hch-tick count pool column-cap pool-cap fn-hpb))
        (if (< (fn-hpb-used fn-hpb) 2048) :stored :done))
 :hints (("Goal" :in-theory (e/d (fn-hch-tick fn-hpb-put fn-hpb-used) (fn-hch-word))))))

(local (defthm fn-hpif-put-is-stored-or-full
 (equal (car (fn-hpb-put w fn-hpb))
        (if (< (fn-hpb-used fn-hpb) 2048) :stored :full))
 :hints (("Goal" :in-theory (enable fn-hpb-put fn-hpb-used)))))

(local (defthm fn-hpif-await-page-is-write
 (equal (car (fn-hpi-await-page region logical physical buffer resume c)) :write)
 :hints (("Goal" :in-theory (e/d (fn-hpi-await-page)
                               (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-hpi-write-effect))))))

(local (defthm fn-hpif-mv-zero (equal (mv-nth 0 x) (car x))
 :hints (("Goal" :in-theory (enable mv-nth)))))

(local (defthm fn-hpif-buffer-continue-complete-output
 (let ((r (fn-hpi-buffer-step c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (fn-hpif-invariantp c fn-hpb) (equal (car r) :continue))
   (and (< (fn-hpb-used fn-hpb) 2048)
        (equal (mv-nth 1 r) nil) (equal (mv-nth 2 r) c)
        (equal (mv-nth 3 r) fn-hpq0) (equal (mv-nth 4 r) fn-hpq1)
        (equal (mv-nth 5 r) fn-hpq2) (equal (mv-nth 6 r) fn-hpq3)
        (equal (fn-hpb-used (mv-nth 7 r)) (+ 1 (fn-hpb-used fn-hpb)))
        (equal (fn-hpb-prefix (mv-nth 7 r))
               (take (+ 1 (fn-hpb-used fn-hpb)) (fn-hpif-page-model c)))
        (equal (fn-hpb-epoch (mv-nth 7 r)) (fn-hpb-epoch fn-hpb))
        (equal (fn-hpb-lease (mv-nth 7 r)) (fn-hpb-lease fn-hpb)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :cases ((equal (fn-omk-at 0 c) :zero))
  :use ((:instance fn-hpif-take-next (n (fn-hpb-used fn-hpb)) (xs (fn-hpif-page-model c))))
  :in-theory (e/d (fn-hpi-buffer-step fn-hpif-invariantp fn-hpif-page-model)
   (fn-hch-tick fn-hpb-put fn-hpi-await-page fn-hpi-await-region fn-hpi-set
    fn-hpi-set-is-update-by-definition fn-omk-at fn-hpb-used fn-hpb-prefix
    fn-hpb-epoch fn-hpb-lease fn-hp-hdr2 fn-hcc-lens fn-hcc-starts fn-hcc-pages
    fn-hpcx-tick fn-hpq-put fn-hpi-region-used fn-hpi-region-cap mv-nth fn-hpif-take-next adt-nth-1+ take nth adt-zeros (:executable-counterpart adt-zeros) unsigned-byte-p))))))

(defthm fn-hpi-tick-preserves-canonical-leading-page
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpif-invariantp c fn-hpb) (equal (car r) :continue))
   (and (fn-hpif-invariantp (mv-nth 2 r) (mv-nth 8 r))
        (equal (mv-nth 1 r) nil) (equal (mv-nth 2 r) c) (equal (mv-nth 3 r) ledger)
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3)
        (equal (mv-nth 9 r) pgs-digest-state)
        (equal (fn-hpb-used (mv-nth 8 r)) (+ 1 (fn-hpb-used fn-hpb)))
        (equal (fn-hpb-epoch (mv-nth 8 r)) (fn-hpb-epoch fn-hpb))
        (equal (fn-hpb-lease (mv-nth 8 r)) (fn-hpb-lease fn-hpb)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpif-buffer-continue-complete-output)
  :in-theory (e/d (fn-hpi-tick fn-hpif-invariantp)
   (fn-hpi-buffer-step fn-hpi-written fn-hpi-supply fn-hpi-stream-step fn-osj-native-grow
    fn-hpi-growth-request fn-hpi-grant-matchesp fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-omk-at fn-hpb-used fn-hpb-prefix fn-hpb-epoch fn-hpb-lease fn-hpif-page-model
    take nth unsigned-byte-p mv-nth)))))

(local (defthm fn-hpif-hch-full-is-unchanged-by-definition
 (implies (<= 2048 (fn-hpb-used fn-hpb))
  (equal (fn-hch-tick count pool column-cap pool-cap fn-hpb) (mv :done fn-hpb)))
 :hints (("Goal" :in-theory (e/d (fn-hch-tick) (fn-hpb-used fn-hch-word fn-hpb-put))))))

(local (defthm fn-hpif-put-full-is-unchanged-by-definition
 (implies (<= 2048 (fn-hpb-used fn-hpb))
  (equal (fn-hpb-put w fn-hpb) (mv :full fn-hpb)))
 :hints (("Goal" :in-theory (e/d (fn-hpb-put) (fn-hpb-used))))))

(defun fn-hpif-page-region (c)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-omk-at 0 c) :zero) :zero :header))
(defun fn-hpif-page-physical (c)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-omk-at 0 c) :zero) 0
  (nfix (fn-omk-at 4 (fn-omk-at 1 (fn-omk-at 6 c))))))
(defun fn-hpif-page-resume (c)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-omk-at 0 c) :zero) :header :body))

(local (defthm fn-hpif-buffer-write-complete-output
 (let ((r (fn-hpi-buffer-step c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (implies (and (fn-hpif-invariantp c fn-hpb) (equal (car r) :write))
   (and (equal (fn-hpb-used fn-hpb) 2048)
        (equal (fn-hpb-prefix fn-hpb) (take 2048 (fn-hpif-page-model c)))
        (equal r
         (let ((issued (fn-hpi-await-page (fn-hpif-page-region c)
                          (if (equal (fn-omk-at 0 c) :zero) nil 0)
                          (fn-hpif-page-physical c) 4 (fn-hpif-page-resume c) c)))
          (mv :write (mv-nth 1 issued) (mv-nth 2 issued)
              fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :cases ((equal (fn-omk-at 0 c) :zero))
  :in-theory (e/d (fn-hpi-buffer-step fn-hpif-invariantp fn-hpif-page-region
                   fn-hpif-page-physical fn-hpif-page-resume)
   (fn-hch-tick fn-hpb-put fn-hpi-await-page fn-hpi-await-region fn-hpi-set
    fn-hpi-set-is-update-by-definition fn-omk-at fn-hpb-used fn-hpb-prefix
    fn-hpb-epoch fn-hpb-lease fn-hp-hdr2 fn-hcc-lens fn-hcc-starts fn-hcc-pages
    fn-hpcx-tick fn-hpq-put fn-hpi-region-used fn-hpi-region-cap mv-nth
    fn-hpif-page-model fn-hpif-take-next adt-nth-1+ take nth adt-zeros
    (:executable-counterpart adt-zeros) unsigned-byte-p))))))

(defthm fn-hpi-tick-hands-off-complete-canonical-leading-page
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpif-invariantp c fn-hpb) (equal (car r) :write))
   (and (equal (fn-hpb-used fn-hpb) 2048)
        (equal (fn-hpb-prefix fn-hpb) (take 2048 (fn-hpif-page-model c)))
        (equal r
         (let ((issued (fn-hpi-await-page (fn-hpif-page-region c)
                          (if (equal (fn-omk-at 0 c) :zero) nil 0)
                          (fn-hpif-page-physical c) 4 (fn-hpif-page-resume c) c)))
          (mv :write (mv-nth 1 issued) (mv-nth 2 issued) ledger
              fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :use (fn-hpif-buffer-write-complete-output)
  :in-theory (e/d (fn-hpi-tick fn-hpif-invariantp)
   (fn-hpi-buffer-step fn-hpi-written fn-hpi-supply fn-hpi-stream-step fn-osj-native-grow
    fn-hpi-growth-request fn-hpi-grant-matchesp fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-omk-at fn-hpb-used fn-hpb-prefix fn-hpb-epoch fn-hpb-lease fn-hpif-page-model
    fn-hpif-page-region fn-hpif-page-physical fn-hpif-page-resume fn-hpi-await-page
    fn-hpif-take-next adt-nth-1+ take nth unsigned-byte-p mv-nth)))))
