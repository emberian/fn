; Actual padding scheduling joins; original canonical carries are proof-only.
(in-package "ACL2")
(include-book "history-image-padding-pages")
(local
 (defun fn-hpizs-field-ind (j k c)
  (if (or (zp j) (zp k)) (list j k c)
    (fn-hpizs-field-ind (1- j) (1- k) (if (consp c) (cdr c) nil)))))

(local
 (defthm fn-hpizs-set-field
  (implies (and (natp k) (< k 25) (natp j) (< j 25))
   (equal (fn-omk-at j (fn-hpi-set k value c))
          (if (equal j k) value (fn-omk-at j c))))
  :hints (("Goal" :induct (fn-hpizs-field-ind j k c)
           :expand ((fn-hpi-set k value c)
                    (fn-omk-at j c)
                    (fn-omk-at j (fn-hpi-set k value c))
                    (:free (a d) (fn-omk-at j (cons a d))))
           :in-theory (e/d (fn-omk-at fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))


(local (defthm fn-hpizs-mv-zero (equal (mv-nth 0 x) (car x))
 :hints (("Goal" :in-theory (enable mv-nth)))))


(defun fn-hpizs-region-contextp (c)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :pad)
      (natp (fn-omk-at 18 c)) (< (fn-omk-at 18 c) 5)))

(local (defthm fn-hpizs-at-cap-advance-output
 (let* ((region (fn-omk-at 18 c))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpizs-region-contextp c)
                (equal (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c))
                (equal (car r) :continue))
   (and (equal (fn-hpi-region-used region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) 0)
        (equal r (mv :continue nil (fn-hpi-set 18 (+ 1 region) c) ledger
                    fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpizs-region-contextp fn-hpi-tick fn-hpi-buffer-step)
   (fn-hpi-grant-matchesp fn-hpi-region-cap fn-hpi-region-used fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-hpi-written fn-hpi-supply fn-hpi-stream-step fn-osj-native-grow fn-hpq-put fn-hpb-put fn-hpcx-tick mv-nth))))))

(defthm fn-hpi-complete-padding-region-advances-with-canonical-carry
 (let* ((region (fn-omk-at 18 c))
        (r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpizs-region-contextp c)
                (fn-hpizp-five-invariantp h (fn-omk-at 12 c) (fn-omk-at 15 c) (fn-omk-at 9 c) (fn-omk-at 10 c)
                  fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (equal (nfix (fn-omk-at region (fn-omk-at 15 c))) (fn-hpi-region-cap region c))
                (equal (car r) :continue))
   (and (equal (fn-hpi-region-used region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) 0)
        (equal r (mv :continue nil (fn-hpi-set 18 (+ 1 region) c) ledger
                    fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
        (fn-hpizp-five-invariantp h (fn-omk-at 12 (mv-nth 2 r)) (fn-omk-at 15 (mv-nth 2 r))
          (fn-omk-at 9 (mv-nth 2 r)) (fn-omk-at 10 (mv-nth 2 r))
          (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :use fn-hpizs-at-cap-advance-output
  :in-theory (e/d () (fn-hpi-tick fn-hpizp-five-invariantp fn-hpizs-region-contextp fn-hpi-set
   fn-hpi-set-is-update-by-definition fn-omk-at fn-hpi-region-cap fn-hpi-region-used mv-nth)))))

(defun fn-hpizs-terminal-contextp (c)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-omk-widthp c 25) (equal (fn-omk-at 0 c) :pad) (equal (fn-omk-at 18 c) 5)))
(defun fn-hpizs-pages-complete-p (c)
 (declare (xargs :guard t :verify-guards nil))
 (and (equal (nfix (fn-omk-at 0 (fn-omk-at 15 c))) (nfix (fn-omk-at 9 c)))
      (equal (nfix (fn-omk-at 1 (fn-omk-at 15 c))) (nfix (fn-omk-at 9 c)))
      (equal (nfix (fn-omk-at 2 (fn-omk-at 15 c))) (nfix (fn-omk-at 9 c)))
      (equal (nfix (fn-omk-at 3 (fn-omk-at 15 c))) (nfix (fn-omk-at 9 c)))
      (equal (nfix (fn-omk-at 4 (fn-omk-at 15 c))) (nfix (fn-omk-at 10 c)))))

(local (defthm fn-hpizs-full-region-tail-empty
 (implies (fn-hpiz-region-invariantp raw (nfix cap) (nfix cap) fn-hpb)
  (equal (fn-hpb-used fn-hpb) 0))
 :hints (("Goal" :in-theory (e/d (fn-hpiz-region-invariantp)
   (fn-hpb-used fn-hpb-prefix adt-cap fn-hp-wpad nthcdr))))))
(local (defthm fn-hpizs-at-is-nth-by-definition
 (equal (fn-omk-at n xs) (nth n xs))
 :hints (("Goal" :induct (fn-omk-at n xs) :in-theory (enable fn-omk-at nth)))))
(local (defthm fn-hpizs-complete-five-tails-empty
 (implies (and (fn-hpizs-pages-complete-p c)
               (fn-hpizp-five-invariantp h (fn-omk-at 12 c) (fn-omk-at 15 c) (fn-omk-at 9 c) (fn-omk-at 10 c)
                 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
  (and (equal (fn-hpb-used fn-hpq0) 0) (equal (fn-hpb-used fn-hpq1) 0)
       (equal (fn-hpb-used fn-hpq2) 0) (equal (fn-hpb-used fn-hpq3) 0) (equal (fn-hpb-used fn-hpb) 0)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hpizs-full-region-tail-empty (raw (nth 0 (fn-hp-regs h (fn-omk-at 12 c)))) (cap (fn-omk-at 9 c)) (fn-hpb fn-hpq0))
        (:instance fn-hpizs-full-region-tail-empty (raw (nth 1 (fn-hp-regs h (fn-omk-at 12 c)))) (cap (fn-omk-at 9 c)) (fn-hpb fn-hpq1))
        (:instance fn-hpizs-full-region-tail-empty (raw (nth 2 (fn-hp-regs h (fn-omk-at 12 c)))) (cap (fn-omk-at 9 c)) (fn-hpb fn-hpq2))
        (:instance fn-hpizs-full-region-tail-empty (raw (nth 3 (fn-hp-regs h (fn-omk-at 12 c)))) (cap (fn-omk-at 9 c)) (fn-hpb fn-hpq3))
        (:instance fn-hpizs-full-region-tail-empty (raw (nth 4 (fn-hp-regs h (fn-omk-at 12 c)))) (cap (fn-omk-at 10 c))))
  :in-theory (e/d (fn-hpizs-pages-complete-p fn-hpizp-five-invariantp fn-hpizs-at-is-nth-by-definition)
   (nfix fn-omk-at fn-hpiz-region-invariantp fn-hpb-used fn-hp-regs nth nthcdr fn-hpizs-full-region-tail-empty))))))

(local (defthm fn-hpizs-terminal-output
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpizs-terminal-contextp c) (equal (car r) :continue))
   (equal r (mv :continue nil (fn-hpi-set 0 :data-digest-start c) ledger
                 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpizs-terminal-contextp fn-hpi-tick fn-hpi-buffer-step)
   (fn-hpi-grant-matchesp fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition
    fn-hpi-written fn-hpi-supply fn-hpi-stream-step fn-osj-native-grow fn-hpq-put fn-hpb-put fn-hpcx-tick mv-nth))))))

(defthm fn-hpi-complete-padding-starts-digest-with-canonical-carry
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpizs-terminal-contextp c) (fn-hpizs-pages-complete-p c)
                (fn-hpizp-five-invariantp h (fn-omk-at 12 c) (fn-omk-at 15 c) (fn-omk-at 9 c) (fn-omk-at 10 c)
                  fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (equal (car r) :continue))
   (and (equal (fn-hpb-used fn-hpq0) 0) (equal (fn-hpb-used fn-hpq1) 0)
        (equal (fn-hpb-used fn-hpq2) 0) (equal (fn-hpb-used fn-hpq3) 0) (equal (fn-hpb-used fn-hpb) 0)
        (equal r (mv :continue nil (fn-hpi-set 0 :data-digest-start c) ledger
                      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
        (fn-hpizp-five-invariantp h (fn-omk-at 12 (mv-nth 2 r)) (fn-omk-at 15 (mv-nth 2 r))
          (fn-omk-at 9 (mv-nth 2 r)) (fn-omk-at 10 (mv-nth 2 r))
          (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpizs-terminal-output fn-hpizs-complete-five-tails-empty)
  :in-theory (e/d () (fn-hpi-tick fn-hpizp-five-invariantp fn-hpizs-terminal-contextp fn-hpizs-pages-complete-p
   fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-hpb-used fn-hpizs-at-is-nth-by-definition mv-nth)))))
