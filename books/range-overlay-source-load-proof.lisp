; The recursive adapter loads every row of an admitted sorted source.
; Its final index and resident bytes describe the whole source.
(in-package "ACL2")
(include-book "range-overlay-prefix-preserved-proof")

(local (include-book "range-overlay-source-order-proof"))

(local
 (defun-nx fn2-ov-follow-source (rows tail src sg ov ix f pool)
   (declare (xargs :measure (len tail)))
   (if (atom tail) (list ov ix f pool)
     (let ((r (fn2-ov-source-insert rows (car tail) src sg ov ix f pool)))
       (fn2-ov-follow-source (append rows (list (car tail))) (cdr tail) src sg
                             (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))))))

(local
 (defthm fn2-ov-loader-with-first-accepted
   (let* ((load (fn2-ov-source-load rows (car tail) src sg f pool))
          (r (fn2-ov-source-insert rows (car tail) src sg ov ix f pool))
          (rest (fn2-ov-adapter-load 3 *fn2-overview-entry* (cdr tail) src sg
                   (fn2-range-line-bytes (append rows (list (car tail))))
                   (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))))
     (implies (and (consp tail) (equal (car load) :ok) (equal (car r) :ok)
                   (equal (mv-nth 1 load) (fn2-range-line-bytes (append rows (list (car tail))))))
              (equal (fn2-ov-adapter-load 3 *fn2-overview-entry* tail src sg (fn2-range-line-bytes rows) ov ix f pool)
                     (list (cons :ok (car rest)) (mv-nth 1 rest) (mv-nth 2 rest) (mv-nth 3 rest) (mv-nth 4 rest)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :expand ((fn2-ov-adapter-load 3 *fn2-overview-entry* tail src sg (fn2-range-line-bytes rows) ov ix f pool))
            :in-theory (union-theories (theory 'minimal-theory)
                       '(eq (:t fn2-run-load-values) (:t fn2-ov-insert) (:t fn2-ov-adapter-load)
                         mv-nth car-cons cdr-cons (:e equal) (:e mv-nth) (:e binary-+) (:e unary--) (:e not) (:e zp)))))))

(local
 (defthm fn2-ov-step-mv-cons
   (equal (mv-nth i (cons a b)) (if (zp i) a (mv-nth (1- i) b)))))

(local
 (defthmd fn2-ov-complete-segment
  (let* ((all (append rows tail))
         (run (fn2-ov-adapter-load 3 *fn2-overview-entry* tail src sg (fn2-range-line-bytes rows) ov ix f pool)))
    (implies (and (fn2-ov-physical-prefix-p rows src sg ov ix f pool) (fn2-ov-source-segment-p rows tail))
             (and (subsetp-equal (car run) '(:ok)) (equal (len (car run)) (len tail))
                  (fn2-ov-physical-prefix-p all src sg (mv-nth 1 run) (mv-nth 2 run) (mv-nth 3 run) (mv-nth 4 run)))))
  :hints (("Goal" :induct (fn2-ov-follow-source rows tail src sg ov ix f pool) :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                      '((:induction fn2-ov-follow-source) cons-car-cdr atom fn2-ov-list-shift-prefix fn2-ov-step-mv-cons car-cons cdr-cons
                        (:e zp) (:e equal) (:e not) (:e len) (:e subsetp-equal) (:e member-equal)
                        (:e binary-+) (:e unary--) (:e consp) (:e mv-nth))))
          ("Subgoal *1/2" :use ((:instance fn2-ov-source-insert-preserves-physical-prefix (row (car tail)))
                                fn2-ov-source-segment-advances fn2-ov-loader-with-first-accepted)
                         :expand ((len tail) (:free (x) (len (cons :ok x))) (:free (x) (subsetp-equal (cons :ok x) '(:ok)))))
          ("Subgoal *1/1" :expand ((fn2-ov-adapter-load 3 *fn2-overview-entry* tail src sg (fn2-range-line-bytes rows) ov ix f pool))
                         :in-theory (union-theories (theory 'minimal-theory)
                              '(fn2-ov-source-segment-p atom true-listp fn2-ov-append-empty-tail
                                fn2-ov-step-mv-cons car-cons cdr-cons (:e equal) (:e not) (:e true-listp)
                                (:e len) (:e subsetp-equal) (:e binary-+) (:e unary--) (:e zp) (:e mv-nth)))))))

(defthmd fn2-ov-adapter-loads-complete-source
  (let* ((all (append rows tail))
         (run (fn2-ov-adapter-load 3 *fn2-overview-entry* tail src sg (fn2-range-line-bytes rows) ov ix f pool)))
    (implies (and (fn2-ov-physical-prefix-p rows src sg ov ix f pool) (true-listp rows) (true-listp tail)
                  (fn2-run-entries-layoutp *fn2-overview-entry* rows) (fn2-run-entries-layoutp *fn2-overview-entry* tail)
                  (fn2-run-sorted-spec *fn2-overview-range-key* all) (<= (len all) 48))
             (and (subsetp-eq (car run) '(:ok)) (equal (len (car run)) (len tail))
                  (fn2-ov-physical-prefix-p all src sg (mv-nth 1 run) (mv-nth 2 run) (mv-nth 3 run) (mv-nth 4 run)))))
  :hints (("Goal" :use fn2-ov-complete-segment
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-ov-source-segment-p (:e equal) (:e not))))))
