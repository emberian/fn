; LC composes existing PGS verdicts, retaining PGS's newest-first fallback.
; No column entry is submitted to a digest check by this selector.
(in-package "ACL2")
(include-book "log-checkpoint-cold-candidate")
(include-book "defkeystone")

(defun fn-lc-cold-page-program (pages)
 (declare (xargs :guard t))
 (if (consp pages)
  (cons (list :pread :page (car pages) (fn-lc-page-octets))
        (fn-lc-cold-page-program (cdr pages))) nil))
(defun fn-lc-cold-pgs-choice-order (order slots pages refusals)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp order)
  (let* ((k (car order)) (rec (pgs-slot k slots))
         (candidate (fn-lc-cold-candidate rec pages))
         (verdict (fn-lc-head candidate)))
   (if (equal (fn-lc-head verdict) :ok)
       (list :ok k (pgs-rec-txid rec) (list (fn-lc-at 2 candidate)) refusals)
     (fn-lc-cold-pgs-choice-order (cdr order) slots pages
      (fn-lc-join refusals (list (list :slot k (fn-lc-rest verdict)))))))
  (list :refused refusals)))
(defun fn-lc-cold-root-order (disk r)
 (declare (xargs :guard t))
 (let* ((slots (pgs-root-slots r disk))
        (s0 (pgs-slot 0 slots)) (s1 (pgs-slot 1 slots)))
  (pgs-open-order s0 (pgs-rec-valid s0) s1 (pgs-rec-valid s1))))
(defun fn-lc-cold-slot-refusals (disk r)
 (declare (xargs :guard t))
 (let* ((slots (pgs-root-slots r disk))
        (s0 (pgs-slot 0 slots)) (s1 (pgs-slot 1 slots)))
  (pgs-slot-refusals s0 (pgs-rec-valid s0) s1 (pgs-rec-valid s1))))
(defun fn-lc-cold-pgs-choice (disk r mode)
 (declare (xargs :guard t :verify-guards nil) (ignore mode))
 (fn-lc-cold-pgs-choice-order (fn-lc-cold-root-order disk r)
   (pgs-root-slots r disk) (pgs-pages disk) (fn-lc-cold-slot-refusals disk r)))
(defun fn-lc-cold-select-order (order slots pages refusals)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp order)
  (let* ((k (car order)) (rec (pgs-slot k slots))
         (candidate (fn-lc-cold-candidate rec pages))
         (verdict (fn-lc-head candidate))
         (requests (fn-lc-at 3 candidate)))
   (if (equal (fn-lc-head verdict) :ok)
       (list (list :ok k (pgs-rec-txid rec) (list (fn-lc-at 2 candidate)) refusals)
             requests (fn-lc-at 1 candidate))
     (let ((rest (fn-lc-cold-select-order (cdr order) slots pages
                   (fn-lc-join refusals (list (list :slot k (fn-lc-rest verdict)))))))
      (list (fn-lc-head rest) (fn-lc-join requests (fn-lc-at 1 rest))
            (fn-lc-at 2 rest)))))
  (list (list :refused refusals) nil nil)))
; Stable memoization retains each physical request at its first use.
(defun fn-lc-cold-first-requests (pages seen)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp pages)
  (if (ec-call (member-equal (car pages) seen))
      (fn-lc-cold-first-requests (cdr pages) seen)
    (cons (car pages) (fn-lc-cold-first-requests (cdr pages) (cons (car pages) seen)))) nil))
; Reference path: inspect candidates in PGS order and stop at the first
; accepted metadata verdict. Each candidate reports its checked prefix.
(defun fn-lc-cold-path-order (order slots pages)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp order)
  (let* ((candidate (fn-lc-cold-candidate (pgs-slot (car order) slots) pages))
         (requests (fn-lc-at 3 candidate)))
   (if (equal (fn-lc-head (fn-lc-head candidate)) :ok) requests
    (fn-lc-join requests (fn-lc-cold-path-order (cdr order) slots pages)))) nil))
(defun fn-lc-cold-only-metadata-requests-p (trace metadata-pages)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp trace)
  (let ((request (car trace)))
   (and (equal (fn-lc-head request) :pread)
        (or (and (equal (fn-lc-at 1 request) :root)
                 (or (equal (fn-lc-at 2 request) 0) (equal (fn-lc-at 2 request) 1)))
            (and (equal (fn-lc-at 1 request) :page)
                 (ec-call (member-equal (fn-lc-at 2 request) metadata-pages))))
        (fn-lc-cold-only-metadata-requests-p (cdr trace) metadata-pages))) t))
(verify-guards fn-lc-cold-first-requests)
(verify-guards fn-lc-cold-path-order)
(verify-guards fn-lc-cold-only-metadata-requests-p)

(defun fn-lc-cold-select (disk r mode)
 (declare (xargs :guard t :verify-guards nil) (ignore mode))
 (let* ((out (fn-lc-cold-select-order (fn-lc-cold-root-order disk r)
               (pgs-root-slots r disk) (pgs-pages disk) (fn-lc-cold-slot-refusals disk r)))
        (choice (fn-lc-head out))
        (trace (fn-lc-join
          (list (list :pread :root 0 (fn-lc-root-slot-octets))
                (list :pread :root 1 (fn-lc-root-slot-octets)))
          (fn-lc-cold-page-program (fn-lc-cold-first-requests (fn-lc-at 1 out) nil)))))
  (list (fn-lc-head choice) (fn-lc-at 1 choice) (fn-lc-at 2 choice)
        (fn-lc-at 3 choice) (fn-lc-at 4 choice) trace (fn-lc-at 2 out))))
(defun fn-lc-cold-directory-path (disk r mode)
 (declare (xargs :guard t :verify-guards nil) (ignore mode))
 (fn-lc-cold-first-requests
  (fn-lc-cold-path-order (fn-lc-cold-root-order disk r)
                        (pgs-root-slots r disk) (pgs-pages disk)) nil))
(verify-guards fn-lc-cold-pgs-choice-order)
(verify-guards fn-lc-cold-pgs-choice)
(verify-guards fn-lc-cold-select-order)
(verify-guards fn-lc-cold-select)
(verify-guards fn-lc-cold-directory-path)


(local (include-book "../tests/acl2/lc-open-fixtures"))
(local (include-book "log-checkpoint-selection-proof"))
(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
 ; Whole-claim positives and isolated biting mutations BEFORE the proof.
 ; empty
 (assert-event (let* ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager))
 (let ((out (fn-lc-cold-select disk r mode)))
  (and (equal (fn-lc-take 5 out) (fn-lc-take 5 (fn-lc-cold-pgs-choice disk r mode)))
       (equal (fn-lc-at 5 out)
        (fn-lc-join
         (list (list :pread :root 0 (fn-lc-root-slot-octets))
               (list :pread :root 1 (fn-lc-root-slot-octets)))
         (fn-lc-cold-page-program (fn-lc-cold-directory-path disk r mode))))
       (fn-lc-cold-only-metadata-requests-p
         (fn-lc-at 5 out) (fn-lc-cold-directory-path disk r mode))))))
 ; fallback
 (assert-event (let* ((disk (lcc-fallback-disk)) (r :lc) (mode :eager))
 (let ((out (fn-lc-cold-select disk r mode)))
  (and (equal (fn-lc-take 5 out) (fn-lc-take 5 (fn-lc-cold-pgs-choice disk r mode)))
       (equal (fn-lc-at 5 out)
        (fn-lc-join
         (list (list :pread :root 0 (fn-lc-root-slot-octets))
               (list :pread :root 1 (fn-lc-root-slot-octets)))
         (fn-lc-cold-page-program (fn-lc-cold-directory-path disk r mode))))
       (fn-lc-cold-only-metadata-requests-p
         (fn-lc-at 5 out) (fn-lc-cold-directory-path disk r mode))))))
 ; eager
 (assert-event (let* ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager))
 (not (let ((out (fn-lc-cold-select disk r mode)))
(and (equal (fn-lc-take 5 out) (fn-lc-take 5 (fn-lc-cold-pgs-choice disk r mode)))
       (equal (fn-lc-at 5 out)
        (fn-lc-join
         (list (list :pread :root 0 (fn-lc-root-slot-octets))
               (list :pread :root 1 (fn-lc-root-slot-octets)))
         (fn-lc-cold-page-program (fn-lc-cold-directory-path disk r mode))))
       (fn-lc-cold-only-metadata-requests-p
         (fn-lc-join (fn-lc-at 5 out) (fn-lc-cold-page-program (list 2)))
         (fn-lc-cold-directory-path disk r mode)))))))
 ; drop99
 (assert-event (let* ((disk (lcc-fallback-disk)) (r :lc) (mode :eager))
 (not (let ((out (fn-lc-cold-select disk r mode)))
(and (equal (fn-lc-take 5 out) (fn-lc-take 5 (fn-lc-cold-pgs-choice disk r mode)))
       (equal (remove-equal (list :pread :page 99 (fn-lc-page-octets)) (fn-lc-at 5 out))
        (fn-lc-join
         (list (list :pread :root 0 (fn-lc-root-slot-octets))
               (list :pread :root 1 (fn-lc-root-slot-octets)))
         (fn-lc-cold-page-program (fn-lc-cold-directory-path disk r mode))))
       (fn-lc-cold-only-metadata-requests-p
         (fn-lc-at 5 out) (fn-lc-cold-directory-path disk r mode)))))))
)
(local (defthm fn-lc-cold-choice-order-agrees
 (equal (car (fn-lc-cold-select-order order slots pages refusals))
        (fn-lc-cold-pgs-choice-order order slots pages refusals))
 :hints (("Goal" :induct (fn-lc-cold-select-order order slots pages refusals)
  :in-theory (disable fn-lc-cold-candidate)))))
(local (defthm fn-lc-cold-path-order-agrees
 (equal (nth 1 (fn-lc-cold-select-order order slots pages refusals))
        (fn-lc-cold-path-order order slots pages))
 :hints (("Goal" :induct (fn-lc-cold-select-order order slots pages refusals)
  :in-theory (disable fn-lc-cold-candidate)))))
(local (defthm fn-lc-cold-metadata-of-append
 (equal (fn-lc-cold-only-metadata-requests-p (append a b) allowed)
        (and (fn-lc-cold-only-metadata-requests-p a allowed)
             (fn-lc-cold-only-metadata-requests-p b allowed)))))
(local (defthm fn-lc-cold-metadata-cons-unfolds
 (equal (fn-lc-cold-only-metadata-requests-p (cons request trace) allowed)
  (and (equal (fn-lc-head request) :pread)
       (or (and (equal (fn-lc-at 1 request) :root)
                (or (equal (fn-lc-at 2 request) 0) (equal (fn-lc-at 2 request) 1)))
           (and (equal (fn-lc-at 1 request) :page)
                (member-equal (fn-lc-at 2 request) allowed)))
       (fn-lc-cold-only-metadata-requests-p trace allowed)))))
(local (defthm fn-lc-cold-page-program-is-metadata
 (implies (subsetp-equal pages allowed)
  (fn-lc-cold-only-metadata-requests-p (fn-lc-cold-page-program pages) allowed))
 :hints (("Goal" :induct (fn-lc-cold-page-program pages)))))
(local (defthm fn-lc-cold-subset-self
 (subsetp-equal pages pages)))
(local (defthm fn-lc-cold-take-five-unfolds
 (equal (take 5 x) (list (car x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)))
 :hints (("Goal" :in-theory (enable take nth)
  :expand ((take 5 x) (:free (y) (take 4 y)) (:free (y) (take 3 y))
           (:free (y) (take 2 y)) (:free (y) (take 1 y)))))))
(defthm fn-lc-cold-selection-is-metadata-only
 (let ((out (fn-lc-cold-select disk r mode)))
  (and (equal (fn-lc-take 5 out) (fn-lc-take 5 (fn-lc-cold-pgs-choice disk r mode)))
       (equal (fn-lc-at 5 out)
        (fn-lc-join
         (list (list :pread :root 0 (fn-lc-root-slot-octets))
               (list :pread :root 1 (fn-lc-root-slot-octets)))
         (fn-lc-cold-page-program (fn-lc-cold-directory-path disk r mode))))
       (fn-lc-cold-only-metadata-requests-p
         (fn-lc-at 5 out) (fn-lc-cold-directory-path disk r mode))))
 :rule-classes nil
 :hints (("Goal" :in-theory
   (e/d (fn-lc-cold-select fn-lc-cold-pgs-choice fn-lc-cold-directory-path)
        (fn-lc-cold-select-order fn-lc-cold-pgs-choice-order fn-lc-cold-path-order
         fn-lc-cold-root-order fn-lc-cold-slot-refusals fn-lc-cold-first-requests
         fn-lc-cold-candidate fn-lc-cold-page-program fn-lc-cold-only-metadata-requests-p)))))
(encapsulate ()
 (local (defattach pgs-digest fn-lc-proof-digest))
 (defteeth fn-lc-cold-selection-is-metadata-only
 :claim (let ((out (fn-lc-cold-select disk r mode)))
  (() (and (equal (fn-lc-take 5 out) (fn-lc-take 5 (fn-lc-cold-pgs-choice disk r mode)))
       (equal (fn-lc-at 5 out)
        (fn-lc-join
         (list (list :pread :root 0 (fn-lc-root-slot-octets))
               (list :pread :root 1 (fn-lc-root-slot-octets)))
         (fn-lc-cold-page-program (fn-lc-cold-directory-path disk r mode))))
       (fn-lc-cold-only-metadata-requests-p
         (fn-lc-at 5 out) (fn-lc-cold-directory-path disk r mode)))))
 :subject fn-lc-cold-select
 :witness ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager))
 :breaks nil
 :mutations ((eager-column-validation (:conclusion (and (equal (fn-lc-take 5 out) (fn-lc-take 5 (fn-lc-cold-pgs-choice disk r mode)))
       (equal (fn-lc-at 5 out)
        (fn-lc-join
         (list (list :pread :root 0 (fn-lc-root-slot-octets))
               (list :pread :root 1 (fn-lc-root-slot-octets)))
         (fn-lc-cold-page-program (fn-lc-cold-directory-path disk r mode))))
       (fn-lc-cold-only-metadata-requests-p
         (fn-lc-join (fn-lc-at 5 out) (fn-lc-cold-page-program (list 2)))
         (fn-lc-cold-directory-path disk r mode))))
 ((disk (fn-lc-at 0 (lco-id5-input 1))) (r :lc) (mode :eager))
 :fault "selector validates column page 2; clause (c) alone must reject it")
 (drops-rejected-metadata (:conclusion (and (equal (fn-lc-take 5 out) (fn-lc-take 5 (fn-lc-cold-pgs-choice disk r mode)))
       (equal (remove-equal (list :pread :page 99 (fn-lc-page-octets)) (fn-lc-at 5 out))
        (fn-lc-join
         (list (list :pread :root 0 (fn-lc-root-slot-octets))
               (list :pread :root 1 (fn-lc-root-slot-octets)))
         (fn-lc-cold-page-program (fn-lc-cold-directory-path disk r mode))))
       (fn-lc-cold-only-metadata-requests-p
         (fn-lc-at 5 out) (fn-lc-cold-directory-path disk r mode))))
 ((disk (lcc-fallback-disk)) (r :lc) (mode :eager))
 :fault "selector hides rejected directory page 99; clause (b) alone must reject it"))))
(defteeth-check (fn-lc-cold-selection-is-metadata-only))
