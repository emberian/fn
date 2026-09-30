; PRF-1142 / SCN-1048. Actual maintenance ledger authority for a private
; checkpoint's census-derived backing. Initial allocation/runtime adequacy
; remains the separate constructor boundary: this book never invents credit.
(in-package "ACL2")
(include-book "snapshot-job-capture")
(include-book "page-maintenance-lease")

; The producer supplies its actual ten-field request. Identity includes
; source pass as well as ordinal, stage incarnation and full maintenance token.
(defun fn-osj-growth-requestp (request source stage maintenance)
  (declare (xargs :guard t))
  (and (consp request) (fn-omk-widthp request 10)
       (equal (fn-omk-at 0 request) :checkpoint-growth)
       (fn-omk-tokenp source)
       (equal (fn-omk-at 1 request) source)
       (natp stage) (equal (fn-omk-at 2 request) stage)
       (equal stage (fn-omk-at 1 maintenance))
       (equal (fn-omk-at 3 request) maintenance)
       (equal (fn-omk-at 0 source) (fn-omk-at 2 maintenance))
       (fn-omk-widthp maintenance 4)
       (equal (fn-omk-at 0 maintenance) :maintenance)
       (natp (fn-omk-at 1 maintenance))
       (natp (fn-omk-at 2 maintenance))
       (natp (fn-omk-at 3 maintenance))
       (natp (fn-omk-at 4 request))
       (natp (fn-omk-at 5 request))
       (posp (fn-omk-at 6 request))
       (natp (fn-omk-at 7 request))
       (equal (fn-omk-at 7 request)
              (+ 16384 (* 16384 (+ 1 (fn-omk-at 6 request)
                                     (fn-omk-at 4 request)
                                     (fn-omk-at 5 request)))))
       (equal (fn-omk-at 8 request) (* 32 (fn-omk-at 4 request)))
       (equal (fn-omk-at 9 request) (* 32 (fn-omk-at 5 request)))))

(defun fn-osj-growth-disk (request)
  (declare (xargs :guard t))
  (+ (nfix (fn-omk-at 7 request)) (nfix (fn-omk-at 8 request))
     (nfix (fn-omk-at 9 request))))

(defun fn-osj-grant-livep (grant ledger)
  (declare (xargs :guard t))
  (let* ((maintenance (fn-omk-at 3 grant))
         (entry (fn-prl-binding maintenance (fn-prl-nth 3 ledger)))
         (row (if (consp entry) (cdr entry) nil))
         (demand (fn-prl-nth 0 row)))
    (and (consp grant) (fn-omk-widthp grant 10)
         (equal (fn-omk-at 0 grant) :checkpoint-funded)
         (fn-osj-growth-requestp
          (cons :checkpoint-growth (cdr grant))
          (fn-omk-at 1 grant) (fn-omk-at 2 grant) maintenance)
         (equal (fn-prl-nth 1 row) :maintenance)
         (equal (fn-prl-nth 2 row) grant)
         (fn-prs-vectorp demand)
         (<= (fn-osj-growth-disk grant) (nfix (fn-prl-nth 1 demand)))
         ; Three private descriptors were reserved at initial admission.
         (<= 3 (nfix (fn-prl-nth 2 demand)))
         (equal (fn-prl-nth 3 demand) 1)
         (equal (fn-prl-nth 4 demand) 1))))

(defun fn-osj-keep-grant (ledger maintenance grant)
  ; Successful fn-pmn-grow has just prepended this exact maintenance row.
  ; Bind its receipt by replacing that first cell, without another lookup.
  (declare (xargs :guard t))
  (let* ((bindings (fn-prl-nth 3 ledger))
         (entry (if (consp bindings) (car bindings) nil))
         (row (if (consp entry) (cdr entry) nil)))
    (fn-prl-build (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger)
                  (fn-prl-nth 2 ledger)
                  (cons (cons maintenance
                              (fn-pmn-row (fn-prl-nth 0 row) grant
                                          (fn-prl-nth 3 row)))
                        (if (consp bindings) (cdr bindings) nil))
                  (fn-prl-nth 4 ledger))))

(defun fn-osj-grow (ledger maintenance source stage request)
  (declare (xargs :guard t))
  (let* ((entry (fn-prl-binding maintenance (fn-prl-nth 3 ledger)))
         (row (if (consp entry) (cdr entry) nil))
         (demand (fn-prl-nth 0 row)))
    (cond
     ((not (fn-osj-growth-requestp request source stage maintenance))
      (mv '(:refused :checkpoint-growth-request) ledger))
     ((not (and (equal (fn-prl-nth 1 row) :maintenance)
                 (fn-prs-vectorp demand)
                 (<= 3 (nfix (fn-prl-nth 2 demand)))
                 (equal (fn-prl-nth 3 demand) 1)
                 (equal (fn-prl-nth 4 demand) 1)))
      (mv '(:refused :checkpoint-maintenance) ledger))
     (t
      (let ((delta (list 0 (nfix (- (fn-osj-growth-disk request)
                                   (nfix (fn-prl-nth 1 demand)))) 0 0 0)))
        (mv-let (word next) (fn-pmn-grow ledger maintenance delta)
          (if (not (equal word :grown)) (mv (list :refused word) ledger)
            (let ((grant (cons :checkpoint-funded (if (consp request) (cdr request) nil))))
              (mv grant (fn-osj-keep-grant next maintenance grant))))))))))

(defthm fn-osj-grown-authority-matches-exact-request
  (implies (equal (car (mv-nth 0
                        (fn-osj-grow ledger maintenance source stage request)))
                  :checkpoint-funded)
           (and (fn-osj-growth-requestp request source stage maintenance)
                (equal (mv-nth 0
                        (fn-osj-grow ledger maintenance source stage request))
                       (cons :checkpoint-funded (cdr request)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osj-grow))))

(defthm fn-osj-grown-authority-preserves-pool-funding
  (implies (equal (car (mv-nth 0
                        (fn-osj-grow ledger maintenance source stage request)))
                  :checkpoint-funded)
           (fn-prs-fundedp
            (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
            (fn-prl-nth 1 (mv-nth 1
                           (fn-osj-grow ledger maintenance source stage request)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osj-grow fn-osj-keep-grant fn-prl-build fn-prl-nth)
           :use ((:instance fn-pmn-grown-pool-funded-by-definition
                            (token maintenance)
                            (delta (list 0
                              (nfix (- (fn-osj-growth-disk request)
                                       (nfix (fn-prl-nth 1
                                          (fn-prl-nth 0
                                           (cdr (fn-prl-binding maintenance
                                                (fn-prl-nth 3 ledger))))))))
                              0 0 0)))))))

(local
 (defthm fn-osj-nth-natural
  (implies (and (fn-prs-nats-p xs) (natp k) (< k (len xs)))
           (natp (fn-prl-nth k xs)))
  :hints (("Goal" :induct (fn-prl-nth k xs)
           :in-theory (enable fn-prl-nth fn-prs-nats-p)))))

(local
 (defun fn-osj-plus-induct (k a b)
  (if (or (zp k) (atom a)) (list a b)
    (fn-osj-plus-induct (1- k) (cdr a) (if (consp b) (cdr b) nil)))))

(local
 (defthm fn-osj-nth-plus
  (implies (and (natp k) (< k (len a)))
           (equal (fn-prl-nth k (fn-prs-plus a b))
                  (+ (nfix (fn-prl-nth k a)) (nfix (fn-prl-nth k b)))))
  :hints (("Goal" :induct (fn-osj-plus-induct k a b)
           :in-theory (enable fn-prl-nth fn-prs-plus)))))

(local
 (defthm fn-osj-vector-fields
  (implies (fn-prs-vectorp xs)
   (and (equal (len xs) 5)
        (natp (fn-prl-nth 0 xs)) (natp (fn-prl-nth 1 xs))
        (natp (fn-prl-nth 2 xs)) (natp (fn-prl-nth 3 xs))
        (natp (fn-prl-nth 4 xs))))
  :hints (("Goal" :in-theory (enable fn-prs-vectorp)))))

(defthm fn-osj-grown-authority-is-live
  (implies (equal (car (mv-nth 0
                        (fn-osj-grow ledger maintenance source stage request)))
                  :checkpoint-funded)
           (fn-osj-grant-livep
            (mv-nth 0 (fn-osj-grow ledger maintenance source stage request))
            (mv-nth 1 (fn-osj-grow ledger maintenance source stage request))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-osj-vector-fields
                    (xs (fn-prl-nth 0
                         (cdr (fn-prl-binding maintenance
                                              (fn-prl-nth 3 ledger)))))))
           :in-theory
           (enable fn-osj-grow fn-osj-grant-livep fn-pmn-grow fn-prl-nth
                   fn-prl-build fn-prl-binding fn-osj-keep-grant fn-pmn-row
                   fn-osj-growth-disk fn-osj-growth-requestp
                   fn-omk-at fn-omk-widthp fn-omk-tokenp))))

(defthm fn-osj-growth-preserves-initial-custody
  (equal
   (fn-prl-nth 3
    (cdr (fn-prl-binding
          maintenance (fn-prl-nth 3
                       (mv-nth 1 (fn-osj-grow ledger maintenance source stage request))))))
   (fn-prl-nth 3 (cdr (fn-prl-binding maintenance (fn-prl-nth 3 ledger)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-osj-grow fn-osj-keep-grant fn-pmn-grow fn-pmn-row
                 fn-prl-build fn-prl-binding fn-prl-nth)
                (fn-osj-growth-requestp fn-osj-growth-disk fn-prs-fundedp
                 fn-prs-plus fn-prs-vectorp)))))

(in-theory (disable fn-osj-growth-requestp fn-osj-growth-disk
                    fn-osj-grant-livep fn-osj-keep-grant fn-osj-grow))
