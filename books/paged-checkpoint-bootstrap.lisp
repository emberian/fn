; Paged checkpoint's own first publication. No history-image initializer.
(in-package "ACL2")
(include-book "pagestore-refine")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-pck-bootstrap-plan (dirty)
  ; Logical model only: first allocation over empty tables, no prior root.
  (declare (xargs :guard (alistp dirty) :verify-guards nil))
  (let ((lp (pgs-dirty-lpages dirty)))
    (if (not (pgs-lpages-ok lp 0 0))
        (list :refused :dirty-out-of-order)
      (let* ((tl (pgs-touched lp nil))
             (al (pgs-alloc (+ (len dirty) (len tl))
                            (pgs-dir-run-pages (pgs-grown-len lp 0)) '(nil 1)))
             (fresh (take (len dirty) (second al)))
             (tfresh (nthcdr (len dirty) (second al)))
             (tab (pgs-plan-ptab nil lp fresh (pgs-dirty-digests dirty) 1))
             (td (pgs-table-dirty tl (pgs-chunk tab)))
             (dir (pgs-plan-ptab nil tl tfresh (pgs-dirty-digests td) 1)))
        (list :plan
              (append (pgs-page-writes dirty fresh) (pgs-page-writes td tfresh)
                      (list (cons (first al) dir)))
              0 (pgs-make-rec 1 (first al) (len tab) (pgs-digest dir))
              (list (third al) (fourth al)))))))

(defun fn-pck-x-bootstrap-reset (pgs-mem)
  ; Data pages were staged by PCK; reset only the absent store's metadata.
  (declare (xargs :stobjs pgs-mem :guard t))
  (let* ((pgs-mem (pgs-x-reset-table 0 pgs-mem))
         (pgs-mem (pgs-x-resize 1 0 pgs-mem)))
    (pgs-x-resize 1 3072 pgs-mem)))

(defun fn-pck-x-bootstrap (lpages pgs-mem fn-octets-pg)
  (declare (xargs :stobjs (pgs-mem fn-octets-pg) :guard (nat-listp lpages)))
  (let ((pgs-mem (fn-pck-x-bootstrap-reset pgs-mem)))
    (pgs-x-commit lpages 0 1 '(nil 1) 0 pgs-mem fn-octets-pg)))

(defthm pckb-reset-invariants
  (let ((m (fn-pck-x-bootstrap-reset pgs-mem)))
    (and (pgs-x-tab-inv 0 m)
         (pgs-x-dir-inv 1024 0 m)
         (equal (pgs-m-length m) 3072)
         (implies (pgs-memp pgs-mem) (pgs-memp m))))
  :hints (("Goal" :in-theory (e/d (fn-pck-x-bootstrap-reset pgs-x-tab-inv
                                   pgs-x-dir-inv pgs-x-reset-table)
                                  (pgs-x-resize pgs-x-zero-range resize-pgs-tv))
           :use ((:instance pgs-x-zero-range-of-fresh-resize (s 1) (lo 1024) (hi 3072) (n 3072)
                            (pgs-mem (pgs-x-reset-table 0 pgs-mem)))))))

(defthm pckb-reset-keeps-data
  (equal (pgs-x-words 0 a k (fn-pck-x-bootstrap-reset pgs-mem))
         (pgs-x-words 0 a k pgs-mem))
  :hints (("Goal" :induct (pgs-x-words 0 a k pgs-mem)
           :in-theory (enable fn-pck-x-bootstrap-reset pgs-x-reset-table
                              pgs-x-word pgs-x-words))))

(defun pckb-seed (r)
  ; Proof witness only. Never written, installed, or passed by the host.
  ; Its directory is the empty lookup at reserved address zero.
  (cons nil (list (cons r (cons nil (pgs-make-rec 0 0 0 (pgs-digest nil)))))))

(defthm pckb-seed-open
  (equal (pgs-open (pckb-seed r) r mode) (list :ok 1 0 nil nil))
  :hints (("Goal" :in-theory (enable pckb-seed pgs-open pgs-open-slots
                 pgs-open-order pgs-try-in-order pgs-slot-refusals pgs-try
                 pgs-dir-verdict pgs-rec-valid pgs-rec-ok pgs-rec-shape-p
                 pgs-make-rec pgs-rec-body pgs-rec-dir-addr pgs-rec-npages
                 pgs-rec-dir-digest pgs-rec-txid pgs-lookup pgs-ptab-p
                 pgs-ptab-txids-ok pgs-contents pgs-flatten pgs-entries-good))))

(defthm pckb-seed-allocator
  (pgs-alloc-inv '(nil 1) (pckb-seed r))
  :hints (("Goal" :in-theory (enable pckb-seed pgs-alloc-inv pgs-disk-keeps
                  pgs-roots-keeps pgs-slots-keeps pgs-rec-keeps-in pgs-rec-keeps
                  pgs-rec-dir-addr pgs-rec-npages pgs-rec-dir-digest
                  pgs-rec-txid pgs-lookup pgs-contents pgs-make-rec))))

(defthm pckb-plan-is-seed-plan
  (equal (fn-pck-bootstrap-plan dirty)
         (pgs-plan-commit (pckb-seed r) r mode dirty '(nil 1)))
  :rule-classes nil
  :hints (("Goal" :use pckb-seed-open
           :in-theory (e/d (fn-pck-bootstrap-plan pgs-plan-commit pckb-seed
                                   pgs-next-txid pgs-next-txid-of pgs-rec-valid pgs-rec-ok
                                   pgs-rec-shape-p pgs-rec-body pgs-rec-dir-addr pgs-rec-npages
                                   pgs-rec-dir-digest pgs-rec-txid pgs-lookup pgs-contents
                                   pgs-flatten pgs-make-rec)
                                  (pgs-open pgs-alloc pgs-plan-ptab pgs-table-dirty
                                   pgs-dirty-digests pgs-page-writes)))))

(defthm pckb-seed-facts
  (and (equal (pgs-pages (pckb-seed r)) nil)
       (equal (pgs-c-cur (pckb-seed r) r mode) (pgs-make-rec 0 0 0 (pgs-digest nil)))
       (equal (pgs-c-k0 (pckb-seed r) r mode) 1)
       (equal (pgs-c-txid (pckb-seed r) r) 1)
       (equal (pgs-c-lpages-ok (pckb-seed r) r mode dirty)
              (pgs-lpages-ok (pgs-dirty-lpages dirty) 0 0))
       (equal (pgs-contents (pgs-sp (pgs-c-cur (pckb-seed r) r mode) nil) nil) nil))
  :hints (("Goal" :use pckb-seed-open
           :in-theory (e/d (pckb-seed pgs-c-cur pgs-c-k0 pgs-c-txid
                  pgs-c-lpages-ok pgs-sp pgs-sd pgs-make-rec
                  pgs-next-txid pgs-next-txid-of pgs-rec-valid pgs-rec-ok
                  pgs-rec-shape-p pgs-rec-body pgs-rec-dir-addr pgs-rec-npages
                  pgs-rec-dir-digest pgs-rec-txid pgs-lookup pgs-contents pgs-flatten)
                  (pgs-open pgs-lpages-ok)))))

(defthm pckb-plan-parts
  (implies (pgs-lpages-ok (pgs-dirty-lpages dirty) 0 0)
           (and (equal (car (fn-pck-bootstrap-plan dirty)) :plan)
                (equal (second (fn-pck-bootstrap-plan dirty))
                       (pgs-c-writes (pckb-seed r) r mode dirty '(nil 1)))
                (equal (third (fn-pck-bootstrap-plan dirty)) 0)
                (equal (fourth (fn-pck-bootstrap-plan dirty))
                       (pgs-c-rec (pckb-seed r) r mode dirty '(nil 1)))))
  :hints (("Goal" :do-not-induct t
           :use (pckb-plan-is-seed-plan pckb-seed-open pckb-seed-facts
                 (:instance pgs-plan-commit-unfold (disk (pckb-seed r)) (alloc '(nil 1))))
           :in-theory (union-theories '(true-listp car-cons cdr-cons)
                                      (theory 'minimal-theory)))))

(defthm pckb-new-try
  (let ((p (fn-pck-bootstrap-plan dirty)))
    (implies (and (pgs-lpages-ok (pgs-dirty-lpages dirty) 0 0)
                  (pgs-writes-faithful (second p) nil)
                  (equal (car (pgs-try (fourth p) (pgs-apply-pages (second p) keep nil) mode)) :ok))
             (equal (pgs-try (fourth p) (pgs-apply-pages (second p) keep nil) mode)
                    (list :ok 1 (pgs-apply-dirty nil dirty)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance pgs-c-step-hyps (disk (pckb-seed :pck)) (r :pck) (alloc '(nil 1)))
                 (:instance pgs-step-try-crash
                            (cur (pgs-c-cur (pckb-seed :pck) :pck mode)) (pages nil)
                            (fresh (pgs-c-fresh (pckb-seed :pck) :pck mode dirty '(nil 1)))
                            (tfresh (pgs-c-tfresh (pckb-seed :pck) :pck mode dirty '(nil 1)))
                            (rs (pgs-c-rs (pckb-seed :pck) :pck mode dirty '(nil 1)))
                            (txid 1))
                 (:instance pckb-seed-open (r :pck))
                 (:instance pckb-seed-allocator (r :pck))
                 (:instance pckb-seed-facts (r :pck))
                 (:instance pckb-plan-parts (r :pck)))
           :in-theory (union-theories '(pgs-c-writes pgs-c-rec)
                                      (theory 'minimal-theory)))))

(defthm pckb-single-view
  (equal (pgs-view (pgs-open (cons pages (list (cons r (cons sv nil)))) r mode))
         (if (and (pgs-rec-valid sv) (equal (car (pgs-try sv pages mode)) :ok))
             (list (second (pgs-try sv pages mode)) (third (pgs-try sv pages mode)))
           nil))
  :rule-classes nil
  :hints (("Goal" :use (:instance pgs-rec-valid-shape (x sv))
           :in-theory (union-theories '(pgs-open pgs-open-slots pgs-open-order
                  pgs-try-in-order pgs-slot-refusals pgs-slot pgs-root-slots
                  pgs-roots pgs-pages pgs-view hons-assoc-equal hons-equal true-listp
                  pgs-rec-valid-of-nil car-cons cdr-cons binary-append)
                  (theory 'minimal-theory)))))

(defthm fn-pck-bootstrap-crash-opens-new-or-refuses
  (let* ((p (fn-pck-bootstrap-plan dirty))
         (o (pgs-open (pgs-crash nil r (second p) keep 0 sv) r mode)))
    (implies (and (pgs-lpages-ok (pgs-dirty-lpages dirty) 0 0)
                  (pgs-writes-faithful (second p) nil)
                  (or (equal sv (fourth p)) (not (pgs-rec-valid sv))))
             (or (equal (pgs-view o) nil)
                 (equal (pgs-view o) (list 1 (pgs-apply-dirty nil dirty))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (pckb-new-try
                 (:instance pckb-single-view
                   (pages (pgs-apply-pages (second (fn-pck-bootstrap-plan dirty)) keep nil))))
           :in-theory (union-theories '(pgs-crash pgs-set-root-slot pgs-set-slot pgs-slot
                  pgs-root-slots pgs-roots pgs-pages hons-assoc-equal hons-equal car-cons cdr-cons)
                  (theory 'minimal-theory)))))

(defthm pckb-reset-abs-dirty
  (equal (pgs-x-abs-dirty lpages (fn-pck-x-bootstrap-reset pgs-mem))
         (pgs-x-abs-dirty lpages pgs-mem))
  :hints (("Goal" :induct (pgs-x-abs-dirty lpages pgs-mem)
           :in-theory (e/d (pgs-x-abs-dirty) (fn-pck-x-bootstrap-reset pgs-x-words)))))

(defthm fn-pck-x-bootstrap-is-the-plan
  ; The digest observations are exactly the existing A-PGS-OBSERVE boundary.
  ; Empty table/directory invariants are established, not caller hypotheses.
  (let* ((m0 (fn-pck-x-bootstrap-reset pgs-mem))
         (r (fn-pck-x-bootstrap lpages pgs-mem fn-octets-pg))
         (res (mv-nth 0 r)) (m2 (mv-nth 1 r))
         (dirty (pgs-x-abs-dirty lpages pgs-mem)))
    (implies (and (pgs-memp pgs-mem) (nat-listp lpages)
                  (equal (car res) :plan)
                  (equal (mv-nth 0 (pgs-x-dirty-digests lpages m0 fn-octets-pg))
                         (pgs-dirty-digests dirty))
                  (equal (nth 9 res)
                         (pgs-dirty-digests
                          (pgs-table-dirty (pgs-touched lpages nil)
                                          (pgs-chunk (pgs-x-tab (pgs-grown-len lpages 0) m2)))))
                  (pgs-rec-valid (nth 1 res))
                  (equal (pgs-rec-dir-digest (nth 1 res))
                         (pgs-digest (pgs-x-dir (pgs-ntables (pgs-grown-len lpages 0)) m2))))
             (equal (list :plan (pgs-x-abs-writes lpages res m2) 0 (nth 1 res) (nth 7 res))
                    (fn-pck-bootstrap-plan dirty))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance pgs-x-commit-glue
                    (sp nil) (sd nil)
                    (dirty (pgs-x-abs-dirty lpages pgs-mem))
                    (al (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil)))
                                   (pgs-dir-run-pages (pgs-grown-len lpages 0)) '(nil 1)))
                    (tx 1) (txid 1) (n 0) (slot 0) (alloc '(nil 1))
                    (pgs-mem (fn-pck-x-bootstrap-reset pgs-mem)))
                 (:instance pgs-x-commit-lpages-ok
                    (txid 1) (n 0) (slot 0) (alloc '(nil 1))
                    (pgs-mem (fn-pck-x-bootstrap-reset pgs-mem)))
                 (:instance pgs-x-alloc-parts
                    (k (+ (len lpages) (len (pgs-touched lpages nil))))
                    (m (pgs-dir-run-pages (pgs-grown-len lpages 0))) (alloc '(nil 1))))
           :in-theory (union-theories '(fn-pck-x-bootstrap fn-pck-bootstrap-plan
                   pckb-reset-invariants pckb-reset-abs-dirty
                   pgs-x-cres pgs-x-cmem pgs-x-tab pgs-x-dir pgs-x-tab-from
                   pgs-x-dirty-lpages-of-abs-dirty pgs-x-dir-run-pages-posp
                   pgs-nat-listp-of-touched pgs-alloc-free natp nat-listp
                   true-list-fix (:executable-counterpart true-list-fix)
                   (:executable-counterpart nat-listp)
                   (:executable-counterpart zp) (:executable-counterpart binary-+)
                   (:executable-counterpart nfix) (:executable-counterpart unary--)
                   (:type-prescription len) (:executable-counterpart pgs-ntables))
                   (theory 'minimal-theory)))))

(defthm pckb-new-complete
  (let ((p (fn-pck-bootstrap-plan dirty)))
    (implies (pgs-lpages-ok (pgs-dirty-lpages dirty) 0 0)
             (and (pgs-rec-valid (fourth p))
                  (equal (pgs-try (fourth p) (pgs-apply-pages (second p) nil nil) mode)
                         (list :ok 1 (pgs-apply-dirty nil dirty))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance pgs-c-step-hyps (disk (pckb-seed :pck)) (r :pck) (alloc '(nil 1)))
                 (:instance pgs-step-try-new
                            (cur (pgs-c-cur (pckb-seed :pck) :pck mode)) (pages nil)
                            (fresh (pgs-c-fresh (pckb-seed :pck) :pck mode dirty '(nil 1)))
                            (tfresh (pgs-c-tfresh (pckb-seed :pck) :pck mode dirty '(nil 1)))
                            (rs (pgs-c-rs (pckb-seed :pck) :pck mode dirty '(nil 1))) (txid 1))
                 (:instance pgs-s-facts
                            (cur (pgs-c-cur (pckb-seed :pck) :pck mode)) (pages nil)
                            (fresh (pgs-c-fresh (pckb-seed :pck) :pck mode dirty '(nil 1)))
                            (tfresh (pgs-c-tfresh (pckb-seed :pck) :pck mode dirty '(nil 1)))
                            (rs (pgs-c-rs (pckb-seed :pck) :pck mode dirty '(nil 1))) (txid 1))
                 (:instance pckb-seed-open (r :pck))
                 (:instance pckb-seed-allocator (r :pck))
                 (:instance pckb-seed-facts (r :pck))
                 (:instance pckb-plan-parts (r :pck)))
           :in-theory (union-theories '(pgs-c-writes pgs-c-rec pgs-srec
                         pgs-make-rec-fields natp (:type-prescription len))
                                      (theory 'minimal-theory)))))

(defthm fn-pck-bootstrap-opens-the-pages
  (let ((p (fn-pck-bootstrap-plan dirty)))
    (implies (pgs-lpages-ok (pgs-dirty-lpages dirty) 0 0)
             (equal (pgs-view (pgs-open (pgs-crash nil r (second p) nil 0 (fourth p)) r mode))
                    (list 1 (pgs-apply-dirty nil dirty)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (pckb-new-complete
                 (:instance pckb-single-view (sv (fourth (fn-pck-bootstrap-plan dirty)))
                    (pages (pgs-apply-pages (second (fn-pck-bootstrap-plan dirty)) nil nil))))
           :in-theory (union-theories '(pgs-crash pgs-set-root-slot pgs-set-slot pgs-slot
                  pgs-root-slots pgs-roots pgs-pages hons-assoc-equal hons-equal car-cons cdr-cons)
                  (theory 'minimal-theory)))))
