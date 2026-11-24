; Ledger initialization empties every FIFO independently of the old rows.
(in-package "ACL2")
(include-book "account-fifo")

; The dimension writers leave both link columns unchanged throughout their
; recursive traversals. Compare the columns directly, at any row count.
(defmacro fn2-account-init-keeps-links (call &key induction)
  `(defthm ,(fn2-columns-sym (car call) "-KEEPS-FIFO-LINKS")
     (implies (or (equal k *fn2-accounts-wait-head$ai*) (equal k *fn2-accounts-wait-tail$ai*))
              (equal (nth k ,call) (nth k fn2-accounts)))
     :hints (("Goal" ,@(and induction (list :induct call))
              :in-theory (enable ,(car call))))))

(fn2-account-init-keeps-links (fn2-account-set-dims row d limits reserves fn2-accounts) :induction t)
(fn2-account-init-keeps-links (fn2-account-configure entries p fn2-accounts) :induction t)
(fn2-account-init-keeps-links (fn2-account-set-capacities d profile fn2-accounts) :induction t)
(fn2-account-init-keeps-links (fn2-account-set-committed d fn2-accounts) :induction t)
(fn2-account-init-keeps-links (fn2-account-default-rows row fn2-accounts))

(defun fn2-account-index-countdown (i n)
  (declare (xargs :guard (and (natp i) (natp n)) :measure (nfix i)))
  (if (or (zp i) (zp n)) 0 (fn2-account-index-countdown (- i 1) (- n 1))))
(defthm fn2-account-read-initial-column
  (implies (and (natp i) (< i (nfix n)))
           (equal (nth i (resize-list nil n v)) v))
  :hints (("Goal" :induct (fn2-account-index-countdown i n)
           :expand ((resize-list nil n v))
           :in-theory (union-theories '(fn2-account-index-countdown nth zp nfix natp) (theory 'ground-zero)))))

(defthm fn2-account-initial-ends
  (let ((new (fn2-accounts-init profile fn2-accounts)))
    (implies (and (natp i) (< i (fn2-accounts-rows new)))
             (and (equal (fn2-accounts-wait-head i new) *fn2-none*)
                  (equal (fn2-accounts-wait-tail i new) *fn2-none*))))
  :hints (("Goal" :in-theory (e/d (fn2-accounts-init fn2-accounts-alloc fn2-accounts-rows
                                   fn2-accounts-wait-head fn2-accounts-wait-tail)
                                  (fn2-accounts-columns-init fn2-account-set-dims fn2-account-configure
                                   fn2-account-set-capacities fn2-account-set-committed fn2-account-default-rows)))))
(defthm fn2-account-initial-fifos-empty
  (let ((new (fn2-accounts-init profile fn2-accounts)))
    (implies (and (natp rows) (<= rows (fn2-accounts-rows new)))
             (equal (fn2-account-fifos-visit rows seen new fn2-machines) seen)))
  :hints (("Goal" :induct (fn2-account-index-countdown rows rows)
           :in-theory (e/d (fn2-account-fifos-visit fn2-account-fifo-visit)
                           (fn2-accounts-init fn2-accounts-rows fn2-accounts-wait-head fn2-accounts-wait-tail)))))
