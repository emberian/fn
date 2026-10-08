; Five final-placement page cursors. Validate every target before the row
; writes anything: refusal is named and leaves the entire store unchanged.
(in-package "ACL2")
(include-book "history-pages-relocate")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-his-rcp (rc)
 (declare (xargs :guard t))
 (and (true-listp rc) (equal (len rc) 3)
      (natp (car rc)) (natp (cadr rc)) (< (cadr rc) 2048)
      (true-listp (caddr rc)) (equal (len (caddr rc)) (cadr rc))))

(defun fn-his-rc-fitp (n rc start nw nd)
 (declare (xargs :guard (natp n)))
 (and (fn-his-rcp rc) (natp start) (natp nw) (natp nd)
      (<= (+ (* 2048 (+ start (car rc))) (cadr rc) n) nw)
      (<= (+ (* 2048 (+ start (car rc))) (cadr rc) n) (* 2048 nd))))

(defthm fn-his-word-end-implies-dirty-bound
  (implies (and (natp j) (posp n) (natp nd) (<= (+ j n) (* 2048 nd)))
           (< (floor (+ j n -1) 2048) nd))
  :hints (("Goal" :in-theory (enable floor)))
  :rule-classes :linear)

(defthm fn-his-u64-listp-revappend
  (implies (and (fn-hp-u64-listp x) (fn-hp-u64-listp y))
           (fn-hp-u64-listp (revappend x y))))

(defthm fn-his-u64-listp-reverse
  (implies (fn-hp-u64-listp x) (fn-hp-u64-listp (reverse x)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm fn-his-u64-listp-append
  (implies (and (fn-hp-u64-listp x) (fn-hp-u64-listp y))
           (fn-hp-u64-listp (append x y))))

(defthm fn-his-u64-listp-rev
  (implies (fn-hp-u64-listp x) (fn-hp-u64-listp (rev x)))
  :hints (("Goal" :induct (rev x) :in-theory (enable rev))))

(local
 (defthm fn-his-positive-len-when-consp
  (implies (consp x) (< 0 (len x)))
  :hints (("Goal" :expand ((len x))))
  :rule-classes :linear))

(defun fn-his-rc-write (ws rc start pgs-mem)
 (declare (xargs :stobjs pgs-mem
                 :guard (and (fn-hp-u64-listp ws)
                             (fn-his-rc-fitp (len ws) rc start
                                            (pgs-w-length pgs-mem) (pgs-d-length pgs-mem))
                             (fn-hp-u64-listp (caddr rc)))
                 :guard-hints (("Goal" :in-theory
                                (e/d (fn-his-rc-fitp fn-his-rcp len)
                                     (fn-hp-x-put floor))))))
 (if (atom ws) (mv rc pgs-mem)
   (let ((page (car rc)) (cnt (+ 1 (cadr rc))) (rev (cons (car ws) (caddr rc))))
     (if (equal cnt 2048)
         (let ((pgs-mem (fn-hp-x-put (* 2048 (+ start page)) (reverse rev) pgs-mem)))
           (fn-his-rc-write (cdr ws) (list (+ 1 page) 0 nil) start pgs-mem))
       (fn-his-rc-write (cdr ws) (list page cnt rev) start pgs-mem)))))

(defthm fn-his-rc-write-keeps-lengths
 (implies (fn-his-rc-fitp (len ws) rc start (pgs-w-length pgs-mem) (pgs-d-length pgs-mem))
          (let ((m (mv-nth 1 (fn-his-rc-write ws rc start pgs-mem))))
            (and (equal (pgs-w-length m) (pgs-w-length pgs-mem))
                 (equal (pgs-d-length m) (pgs-d-length pgs-mem)))))
 :hints (("Goal" :induct (fn-his-rc-write ws rc start pgs-mem)
          :in-theory (e/d (fn-his-rc-fitp fn-his-rcp len) (fn-hp-x-put floor)))))

(defun fn-his-rc-put (ws rc start pgs-mem)
 (declare (xargs :stobjs pgs-mem :guard (fn-hp-u64-listp ws)))
 (if (not (and (fn-his-rc-fitp (len ws) rc start (pgs-w-length pgs-mem) (pgs-d-length pgs-mem))
               (fn-hp-u64-listp (caddr rc))))
     (mv '(:refused :placement) rc pgs-mem)
   (mv-let (rc pgs-mem) (fn-his-rc-write ws rc start pgs-mem)
     (mv nil rc pgs-mem))))

(defthm fn-his-rc-put-keeps-w-length
 (equal (pgs-w-length (mv-nth 2 (fn-his-rc-put ws rc start pgs-mem)))
        (pgs-w-length pgs-mem))
 :hints (("Goal" :in-theory (e/d (fn-his-rc-put) (fn-his-rc-write fn-his-rc-fitp)))))

(defthm fn-his-rc-put-refuses-placement-unchanged
 (implies (mv-nth 0 (fn-his-rc-put ws rc start pgs-mem))
          (and (equal (mv-nth 0 (fn-his-rc-put ws rc start pgs-mem)) '(:refused :placement))
               (equal (mv-nth 1 (fn-his-rc-put ws rc start pgs-mem)) rc)
               (equal (mv-nth 2 (fn-his-rc-put ws rc start pgs-mem)) pgs-mem)))
 :hints (("Goal" :in-theory (e/d (fn-his-rc-put) (fn-his-rc-write fn-his-rc-fitp)))))

(defun fn-his-cellsp (cells)
 (declare (xargs :guard t))
 (if (atom cells) (null cells)
   (and (fn-hp-u64-listp (car cells)) (fn-his-cellsp (cdr cells)))))

(defun fn-his-rcs-fitp (cells rcs starts nw nd)
 (declare (xargs :guard t))
 (if (atom cells) (and (null cells) (null rcs) (null starts))
   (and (consp rcs) (consp starts)
        (fn-his-rc-fitp (len (car cells)) (car rcs) (car starts) nw nd)
        (fn-hp-u64-listp (caddr (car rcs)))
        (fn-his-rcs-fitp (cdr cells) (cdr rcs) (cdr starts) nw nd))))

(defun fn-his-rcs-write (cells rcs starts pgs-mem)
 (declare (xargs :stobjs pgs-mem
                 :guard (and (fn-his-cellsp cells)
                             (fn-his-rcs-fitp cells rcs starts
                                             (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
                 :guard-hints (("Goal" :in-theory (disable fn-his-rc-write)))))
 (if (atom cells) (mv rcs pgs-mem)
   (mv-let (rc pgs-mem) (fn-his-rc-write (car cells) (car rcs) (car starts) pgs-mem)
     (mv-let (rest pgs-mem) (fn-his-rcs-write (cdr cells) (cdr rcs) (cdr starts) pgs-mem)
       (mv (cons rc rest) pgs-mem)))))

(defthm fn-his-rcs-write-keeps-lengths
 (implies (fn-his-rcs-fitp cells rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem))
          (let ((m (mv-nth 1 (fn-his-rcs-write cells rcs starts pgs-mem))))
            (and (equal (pgs-w-length m) (pgs-w-length pgs-mem))
                 (equal (pgs-d-length m) (pgs-d-length pgs-mem)))))
 :hints (("Goal" :induct (fn-his-rcs-write cells rcs starts pgs-mem)
          :in-theory (disable fn-his-rc-write fn-his-rc-fitp))))

(defun fn-his-rcs-put (cells rcs starts pgs-mem)
 (declare (xargs :stobjs pgs-mem :guard (fn-his-cellsp cells)))
 (if (not (fn-his-rcs-fitp cells rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
     (mv '(:refused :placement) rcs pgs-mem)
   (mv-let (rcs pgs-mem) (fn-his-rcs-write cells rcs starts pgs-mem)
     (mv nil rcs pgs-mem))))

(defthm fn-his-rcs-put-keeps-w-length
 (equal (pgs-w-length (mv-nth 2 (fn-his-rcs-put cells rcs starts pgs-mem)))
        (pgs-w-length pgs-mem))
 :hints (("Goal" :in-theory (e/d (fn-his-rcs-put)
                                (fn-his-rcs-write fn-his-rcs-fitp)))))

(defthm fn-his-rcs-put-refuses-placement-unchanged
 (implies (mv-nth 0 (fn-his-rcs-put cells rcs starts pgs-mem))
          (and (equal (mv-nth 0 (fn-his-rcs-put cells rcs starts pgs-mem)) '(:refused :placement))
               (equal (mv-nth 1 (fn-his-rcs-put cells rcs starts pgs-mem)) rcs)
               (equal (mv-nth 2 (fn-his-rcs-put cells rcs starts pgs-mem)) pgs-mem)))
 :hints (("Goal" :in-theory (e/d (fn-his-rcs-put)
                                (fn-his-rcs-write fn-his-rcs-fitp)))))

(defun fn-his-rcs-flush-fitp (rcs starts nw nd)
 (declare (xargs :guard t))
 (if (atom rcs) (and (null rcs) (null starts))
   (and (consp starts)
        (fn-his-rc-fitp 0 (car rcs) (car starts) nw nd)
        (fn-hp-u64-listp (caddr (car rcs)))
        (fn-his-rcs-flush-fitp (cdr rcs) (cdr starts) nw nd))))

(defun fn-his-rcs-flush-write (rcs starts pgs-mem)
 (declare (xargs :stobjs pgs-mem
                 :guard (fn-his-rcs-flush-fitp rcs starts
                                              (pgs-w-length pgs-mem) (pgs-d-length pgs-mem))
                 :guard-hints (("Goal" :in-theory
                                (e/d (fn-his-rc-fitp fn-his-rcp len)
                                     (fn-hp-x-put floor))))))
 (if (atom rcs) pgs-mem
   (let ((pgs-mem (if (equal (cadr (car rcs)) 0) pgs-mem
                    (fn-hp-x-put (* 2048 (+ (car starts) (car (car rcs))))
                                 (reverse (caddr (car rcs))) pgs-mem))))
     (fn-his-rcs-flush-write (cdr rcs) (cdr starts) pgs-mem))))

(defthm fn-his-rcs-flush-write-keeps-lengths
 (implies (fn-his-rcs-flush-fitp rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem))
          (let ((m (fn-his-rcs-flush-write rcs starts pgs-mem)))
            (and (equal (pgs-w-length m) (pgs-w-length pgs-mem))
                 (equal (pgs-d-length m) (pgs-d-length pgs-mem)))))
 :hints (("Goal" :induct (fn-his-rcs-flush-write rcs starts pgs-mem)
          :in-theory (e/d (fn-his-rc-fitp fn-his-rcp len) (fn-hp-x-put floor)))))

(defun fn-his-rcs-flush (rcs starts pgs-mem)
 (declare (xargs :stobjs pgs-mem :guard t))
 (if (not (fn-his-rcs-flush-fitp rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
     (mv '(:refused :placement) pgs-mem)
   (let ((pgs-mem (fn-his-rcs-flush-write rcs starts pgs-mem)))
     (mv :ok pgs-mem))))

(defthm fn-his-rcs-flush-refuses-placement-unchanged
 (implies (not (equal (mv-nth 0 (fn-his-rcs-flush rcs starts pgs-mem)) :ok))
          (and (equal (mv-nth 0 (fn-his-rcs-flush rcs starts pgs-mem)) '(:refused :placement))
               (equal (mv-nth 1 (fn-his-rcs-flush rcs starts pgs-mem)) pgs-mem)))
 :hints (("Goal" :in-theory (e/d (fn-his-rcs-flush)
                                (fn-his-rcs-flush-write fn-his-rcs-flush-fitp)))))
