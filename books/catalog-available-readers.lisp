; Actual metadata readers for Option 2' command enumeration.
; Raw retrieval/overview ranges remain a separate retained-identity API.
(in-package "ACL2")
(include-book "served-catalog-view")
(include-book "nntp-projection")

(defun fn-scat-available-numbers-loop (group low high v acc fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (natp low) (natp high) (natp v) (true-listp acc))
                  :measure (nfix (- (+ 1 high) low))))
  (if (and (natp low) (natp high) (<= low high))
      (fn-scat-available-numbers-loop group (+ 1 low) high v
        (if (fn-scv-keptp group low v fn-cat) (cons low acc) acc) fn-cat)
    (revappend acc nil)))

(defun fn-scat-available-numbers (group low high v fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil
                  :guard (and (natp low) (natp high) (natp v))
                  :measure (nfix (- (+ 1 high) low))))
  (mbe :logic
       (if (and (natp low) (natp high) (<= low high))
           (if (fn-scv-keptp group low v fn-cat)
               (cons low (fn-scat-available-numbers group (+ 1 low) high v fn-cat))
             (fn-scat-available-numbers group (+ 1 low) high v fn-cat))
         nil)
       :exec (fn-scat-available-numbers-loop group low high v nil fn-cat)))

(local (defthm fn-scat-available-numbers-loop-is-revappend
  (equal (fn-scat-available-numbers-loop group low high v acc fn-cat)
         (revappend acc (fn-scat-available-numbers group low high v fn-cat)))
  :hints (("Goal" :induct (fn-scat-available-numbers-loop group low high v acc fn-cat)
           :in-theory (disable fn-scv-keptp)))))

(verify-guards fn-scat-available-numbers
  :hints (("Goal" :use ((:instance fn-scat-available-numbers-loop-is-revappend
                                  (acc nil))))))

(defun fn-scat-available-range-numbers (group low high v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp low) (natp high) (natp v))))
  (fn-scat-available-numbers group low
    (min high (nfix (- (fn-cat-group-next group fn-cat) 1))) v fn-cat))

(defun fn-scat-available-summary (archive group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((s (if (and (equal v (fn-cat-count fn-cat))
                    (<= (fn-cat-horizon fn-cat) v))
               (list (fn-cat-group-live-count group fn-cat)
                     (fn-cat-group-live-low group fn-cat)
                     (fn-cat-group-live-high group fn-cat))
             (fn-scv-summary group v fn-cat))))
    (if (posp (car s)) s
      (let ((next (fn-next-number group (fn-state-nexts archive))))
        (list 0 next (if (posp next) (- next 1) 0))))))

(defun fn-scat-available-low (group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (if (and (equal v (fn-cat-count fn-cat))
           (<= (fn-cat-horizon fn-cat) v))
      (fn-cat-group-live-low group fn-cat)
    (cadr (fn-scv-summary group v fn-cat))))

(defun fn-scat-available-next-number (group current v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp current) (natp v))))
  (fn-scv-first-p group (+ 1 current)
    (nfix (- (fn-cat-group-next group fn-cat) 1)) v fn-cat))

(defun fn-scat-available-previous-number (group current v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp current) (natp v))))
  (if (posp current)
      (fn-scv-last-p group (min (- current 1)
         (nfix (- (fn-cat-group-next group fn-cat) 1))) v fn-cat)
    0))

(defthm fn-scat-available-numbers-count
  (implies (and (natp low) (natp high))
           (equal (len (fn-scat-available-numbers group low high v fn-cat))
                  (fn-scv-count-p group low high v fn-cat)))
  :hints (("Goal" :induct (fn-scat-available-numbers group low high v fn-cat)
           :in-theory (e/d (fn-scv-count-p) (fn-scv-keptp)))))

(defthm fn-scat-available-numbers-first
  (implies (and (natp low) (natp high))
           (equal (fn-scv-first-p group low high v fn-cat)
                  (let ((numbers (fn-scat-available-numbers group low high v fn-cat)))
                    (if (consp numbers) (car numbers) 0))))
  :hints (("Goal" :induct (fn-scat-available-numbers group low high v fn-cat)
           :in-theory (e/d (fn-scv-first-p) (fn-scv-keptp)))))

(defun fn-scat-available-last (numbers)
  (declare (xargs :guard t))
  (if (consp numbers)
      (if (consp (cdr numbers)) (fn-scat-available-last (cdr numbers)) (car numbers))
    0))

(local (defthm fn-scat-available-numbers-empty
  (implies (< high low)
           (equal (fn-scat-available-numbers group low high v fn-cat) nil))))

(local (defthm fn-scat-available-numbers-snoc
  (implies (and (natp low) (natp high) (<= low high))
           (equal (fn-scat-available-numbers group low high v fn-cat)
                  (append (fn-scat-available-numbers group low (- high 1) v fn-cat)
                    (if (fn-scv-keptp group high v fn-cat) (list high) nil))))
  :hints (("Goal" :induct (fn-scat-available-numbers group low high v fn-cat)
           :in-theory (disable fn-scv-keptp)
           :expand ((fn-scat-available-numbers group low high v fn-cat)
                    (fn-scat-available-numbers group low (- high 1) v fn-cat))))))

(local (defthm fn-scat-available-last-append
  (equal (fn-scat-available-last (append a b))
         (if (consp b) (fn-scat-available-last b) (fn-scat-available-last a)))))

(defthm fn-scat-available-numbers-last
  (implies (natp high)
           (equal (fn-scv-last-p group high v fn-cat)
                  (fn-scat-available-last
                    (fn-scat-available-numbers group 1 high v fn-cat))))
  :hints (("Goal" :induct (fn-scv-last-p group high v fn-cat)
           :in-theory (e/d (fn-scv-last-p)
                           (fn-scv-keptp fn-scat-available-numbers)))
          ("Subgoal *1/2" :use ((:instance fn-scat-available-numbers-snoc (low 1))))
          ("Subgoal *1/1" :use ((:instance fn-scat-available-numbers-snoc (low 1))))))

(in-theory (disable fn-scat-available-numbers fn-scat-available-range-numbers
                    fn-scat-available-summary fn-scat-available-low
                    fn-scat-available-next-number fn-scat-available-previous-number))
