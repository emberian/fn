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

; The summary of GROUP's numbers served at view V: the catalog's carried live
; count/low/high corrected over the rows appended or withdrawn since V
; (fn-scv-summary; empty correction at the live view, so O(1) there).
; fn-scat-available-summary-is-the-walk below states it equals the walk over
; the group's numbers.
(defun fn-scat-available-summary (archive group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((s (fn-scv-summary group v fn-cat)))
    (if (posp (car s)) s
      (let ((next (fn-next-number group (fn-state-nexts archive))))
        (list 0 next (if (posp next) (- next 1) 0))))))

(defun fn-scat-available-low (group v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (cadr (fn-scv-summary group v fn-cat)))

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

; -----------------------------------------------------------------------------
; The carried summary is the walk.  fn-scat-available-summary reads the
; catalog's carried live count/low/high (corrected over the rows appended or
; withdrawn since the view) in one call; the walk it replaces probed every
; number 1 .. NEXT-1 of the group (the LIST cursor's former summary phase,
; fn-lst-probe-summary).  The two agree whenever the group's high is below
; the allocation watermark NEXT: no number above the high is served.

(local
 (defthm fn-sar-assoc-of-numbersp
   (implies (fn-held-numbersp ns)
            (or (null (cdr (fn-cat-assoc g ns)))
                (posp (cdr (fn-cat-assoc g ns)))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-held-numbersp)))))

(local
 (defthm fn-sar-assoc-rewrite
   (implies (and (fn-held-numbersp ns) (cdr (fn-cat-assoc g ns)))
            (and (integerp (cdr (fn-cat-assoc g ns)))
                 (< 0 (cdr (fn-cat-assoc g ns)))))
   :hints (("Goal" :use fn-sar-assoc-of-numbersp))))

; A number above the group's high names no row.
(local
 (defthm fn-sar-number-seq-above-high
   (implies (and (fn-cat-rowsp c) (rationalp n) (< (fn-cat-group-high g c) n))
            (equal (fn-cat-number-seq g n c i) nil))))

(defthm fn-scat-keptp-above-high
  (implies (and (fn-cat-p fn-cat) (natp k) (< (fn-cat-group-high group fn-cat) k))
           (not (fn-scv-keptp group k v fn-cat)))
  :hints (("Goal" :in-theory (enable fn-scv-keptp fn-cat-group-number-is-number-seq))))

(local
 (defun fn-sar-down (n h)
   (declare (xargs :measure (nfix (- (nfix n) (nfix h)))))
   (if (and (natp n) (natp h) (< h n)) (fn-sar-down (- n 1) h) n)))

(defthm fn-scat-available-numbers-above-high
  (implies (and (fn-cat-p fn-cat) (natp n) (natp h)
                (equal h (fn-cat-group-high group fn-cat)) (<= h n))
           (equal (fn-scat-available-numbers group 1 n v fn-cat)
                  (fn-scat-available-numbers group 1 h v fn-cat)))
  :hints (("Goal" :induct (fn-sar-down n h)
           :in-theory (disable fn-scv-keptp fn-scat-available-numbers))
          ("Subgoal *1/2" :use ((:instance fn-scat-available-numbers-snoc (low 1) (high n))
                                (:instance fn-scat-keptp-above-high (k n))))))

(local
 (defthm fn-sar-summary-count
   (implies (fn-cat-p fn-cat)
            (equal (car (fn-scv-summary group v fn-cat))
                   (len (fn-scat-available-numbers group 1 (fn-cat-group-high group fn-cat) v fn-cat))))
   :hints (("Goal" :in-theory (disable fn-scv-summary fn-scat-available-numbers fn-scv-count-p)
            :use (fn-scv-count-is-count-p
                  (:instance fn-scat-available-numbers-count (low 1)
                             (high (fn-cat-group-high group fn-cat))))))))

(local
 (defthm fn-sar-summary-first
   (implies (fn-cat-p fn-cat)
            (equal (cadr (fn-scv-summary group v fn-cat))
                   (let ((numbers (fn-scat-available-numbers group 1 (fn-cat-group-high group fn-cat) v fn-cat)))
                     (if (consp numbers) (car numbers) 0))))
   :hints (("Goal" :in-theory (disable fn-scv-summary fn-scat-available-numbers fn-scv-first-p)
            :use (fn-scv-first-is-first-p
                  (:instance fn-scat-available-numbers-first (low 1)
                             (high (fn-cat-group-high group fn-cat))))))))

(local
 (defthm fn-sar-summary-last
   (implies (fn-cat-p fn-cat)
            (equal (caddr (fn-scv-summary group v fn-cat))
                   (fn-scat-available-last
                    (fn-scat-available-numbers group 1 (fn-cat-group-high group fn-cat) v fn-cat))))
   :hints (("Goal" :in-theory (disable fn-scv-summary fn-scat-available-numbers fn-scv-last-p
                                       fn-scat-available-last)
            :use (fn-scv-last-is-last-p
                  (:instance fn-scat-available-numbers-last (high (fn-cat-group-high group fn-cat))))))))

(local
 (defthm fn-sar-summary-shape
   (and (true-listp (fn-scv-summary group v fn-cat))
        (equal (len (fn-scv-summary group v fn-cat)) 3))
   :hints (("Goal" :in-theory (enable fn-scv-summary)))))

(local
 (defthm fn-sar-list3
   (implies (and (true-listp x) (equal (len x) 3))
            (equal x (list (car x) (cadr x) (caddr x))))
   :rule-classes nil))

(local (defthm fn-sar-len-of-consp (implies (consp x) (< 0 (len x))) :rule-classes :linear))

(local
 (defthm fn-sar-walk-core
   (implies (and (fn-cat-p fn-cat) (natp n) (<= (fn-cat-group-high group fn-cat) n))
            (equal (let ((s (fn-scv-summary group v fn-cat))) (if (posp (car s)) s (list 0 z w)))
                   (let ((numbers (fn-scat-available-numbers group 1 n v fn-cat)))
                     (if (consp numbers)
                         (list (len numbers) (car numbers) (fn-scat-available-last numbers))
                       (list 0 z w)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-scv-summary fn-scat-available-numbers fn-scat-available-last
                                fn-scat-available-numbers-count fn-scat-available-numbers-first
                                fn-scat-available-numbers-last fn-sar-summary-count
                                fn-sar-summary-first fn-sar-summary-last fn-sar-summary-shape
                                fn-scat-available-numbers-above-high)
            :use ((:instance fn-scat-available-numbers-above-high
                             (h (fn-cat-group-high group fn-cat)))
                  fn-sar-summary-count fn-sar-summary-first fn-sar-summary-last
                  fn-sar-summary-shape
                  (:instance fn-sar-list3 (x (fn-scv-summary group v fn-cat))))))))

(local
 (defthm fn-sar-summary-unfold
   (equal (fn-scat-available-summary archive group v fn-cat)
          (let ((s (fn-scv-summary group v fn-cat)))
            (if (posp (car s)) s
              (list 0 (fn-next-number group (fn-state-nexts archive))
                    (if (posp (fn-next-number group (fn-state-nexts archive)))
                        (- (fn-next-number group (fn-state-nexts archive)) 1)
                      0)))))
   :hints (("Goal" :in-theory (enable fn-scat-available-summary)))))

(local
 (defthm fn-sar-walk-gen
   (implies (and (fn-cat-p fn-cat) (natp next)
                 (<= (fn-cat-group-high group fn-cat) (if (posp next) (- next 1) 0)))
            (equal (let ((s (fn-scv-summary group v fn-cat)))
                     (if (posp (car s)) s (list 0 next (if (posp next) (- next 1) 0))))
                   (let* ((high (if (posp next) (- next 1) 0))
                          (numbers (fn-scat-available-numbers group 1 high v fn-cat)))
                     (if (consp numbers)
                         (list (len numbers) (car numbers) (fn-scat-available-last numbers))
                       (list 0 next high)))))
   :hints (("Goal" :do-not-induct t :cases ((posp next))
            :in-theory (disable fn-scv-summary fn-scat-available-numbers fn-scat-available-last
                                fn-scat-available-numbers-count fn-scat-available-numbers-first
                                fn-scat-available-numbers-last fn-sar-summary-unfold)
            :use ((:instance fn-sar-walk-core (n (if (posp next) (- next 1) 0)) (z next)
                             (w (if (posp next) (- next 1) 0)))))
           ("Subgoal 2" :use ((:instance fn-sar-walk-core (n 0) (z next) (w 0))))
           ("Subgoal 1" :use ((:instance fn-sar-walk-core (n (- next 1)) (z next)
                                         (w (- next 1))))))))

; KEYSTONE: the carried summary is the walk over the group's numbers.
(defthm fn-scat-available-summary-is-the-walk
  (let ((next (fn-next-number group (fn-state-nexts archive))))
    (implies (and (fn-cat-p fn-cat) (natp next)
                  (<= (fn-cat-group-high group fn-cat) (if (posp next) (- next 1) 0)))
             (equal (fn-scat-available-summary archive group v fn-cat)
                    (let* ((high (if (posp next) (- next 1) 0))
                           (numbers (fn-scat-available-numbers group 1 high v fn-cat)))
                      (if (consp numbers)
                          (list (len numbers) (car numbers) (fn-scat-available-last numbers))
                        (list 0 next high))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use (fn-sar-summary-unfold
                 (:instance fn-sar-walk-gen
                            (next (fn-next-number group (fn-state-nexts archive))))))))
