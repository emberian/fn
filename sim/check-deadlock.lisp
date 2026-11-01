; Finite PV geometry: forbidden OPEN rectangles, then boundary deadlocks.
; Test/model logic, not a served path or a reachability/scheduling classifier.
(in-package "ACL2")
(include-book "../books/declare")
(fn2-book-layer :b)

(defun fn2-pv-capsp (caps)
 (declare (xargs :verify-guards nil))
 (if (atom caps) (null caps)
  (and (consp (car caps)) (keywordp (caar caps)) (natp (cdar caps))
       (not (assoc-eq (caar caps) (cdr caps))) (fn2-pv-capsp (cdr caps)))))
(defun fn2-pv-retention-valid (retained caps)
 (declare (xargs :verify-guards nil))
 (if (atom retained) (null retained)
  (and (assoc-eq (caar retained) caps) (fn2-pv-retention-valid (cdr retained) caps))))
(defun fn2-pv-final-holds (caps holds retained)
 (declare (xargs :verify-guards nil))
 (if (atom caps) t
  (and (= (len (cdr (assoc-eq (caar caps) holds))) (nfix (cdr (assoc-eq (caar caps) retained))))
       (fn2-pv-final-holds (cdr caps) holds retained))))
(defun fn2-pv-close-units (resource starts thread end)
 (declare (xargs :verify-guards nil))
 (if (atom starts) nil
  (cons (list resource thread (car starts) end) (fn2-pv-close-units resource (cdr starts) thread end))))
(defun fn2-pv-close-held (holds thread end)
 (declare (xargs :verify-guards nil))
 (if (atom holds) nil
  (append (fn2-pv-close-units (caar holds) (cdar holds) thread end)
          (fn2-pv-close-held (cdr holds) thread end))))
; An interval is (resource thread acquire release). Repeated acquisitions
; consume distinct units; pairing releases LIFO preserves the holding count.
(defun fn2-pv-resource (interval) (car interval))
(defun fn2-pv-thread (interval) (cadr interval))
(defun fn2-pv-acquire (interval) (caddr interval))
(defun fn2-pv-release (interval) (cadddr interval))
(defun fn2-pv-word (word caps thread position holds retained)
 (declare (xargs :verify-guards nil))
 (if (atom word)
     (mv (and (null word) (fn2-pv-final-holds caps holds retained))
         (fn2-pv-close-held holds thread (+ 1 (nfix position))))
  (let* ((op (car word)) (r (cadr op)) (starts (cdr (assoc-eq r holds))))
   (if (not (and (true-listp op) (= (len op) 2) (assoc-eq r caps)
                 (or (eq (car op) :p) (and (eq (car op) :v) (consp starts)))))
       (mv nil nil)
    (mv-let (ok intervals)
     (fn2-pv-word (cdr word) caps thread (+ 1 (nfix position))
      (put-assoc-eq r (if (eq (car op) :p) (cons position starts) (cdr starts)) holds) retained)
     (mv ok (if (eq (car op) :p) intervals
              (cons (list r thread (car starts) position) intervals))))))))
(defun fn2-pv-collect (threads caps index retained)
 (declare (xargs :verify-guards nil))
 (if (atom threads) (mv (null threads) nil nil)
  (mv-let (ok intervals) (fn2-pv-word (car threads) caps index 1 nil (car retained))
   (mv-let (rest-ok rest terminals) (fn2-pv-collect (cdr threads) caps (+ 1 (nfix index)) (cdr retained))
    (mv (and ok rest-ok (fn2-pv-capsp (car retained)) (fn2-pv-retention-valid (car retained) caps)) (append intervals rest)
        (cons (+ 1 (len (car threads))) terminals))))))
(defun fn2-pv-peak (word resource held peak)
 (declare (xargs :verify-guards nil))
 (if (atom word) peak
  (let ((next (if (eq (cadar word) resource)
                  (+ held (if (eq (caar word) :p) 1 -1)) held)))
   (fn2-pv-peak (cdr word) resource next (max peak next)))))
(defun fn2-pv-demand (threads resource)
 (declare (xargs :verify-guards nil))
 (if (atom threads) 0
  (+ (fn2-pv-peak (car threads) resource 0 0) (fn2-pv-demand (cdr threads) resource))))
(defun fn2-pv-select (resource intervals)
 (declare (xargs :verify-guards nil))
 (if (atom intervals) nil
  (if (eq resource (fn2-pv-resource (car intervals)))
      (cons (car intervals) (fn2-pv-select resource (cdr intervals)))
    (fn2-pv-select resource (cdr intervals)))))
; Unconstrained axes extend beyond [0,terminal], so endpoints are interior.
(defun fn2-pv-domain (terminals)
 (declare (xargs :verify-guards nil))
 (if (atom terminals) nil
  (cons (cons -1 (+ 1 (nfix (car terminals)))) (fn2-pv-domain (cdr terminals)))))
(defun fn2-pv-tighten (rectangle axis lower upper)
 (declare (xargs :verify-guards nil))
 (if (atom rectangle) nil
  (if (zp axis)
      (let ((lo (max lower (caar rectangle))) (hi (min upper (cdar rectangle))))
       (and (< lo hi) (cons (cons lo hi) (cdr rectangle))))
    (let ((tail (fn2-pv-tighten (cdr rectangle) (- axis 1) lower upper)))
     (and tail (cons (car rectangle) tail))))))
(defun fn2-pv-combinations (intervals need rectangle)
 (declare (xargs :verify-guards nil))
 (cond ((zp need) (list rectangle)) ((atom intervals) nil)
  (t (let ((next (fn2-pv-tighten rectangle (fn2-pv-thread (car intervals))
                  (fn2-pv-acquire (car intervals)) (fn2-pv-release (car intervals)))))
      (append (and next (fn2-pv-combinations (cdr intervals) (- need 1) next))
              (fn2-pv-combinations (cdr intervals) need rectangle))))))
(defun fn2-pv-regions (caps threads intervals domain)
 (declare (xargs :verify-guards nil))
 (if (atom caps) nil
  (append (and (> (fn2-pv-demand threads (caar caps)) (cdar caps))
               (fn2-pv-combinations (fn2-pv-select (caar caps) intervals) (+ 1 (cdar caps)) domain))
          (fn2-pv-regions (cdr caps) threads intervals domain))))
(defun fn2-pv-inside (point rectangle)
 (declare (xargs :verify-guards nil))
 (if (atom point) t
  (and (< (caar rectangle) (car point)) (< (car point) (cdar rectangle))
       (fn2-pv-inside (cdr point) (cdr rectangle)))))
(defun fn2-pv-forbidden (point rectangles)
 (declare (xargs :verify-guards nil))
 (if (atom rectangles) nil
  (or (fn2-pv-inside point (car rectangles)) (fn2-pv-forbidden point (cdr rectangles)))))
; Direction j is blocked exactly at a lower face with all OTHER coordinates
; strictly interior. A lower corner shared by two faces does not block either.
(defun fn2-pv-face (point rectangle axis)
 (declare (xargs :verify-guards nil))
 (if (atom point) nil
  (if (zp axis)
      (and (= (car point) (caar rectangle)) (fn2-pv-inside (cdr point) (cdr rectangle)))
    (and (< (caar rectangle) (car point)) (< (car point) (cdar rectangle))
         (fn2-pv-face (cdr point) (cdr rectangle) (- axis 1))))))
(defun fn2-pv-blocked (point rectangles axis)
 (declare (xargs :verify-guards nil))
 (if (atom rectangles) nil
  (or (fn2-pv-face point (car rectangles) axis) (fn2-pv-blocked point (cdr rectangles) axis))))
(defun fn2-pv-all-blocked (tail terminals point rectangles axis)
 (declare (xargs :verify-guards nil))
 (if (atom tail) t
  (and (or (= (car tail) (car terminals)) (fn2-pv-blocked point rectangles axis))
       (fn2-pv-all-blocked (cdr tail) (cdr terminals) point rectangles (+ 1 (nfix axis))))))
(defun fn2-pv-lowers (rectangles axis terminal)
 (declare (xargs :verify-guards nil))
 (if (atom rectangles) nil
  (let ((lo (car (nth axis (car rectangles)))))
   (if (and (natp lo) (< lo terminal))
       (add-to-set-equal lo (fn2-pv-lowers (cdr rectangles) axis terminal))
     (fn2-pv-lowers (cdr rectangles) axis terminal)))))
(defun fn2-pv-choices (terminals rectangles axis)
 (declare (xargs :verify-guards nil))
 (if (atom terminals) nil
  (cons (cons (car terminals) (fn2-pv-lowers rectangles axis (car terminals)))
        (fn2-pv-choices (cdr terminals) rectangles (+ 1 (nfix axis))))))
(defun fn2-pv-products (choices)
 (declare (xargs :verify-guards nil))
 (if (atom choices) 1 (* (len (car choices)) (fn2-pv-products (cdr choices)))))
; Iterate the Cartesian product without materializing all candidate points.
(defun fn2-pv-search (choices remaining prefix terminals rectangles)
 (declare (xargs :verify-guards nil :measure (make-ord 1 (+ 1 (acl2-count choices)) (acl2-count remaining))))
 (cond ((atom choices)
        (let ((point (reverse prefix)))
         (and (not (equal point terminals)) (not (fn2-pv-forbidden point rectangles))
              (fn2-pv-all-blocked point terminals point rectangles 0) (list point))))
       ((atom remaining) nil)
       (t (append (fn2-pv-search (cdr choices) (cadr choices) (cons (car remaining) prefix) terminals rectangles)
                  (fn2-pv-search choices (cdr remaining) prefix terminals rectangles)))))
; Retention is explicit ownership after terminal, never an invented release.
(defun fn2-pv-check-retained (threads capacities retained)
 (declare (xargs :verify-guards nil))
 (mv-let (ok intervals terminals) (fn2-pv-collect threads capacities 0 retained)
  (if (not (and (fn2-pv-capsp capacities) (true-listp retained) (= (len threads) (len retained)) ok))
      (list (cons :status :invalid-pv-program) (cons :threads (len threads)))
   (let* ((regions (remove-duplicates-equal (fn2-pv-regions capacities threads intervals (fn2-pv-domain terminals))))
          (choices (fn2-pv-choices terminals regions 0))
          (witnesses (fn2-pv-search choices (car choices) nil terminals regions)))
    (list (cons :status :ok) (cons :threads (len threads)) (cons :intervals (len intervals))
          (cons :rectangles (len regions)) (cons :candidates (fn2-pv-products choices))
          (cons :deadlocks (len witnesses)) (cons :witnesses witnesses) (cons :regions regions))))))

(defun fn2-pv-check (threads capacities)
 (declare (xargs :verify-guards nil))
 (fn2-pv-check-retained threads capacities (make-list (len threads) :initial-element nil)))

(assert-event
 (equal (cdr (assoc-eq :witnesses (fn2-pv-check
  '(((:p :a) (:p :b) (:v :b) (:v :a)) ((:p :b) (:p :a) (:v :a) (:v :b))) '((:a . 1) (:b . 1)))))
  '((2 2))))
(assert-event
 (equal (cdr (assoc-eq :deadlocks (fn2-pv-check
  '(((:p :a) (:v :a)) ((:p :a) (:v :a))) '((:a . 1))))) 0))
(assert-event
 (equal (cdr (assoc-eq :witnesses (fn2-pv-check
  '(((:p :batch) (:p :send) (:v :send) (:v :batch))
    ((:p :batch) (:p :send) (:v :send) (:v :batch))
    ((:p :send) (:p :batch) (:v :batch) (:v :send)) ()) '((:batch . 2) (:send . 1)))))
  '((2 2 2 1))))
(assert-event (equal (cdr (assoc-eq :status (fn2-pv-check '(((:p :a))) '((:a . 1))))) :invalid-pv-program))

(assert-event
 (equal (cdr (assoc-eq :witnesses (fn2-pv-check-retained
  '(((:p :a)) ((:p :a) (:v :a))) '((:a . 1)) '(((:a . 1)) nil)))) '((2 1))))
(assert-event
 (equal (cdr (assoc-eq :status (fn2-pv-check-retained
  '(((:p :a))) '((:a . 1)) '(((:a . 2)))))) :invalid-pv-program))
