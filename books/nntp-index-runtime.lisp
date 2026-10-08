; Runtime NNTP number projection over materialized membership entries.
; Kept below books/nntp.lisp so the served pinned dispatcher can use it.
(in-package "ACL2")
(include-book "nntp-projection")
(include-book "def-loop")
(include-book "index")

(defun fn-nntp-index-msgid-okp (text)
  (declare (xargs :guard t :verify-guards nil))
  (and (stringp text)
       (<= (length text) *fn-nntp-max-message-id-octets*)
       (fn-nntp-message-id-tokenp (fn-nntp-string-octets text))))

(defun fn-nntp-index-entry-available (entry)
  (declare (xargs :guard t :verify-guards nil))
  (let ((number (fn-index-entry-number entry)))
    (if (and (posp number)
             (<= number *fn-nntp-max-article-number*)
             (fn-nntp-index-msgid-okp (fn-index-entry-msgid entry)))
        number
      0)))

(verify-guards fn-nntp-index-msgid-okp)

(verify-guards fn-nntp-index-entry-available)

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(def-loop fn-nntp-index-numbers (entries)
  :shape :step :done (atom entries) :emit (posp number)
  :let ((number (fn-nntp-index-entry-available (fn-ag-car entries)))) :body number
  :next (fn-ag-cdr entries) :skip-next (fn-ag-cdr entries))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(def-loop fn-nntp-numbers-count (numbers)
  :shape :foldr :over numbers :elt n
  :combine (+ 1 acc) :init 0
  :rev fn-ag-rev-onto
  :loop-guard (natp acc))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(def-loop fn-nntp-numbers-min (numbers)
  :shape :foldr :over numbers :elt n
  :combine (let ((number n))
                (if (and (posp number) (or (not (posp acc)) (< number acc))) number acc))
  :init 0
  :rev fn-ag-rev-onto
  :loop-guard (rationalp acc))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(def-loop fn-nntp-numbers-max (numbers)
  :shape :foldr :over numbers :elt n
  :combine (let ((number n)) (if (and (posp number) (< acc number)) number acc)) :init 0
  :rev fn-ag-rev-onto
  :loop-guard (rationalp acc))

(defthm fn-nntp-numbers-max-natp
  (natp (fn-nntp-numbers-max numbers))
  :rule-classes (:type-prescription :rewrite))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(def-loop fn-nntp-numbers-min-above (current numbers)
  :shape :foldr :over numbers :elt n
  :combine (let ((number n))
                (if (and (posp number)
                         (fn-ag-less current number)
                         (or (not (posp acc)) (< number acc)))
                    number
                    acc))
  :init 0
  :rev fn-ag-rev-onto
  :loop-guard (rationalp acc))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(def-loop fn-nntp-numbers-max-below (current numbers)
  :shape :foldr :over numbers :elt n
  :combine (let ((number n))
                (if (and (posp number) (fn-ag-less number current) (< acc number)) number acc))
  :init 0
  :rev fn-ag-rev-onto
  :loop-guard (rationalp acc))

(defthm fn-nntp-numbers-max-below-natp
  (natp (fn-nntp-numbers-max-below current numbers))
  :rule-classes (:type-prescription :rewrite))

;; A group's bucket lists its entries newest first, so the numbers of a range
;; arrive strictly descending and the insertion sort was quadratic (OVER 1-2000
;; inserted each number at the end of the sorted rest: lane served-readers'
;; profile, 2026-09-27).  A strictly descending list sorts to its reverse
;; (fn-nntp-numbers-sort-of-descending); any other order takes the insertion.
(defun fn-nntp-descending-integersp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (integerp (car xs))
           (or (not (consp (cdr xs)))
               (and (integerp (car (cdr xs)))
                    (< (car (cdr xs)) (car xs))))
           (fn-nntp-descending-integersp (cdr xs)))
    t))

; Any other order inserts from the right by a loop over the reversed list
; (PKT-877, lane serve-depth): the recursion took one control-stack frame per
; number, so OVER or LISTGROUP of a whole large group stopped the owner.
(defun fn-nntp-numbers-sort-loop (rev acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rev)
      (fn-nntp-numbers-sort-loop (cdr rev) (fn-nntp-insert-number (car rev) acc))
    acc))

(defun fn-nntp-numbers-sort (numbers)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp numbers)
                  (fn-nntp-insert-number (fn-ag-car numbers)
                                         (fn-nntp-numbers-sort (fn-ag-cdr numbers)))
                nil)
       :exec (if (fn-nntp-descending-integersp numbers)
                 (fn-ng-revappend numbers nil)
               (fn-nntp-numbers-sort-loop (fn-ag-rev-onto numbers nil) nil))))

(local
 (defthm fn-nntp-numbers-sort-loop-of-rev-onto
   (equal (fn-nntp-numbers-sort-loop (fn-ag-rev-onto numbers zs) nil)
          (fn-nntp-numbers-sort-loop zs (fn-nntp-numbers-sort numbers)))
   :hints (("Goal" :induct (fn-ag-rev-onto numbers zs)
                   :in-theory (union-theories '(fn-nntp-numbers-sort-loop fn-nntp-numbers-sort
                                                fn-ag-rev-onto fn-ag-car fn-ag-cdr
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(local (defun fn-nntp-all-below (xs n)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs) (and (< (car xs) n) (fn-nntp-all-below (cdr xs) n)) t)))
(local (defthm fn-nntp-insert-number-above-all
  (implies (fn-nntp-all-below ys n)
           (equal (fn-nntp-insert-number n ys) (append ys (list n))))
  :hints (("Goal" :in-theory (enable fn-nntp-insert-number)))))
(local (defthm fn-nntp-all-below-append
  (equal (fn-nntp-all-below (append a b) n)
         (and (fn-nntp-all-below a n) (fn-nntp-all-below b n)))))
(local (defthm fn-nntp-all-below-revappend
  (equal (fn-nntp-all-below (revappend xs acc) n)
         (and (fn-nntp-all-below xs n) (fn-nntp-all-below acc n)))
  :hints (("Goal" :induct (revappend xs acc)))))
(local (defthm fn-nntp-all-below-reverse
  (implies (true-listp xs)
           (equal (fn-nntp-all-below (reverse xs) n) (fn-nntp-all-below xs n)))
  :hints (("Goal" :in-theory (enable reverse revappend)))))
(local (defthm fn-nntp-descending-all-below
  (implies (and (fn-nntp-descending-integersp (cons x xs)))
           (fn-nntp-all-below xs x))
  :hints (("Goal" :induct (fn-nntp-descending-integersp xs)))))
(local (defthm fn-nntp-revappend-of-append
  (equal (revappend xs (append a b)) (append (revappend xs a) b))
  :hints (("Goal" :induct (revappend xs a)))))
(local (defthm fn-nntp-revappend-cons-nil
  (implies (consp xs)
           (equal (revappend xs nil)
                  (append (revappend (cdr xs) nil) (list (car xs)))))
  :hints (("Goal" :expand ((revappend xs nil))
           :in-theory (disable fn-nntp-revappend-of-append)
           :use ((:instance fn-nntp-revappend-of-append
                            (xs (cdr xs)) (a nil) (b (list (car xs)))))))))
(local (defthm fn-nntp-revappend-of-atom
  (implies (not (consp xs)) (equal (revappend xs acc) acc))
  :hints (("Goal" :expand ((revappend xs acc))))))
(local (defthm fn-nntp-descending-all-below-cdr
  (implies (and (consp numbers) (fn-nntp-descending-integersp numbers))
           (fn-nntp-all-below (cdr numbers) (car numbers)))
  :hints (("Goal" :use ((:instance fn-nntp-descending-all-below
                                   (x (car numbers)) (xs (cdr numbers))))))))
(local (in-theory (disable revappend)))
(local (defthm fn-nntp-all-below-insert
  (equal (fn-nntp-all-below (fn-nntp-insert-number x ys) n)
         (and (< x n) (fn-nntp-all-below ys n)))
  :hints (("Goal" :in-theory (enable fn-nntp-insert-number)))))
(local (defthm fn-nntp-all-below-sort
  (implies (fn-nntp-all-below xs n)
           (fn-nntp-all-below (fn-nntp-numbers-sort xs) n))
  :hints (("Goal" :in-theory (enable fn-nntp-numbers-sort)))))
(defthm fn-nntp-numbers-sort-of-descending
  (implies (fn-nntp-descending-integersp numbers)
           (equal (fn-nntp-numbers-sort numbers) (revappend numbers nil)))
  :hints (("Goal" :induct (fn-nntp-numbers-sort numbers)
           :in-theory (enable fn-nntp-numbers-sort))))

(defconst *fn-nntp-index-all-low* 1)

(defconst *fn-nntp-index-all-high* 2147483647)

(defun fn-nntp-index-group-numbers (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-index-numbers
   (fn-index-query-range index group
                         *fn-nntp-index-all-low* *fn-nntp-index-all-high*)))

(defun fn-nntp-index-group-count (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-count (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-low (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-min (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-high (index group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-max (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-next-number (index group current)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-min-above current (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-last-number (index group current)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-max-below current (fn-nntp-index-group-numbers index group)))

(defun fn-nntp-index-group-range-numbers (index group low high)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-numbers-sort
   (fn-nntp-index-numbers (fn-index-query-range index group low high))))

(verify-guards fn-nntp-numbers-sort-loop)
(verify-guards fn-nntp-numbers-sort
  :hints (("Goal" :in-theory (disable fn-nntp-insert-number)
                  :use ((:instance fn-nntp-numbers-sort-of-descending)
                        (:instance fn-nntp-numbers-sort-loop-of-rev-onto (zs nil))))))
(verify-guards fn-nntp-index-group-numbers)
(verify-guards fn-nntp-index-group-count)
(verify-guards fn-nntp-index-group-low)
(verify-guards fn-nntp-index-group-high)
(verify-guards fn-nntp-index-group-next-number)
(verify-guards fn-nntp-index-group-last-number)
(verify-guards fn-nntp-index-group-range-numbers)

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-nntp-index-entry-available)
                    (:definition fn-nntp-index-msgid-okp)))
