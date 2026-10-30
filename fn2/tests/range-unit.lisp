;; Layer C3 unit: range reads over overlays and runs, and the read plan.
(in-package "ACL2")
(include-book "runs-assembly")

; Overview entry (group g, number n): article 100+n, position 10n, line "A" tag.
(defun fn2-rgt-ov (g n tag) (declare (xargs :verify-guards nil)) (list g n (+ 100 n) (* 10 n) (list 65 tag)))
(defun fn2-rgt-ovs (g n k step tag)
 (declare (xargs :verify-guards nil :measure (nfix k)))
 (if (zp k) nil (cons (fn2-rgt-ov g n tag) (fn2-rgt-ovs g (+ n step) (- k 1) step tag))))
(defconst *fn2-rgt-key* '((group (:id group)) (number (:id group-number))))
; Two runs (even numbers, odd numbers, both of groups 1 and 2) and an
; overlay that holds newer rows for numbers 4 and 9 and numbers 11-15.
(defconst *fn2-rgt-sources*
 (list (append (fn2-rgt-ovs 1 2 5 2 1) (fn2-rgt-ovs 2 2 20 2 1))
       (append (fn2-rgt-ovs 1 1 5 2 2) (fn2-rgt-ovs 2 1 20 2 2))
       (append (list (fn2-rgt-ov 1 4 3) (fn2-rgt-ov 1 9 3)) (fn2-rgt-ovs 1 11 5 1 3))))
(defun fn2-rgt-holds (cases)
 (declare (xargs :verify-guards nil))
 (or (atom cases)
     (let ((c (car cases)))
      (and (equal (fn2-range-image 3 *fn2-overview-entry* *fn2-rgt-sources* (nth 0 c) (nth 1 c) (nth 2 c) (nth 3 c) (nth 4 c) (nth 5 c))
                  (fn2-range-spec *fn2-rgt-key* *fn2-rgt-sources* (nth 0 c) (nth 1 c) (nth 2 c) (nth 3 c)))
           (fn2-rgt-holds (cdr cases))))))
; (lo hi pidx plimit budget sealat): whole group, a window, a position
; limit (an exactly-at read), an empty window, group 2 across all of it, a
; budget of one with the overlay sealed after the third and after the
; first delivery.
(defconst *fn2-rgt-cases*
 '(((1 0) (1 99) nil 0 8 nil) ((1 3) (1 12) nil 0 8 nil) ((1 0) (1 99) 3 70 4 nil) ((1 16) (1 99) nil 0 8 nil)
   ((2 0) (2 99) nil 0 8 nil) ((1 0) (2 7) nil 0 1 3) ((1 0) (1 99) 3 120 1 1)))
(defun fn2-range-read-exact-positive ()
 (declare (xargs :verify-guards nil))
 (and (fn2-range-inputp *fn2-overview-entry* *fn2-rgt-key* *fn2-rgt-sources* 1)
      (fn2-rgt-holds *fn2-rgt-cases*)
      ;; the cases are not vacuous: the whole group delivers 15 rows, newest ones for 4 and 9
      (equal (len (fn2-range-image 3 *fn2-overview-entry* *fn2-rgt-sources* '(1 0) '(1 99) nil 0 8 nil)) 15)
      (equal (nth 3 (fn2-range-image 3 *fn2-overview-entry* *fn2-rgt-sources* '(1 0) '(1 99) nil 0 8 nil)) (fn2-rgt-ov 1 4 3))))
; Negative: a run whose entries are out of order (premise false) reads
; back otherwise than the specification.
(defconst *fn2-rgt-bad*
 (list (list (fn2-rgt-ov 1 6 1) (fn2-rgt-ov 1 2 1) (fn2-rgt-ov 1 8 1)) (list (fn2-rgt-ov 1 4 3))))
(defun fn2-range-read-exact-negative ()
 (declare (xargs :verify-guards nil))
 (and (not (fn2-range-inputp *fn2-overview-entry* *fn2-rgt-key* *fn2-rgt-bad* 8))
      (not (equal (fn2-range-image 3 *fn2-overview-entry* *fn2-rgt-bad* '(1 0) '(1 99) nil 0 8 nil)
                  (fn2-range-spec *fn2-rgt-key* *fn2-rgt-bad* '(1 0) '(1 99) nil 0)))))
(fn2-assert-owed-teeth fn2-range-read-exact)

;; The addressing schema reads the same way: principal 7's entries after
;; position 25 (a stream seek by key), across a run and the overlay.
(defun fn2-rgt-ad (p pos) (declare (xargs :verify-guards nil)) (list p pos (+ 1000 pos) 3 1))
(defconst *fn2-rgt-addr* (list (list (fn2-rgt-ad 7 10) (fn2-rgt-ad 7 20) (fn2-rgt-ad 7 30) (fn2-rgt-ad 8 5))
                               (list (fn2-rgt-ad 7 40) (fn2-rgt-ad 9 1))))
(assert-event (equal (fn2-range-image 4 *fn2-addr-entry* *fn2-rgt-addr* '(7 26) '(7 1000000) nil 0 8 nil)
                     (list (fn2-rgt-ad 7 30) (fn2-rgt-ad 7 40))))
;; A schema with an octet key is refused by name.
(assert-event (equal (fn2-range-image 1 *fn2-identity-entry* (list nil nil) (list nil (cons 1 nil)) (list nil (cons 1 nil)) nil 0 8 nil)
                     '(:key-kind)))

;; Teeth for fn2-range-seek-position. Positive: group 1 of the sources above
;; (position 10n for number n, the overlay's rows too), after positions 0,
;; 35, 40 and 41, and past every entry; group 2. Negative: positions that
;; do not grow with the number (premise false) mislead the bisection.
(defun fn2-rgt-seeks (prefix ps)
 (declare (xargs :verify-guards nil))
 (if (atom ps) nil
  (cons (car (fn2-range-seek-image 3 *fn2-overview-entry* *fn2-rgt-sources* prefix (car ps) 1000 3 8))
        (fn2-rgt-seeks prefix (cdr ps)))))
(defun fn2-rgt-seek-specs (prefix ps)
 (declare (xargs :verify-guards nil))
 (if (atom ps) nil
  (cons (fn2-range-seek-spec *fn2-rgt-key* *fn2-rgt-sources* prefix (car ps) 1000 3) (fn2-rgt-seek-specs prefix (cdr ps)))))
(defun fn2-range-seek-position-positive ()
 (declare (xargs :verify-guards nil))
 (and (fn2-range-monotonep *fn2-rgt-key* *fn2-rgt-sources* '(1) 3) (fn2-range-monotonep *fn2-rgt-key* *fn2-rgt-sources* '(2) 3)
      (equal (fn2-rgt-seeks '(1) '(0 35 40 41 150)) '(0 4 5 5 16))
      (equal (fn2-rgt-seeks '(1) '(0 35 40 41 150)) (fn2-rgt-seek-specs '(1) '(0 35 40 41 150)))
      (equal (fn2-rgt-seeks '(2) '(0 205 400)) (fn2-rgt-seek-specs '(2) '(0 205 400)))))
(defconst *fn2-rgt-unordered*
 (list (list (list 1 1 101 10 (list 65)) (list 1 2 102 20 (list 65)) (list 1 3 103 30 (list 65)) (list 1 4 104 40 (list 65))
             (list 1 5 105 50 (list 65)) (list 1 6 106 60 (list 65)) (list 1 7 107 70 (list 65)) (list 1 8 108 5 (list 65)))
       nil))
(defun fn2-range-seek-position-negative ()
 (declare (xargs :verify-guards nil))
 (and (not (fn2-range-monotonep *fn2-rgt-key* *fn2-rgt-unordered* '(1) 3))
      (not (equal (car (fn2-range-seek-image 3 *fn2-overview-entry* *fn2-rgt-unordered* '(1) 45 1000 3 8))
                  (fn2-range-seek-spec *fn2-rgt-key* *fn2-rgt-unordered* '(1) 45 1000 3)))))
(fn2-assert-owed-teeth fn2-range-seek-position)
;; Probes per seek (bisection over [0, 1000): about log2 1000).
(value-triple (cw "fn2-range seek probes: ~x0~%" (cadr (fn2-range-seek-image 3 *fn2-overview-entry* *fn2-rgt-sources* '(1) 35 1000 3 8))))
