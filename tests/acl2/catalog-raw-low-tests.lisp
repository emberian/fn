; Teeth for the maintained raw low (lane s-group-low): books/catalog-logic.lisp
; fn-cat-raws-okp / fn-cat-group-raw-low{correspondence}, the paged writers
; fn-cat$p-commit-w / fn-cat$p-withdraw-w, and the served equation
; (books/served-catalog.lisp fn-scat-group-raw-low-at-top).
;
; Every state is BUILT by the paged executables, the logical catalog beside it
; by the exports' :logic functions.  Numbers: row i of "fn.test" is number i+1.
;
;  * WITNESS (antecedent and conclusion, whole): rows 0-2 of 7 withdrawn; the
;    view is the top view (v = count = 7, horizon 7 <= 7); the paged cell, the
;    logical first raw-kept number and the potential agree on 4.
;  * HYPOTHESIS REMOVAL (the top view): the same rows at v = 6 = count, where
;    the last withdrawal is at version 6 and the horizon is 7: not the top
;    view, and the cell (4) differs from the raw low a reader at 6 sees (1).
;  * MUTATION (the withdraw arm): the old withdrawal without the raw-low plan
;    (fn-cat$p-withdraw-w0) leaves the cell at 1 while the first raw-kept
;    number is 4 -- fn-cat-raws-okp's counterexample.
;  * COMMIT arm: a first row whose Message-ID is not renderable leaves no raw
;    low; the next good row becomes it.
;  * SCAN COST: a withdrawal of the raw low takes exactly the potential's rise.

(in-package "ACL2")
(include-book "../../books/catalog-paged")

(defun crl-id (i)
  (declare (xargs :mode :program))
  (concatenate 'string "<" (coerce (explode-atom i 10) 'string) "@x>"))

(defun crl-row (i bad)
  (declare (xargs :mode :program))
  (let* ((art (append (fn-record-string-octets "Subject: a") '(13 10 13 10 97 13 10)))
         (id (if bad
                 (concatenate 'string "<" (coerce (make-list 300 :initial-element #\a) 'string) "@x>")
               (crl-id i)))
         (h (fn-held-plain (fn-record-make i (+ 1 i) 0 id art '("fn.test") "o" "s" "e" 1 5) i)))
    (fn-held-with-facts h (fn-held-facts-of art))))

(defun crl-commit (i n bad0 fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (if (>= i n) fn-cat$p
    (let ((fn-cat$p (fn-cat$p-commit-w (crl-row i (and bad0 (= i 0))) fn-cat$p)))
      (crl-commit (1+ i) n bad0 fn-cat$p))))

(defun crl-a-commit (i n bad0 c)
  (declare (xargs :mode :program))
  (if (>= i n) c
    (crl-a-commit (1+ i) n bad0 (fn-cat$a-commit (crl-row i (and bad0 (= i 0))) c))))

(defun crl-withdraw (l w0 fn-cat$p)
  (declare (xargs :mode :program :stobjs fn-cat$p))
  (if (atom l) fn-cat$p
    (let ((fn-cat$p (if w0
                        (fn-cat$p-withdraw-w0 (car l) 7 fn-cat$p)
                      (fn-cat$p-withdraw-w (car l) 7 fn-cat$p))))
      (crl-withdraw (cdr l) w0 fn-cat$p))))

(defun crl-a-withdraw (l c)
  (declare (xargs :mode :program))
  (if (atom l) c (crl-a-withdraw (cdr l) (fn-cat$a-withdraw (car l) 7 c))))

; (paged cell, logical raw-first, paged count, paged horizon, the logical catalog)
(defun crl-read (n bad0 l w0 more)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat$p
    (mv-let (r fn-cat$p)
      (let* ((fn-cat$p (crl-commit 0 n bad0 fn-cat$p))
             (fn-cat$p (crl-withdraw l w0 fn-cat$p))
             (fn-cat$p (crl-commit n (+ n more) bad0 fn-cat$p))
             (c (crl-a-commit n (+ n more) bad0 (crl-a-withdraw l (crl-a-commit 0 n bad0 nil)))))
        (mv (list (fn-cat$p-group-raw-low "fn.test" fn-cat$p)
                  (fn-cat-raw-first "fn.test" 1 (fn-cat-group-high "fn.test" c) c)
                  (fn-cat$p-count fn-cat$p)
                  (fn-cat$p-horizon fn-cat$p)
                  c)
            fn-cat$p))
      r)))

; The raw low a reader at version V sees (numbers 1 .. top): the first number
; whose row is visible at V with a renderable Message-ID.
(defun crl-low-at (k top v c)
  (declare (xargs :mode :program))
  (if (> k top) 0
    (let ((s (fn-cat-number-seq "fn.test" k c 0)))
      (if (and (natp s) (< s (len c)) (fn-cat-visiblep s v c)
               (fn-scat-msgid-idp (fn-record-msgid (nth s c))))
          k
        (crl-low-at (1+ k) top v c)))))

; WITNESS: the top view, rows 0-2 of 7 withdrawn.
(assert-event
 (let* ((r (crl-read 6 nil '(0 1 2) nil 1))
        (cell (first r)) (first-kept (second r)) (count (third r)) (hz (fourth r)) (c (fifth r)))
   (and (equal count 7) (<= hz count)                       ; the top view
        (equal cell 4) (equal first-kept 4)                 ; the cell is the raw low
        (equal (crl-low-at 1 7 count c) 4)                  ; and a reader at the top sees it
        (equal (fn-cat-raw-phi "fn.test" c) 4))))

; HYPOTHESIS REMOVAL: v = count = 6 with the last withdrawal at version 6.
(assert-event
 (let* ((r (crl-read 6 nil '(0 1 2) nil 0))
        (cell (first r)) (count (third r)) (hz (fourth r)) (c (fifth r)))
   (and (equal count 6) (> hz count)                        ; not the top view
        (equal cell 4)
        (equal (crl-low-at 1 6 count c) 1)                  ; the reader at 6 still sees number 1
        (not (equal cell (crl-low-at 1 6 count c))))))

; MUTATION: the withdrawal without the raw-low plan.
(assert-event
 (let* ((r (crl-read 6 nil '(0 1 2) t 1)))
   (and (equal (first r) 1) (equal (second r) 4)
        (not (equal (first r) (second r))))))

; COMMIT arm: a first row with a non-renderable Message-ID has no raw low; the
; next row becomes it; withdrawing that one moves the low to the next.
(assert-event
 (let* ((r0 (crl-read 1 t nil nil 0))
        (r1 (crl-read 1 t nil nil 1))
        (r2 (crl-read 2 t '(1) nil 0)))
   (and (equal (first r0) 0) (equal (second r0) 0)
        (equal (first r1) 2) (equal (second r1) 2)
        (equal (first r2) 0) (equal (second r2) 0))))

; SCAN COST: withdrawing row 3 (number 4, the raw low) after rows 0-2 probes
; exactly the potential's rise (one probe: number 5 is kept).
(assert-event
 (let* ((c (crl-a-withdraw '(0 1 2) (crl-a-commit 0 7 nil nil)))
        (steps (fn-cat-withdraw-scan-steps "fn.test" c 3))
        (rise (- (fn-cat-raw-phi "fn.test" (fn-cat$a-withdraw 3 7 c))
                 (fn-cat-raw-phi "fn.test" c))))
   (and (equal steps 1) (equal rise 1)
        ;; a withdrawal that is not the low scans nothing
        (equal (fn-cat-withdraw-scan-steps "fn.test" c 5) 0)
        ;; withdrawing the last kept number scans to the high
        (let* ((c2 (crl-a-withdraw '(0 1 2 3 4 5) (crl-a-commit 0 7 nil nil))))
          (equal (fn-cat-withdraw-scan-steps "fn.test" c2 6)
                 (- (fn-cat-raw-phi "fn.test" (fn-cat$a-withdraw 6 7 c2))
                    (fn-cat-raw-phi "fn.test" c2)))))))
