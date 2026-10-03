(in-package "ACL2")
(include-book "../../books/owner-time-journal-stream")

(defun otjs-test-splits (n xs)
  (declare (xargs :measure (nfix n)))
  (let* ((whole (fn-otjs-consume xs (fn-otjs-init)))
         (split (fn-otjs-consume (nthcdr (nfix n) xs)
                   (fn-otjs-consume (take (nfix n) xs) (fn-otjs-init)))))
    (and (equal split whole)
         (or (zp n) (otjs-test-splits (- n 1) xs)))))

(defun otjs-test-cases (cases)
  (if (consp cases)
      (let* ((xs (car cases))
             (st (fn-otjs-consume xs (fn-otjs-init))))
        (and (equal (fn-otjs-report st) (fn-otm-journal-report xs))
             (equal (fn-otjs-exit st) (fn-otm-journal-exit xs))
             (<= (len (fn-otjs-fields st)) 8)
             (otjs-test-splits (len xs) xs)
             (otjs-test-cases (cdr cases))))
    t))

(assert-event
 (let* ((start (fn-otm-start-line 1700000000 t))
        (note (fn-otm-jline '(1 5 0 1 2 0 0)))
        (gap (fn-otm-jline '(3 5 0 1 2 0 0)))
        (unknown (fn-otm-jline '(1 99 0 0 0 0 0)))
        (long (fn-otm-jline '(8 0 2 3 4 5 6 7 8 9 10 11 12)))
        (huge (fn-otm-start-line (expt 10 100) t)))
   (otjs-test-cases
    (list nil start (append start note) (append start note start note)
          (append start gap note) (append start unknown note)
          (append start long note) huge
          '(10) '(48 32 32 49 10) '(48 32 49) '(48 32)
          (append start '(255) note)
          (append start (butlast note 1))
          (fn-otm-jline (make-list 500 :initial-element 0))))))

; Literal chunk-associativity witness (unconditional keystone).
(assert-event
 (let ((a '(48 32 48 32 48)) (b '(32 48 32 48 32 48 32 48 10))
       (st (fn-otjs-init)))
   (equal (fn-otjs-consume (append a b) st)
          (fn-otjs-consume b (fn-otjs-consume a st)))))
; Literal bounded-fields keystone premise and conclusion.
(assert-event
 (let ((st (fn-otjs-init)) (xs (fn-otm-jline (make-list 500 :initial-element 0))))
   (and (<= (len (fn-otjs-fields st)) 8)
        (<= (len (fn-otjs-fields (fn-otjs-consume xs st))) 8))))
; Corrupted state, field-bound premise removed: no retained hypotheses;
; both the omitted premise and conclusion affirmatively fail.
(assert-event
 (let ((st '(:whole nil (0 1 2 3 4 5 6 7 8) 0 0 :agrees nil)))
   (and (not (<= (len (fn-otjs-fields st)) 8))
        (not (<= (len (fn-otjs-fields (fn-otjs-consume '(48) st))) 8)))))
(assert-event
 (and (eq (symbol-class 'fn-otjs-init (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-otjs-consume (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-otjs-read-count (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-otjs-report (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-otjs-exit (w state)) :common-lisp-compliant)))

; Literal unconditional report keystone: continue counting complete entries
; and segment markers after the first replay gap, including an overlong
; rejected segment. A later restart cannot erase the earlier verdict.
(assert-event
 (let* ((xs (append (fn-otm-start-line (expt 10 100) t)
                    (fn-otm-jline '(1 5 0 1 2 0 0))
                    (fn-otm-jline '(3 5 0 1 2 0 0))
                    (fn-otm-jline '(999 0 0 0 0 0 0 0 0 0 0))
                    (fn-otm-start-line 1700000000 t)
                    (fn-otm-jline '(1 5 0 1 2 0 0)) '(255)))
        (st (fn-otjs-consume xs (fn-otjs-init))))
   (and (equal (fn-otjs-report st) (fn-otm-journal-report xs))
        (equal (fn-otjs-report st)
               (fn-osch-text "journal: entries=6 segments=3 status=malformed replay=gap-at-2
")))))

; Literal unconditional exit keystone, with a torn suffix after the gap.
(assert-event
 (let* ((xs (append (fn-otm-start-line 1 t)
                    (fn-otm-jline '(2 5 0 1 2 0 0)) '(48 32)))
        (st (fn-otjs-consume xs (fn-otjs-init))))
   (and (equal (fn-otjs-exit st) (fn-otm-journal-exit xs))
        (equal (fn-otjs-exit st) 1)
        (equal (fn-otjs-status st) :torn))))
