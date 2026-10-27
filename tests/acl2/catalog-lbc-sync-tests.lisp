;; Route A2 differential: random commit / withdraw / clear sequences are
;; applied to the REAL fn-cat exports (fn-cat-commit, fn-cat-withdraw,
;; fn-cat-clear); at random points fn-lbc-sync catches the columns up.  After
;; a final sync every group summary, number lookup, msgid lookup and
;; withdrawn flag of the columns must agree with fn-cat.  The teeth run
;; withdraws one row in fn-cat after the final sync and must be caught.
(in-package "ACL2")
(include-book "../../books/catalog-columns-sync")
(include-book "../../books/nntp-session")

(defconst *fn-lbcs-pa* '(83 117 98 106 101 99 116 58 32 97 13 10 70 114 111 109 58 32 120 13 10 13 10 97 13 10 46 100 13 10))
(defconst *fn-lbcs-pb* '(83 117 98 106 101 99 116 58 32 98 13 10 13 10 98 13 10))
(defconst *fn-lbcs-pc* '(104 105))
(defun fn-lbcs-next (s) (declare (xargs :mode :program)) (mod (+ (* s 1103515245) 12345) 2147483648))
(defun fn-lbcs-pick (s l) (declare (xargs :mode :program)) (nth (mod (floor s 65536) (len l)) l))
(defun fn-lbcs-groups (s)
  (declare (xargs :mode :program))
  (let ((m (mod (floor s 1024) 7)))
    (case m (0 '("a")) (1 '("b")) (2 '("c")) (3 '("a" "b")) (4 '("b" "c")) (5 '("a" "c")) (t '("a" "b" "c")))))

(defun fn-lbcs-steps (n s fn-arena fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-arena fn-cat fn-lbc) :mode :program))
  (if (zp n) (mv fn-cat fn-lbc)
    (let* ((s (fn-lbcs-next s)) (cnt (fn-cat-count fn-cat)) (op (mod (floor s 256) 20)))
      (cond
       ((= op 19)
        (mv-let (fn-cat fn-lbc) (fn-cat-clear-and-columns fn-cat fn-lbc)
          (fn-lbcs-steps (- n 1) s fn-arena fn-cat fn-lbc)))
       ((>= op 16)
        (let ((fn-lbc (fn-lbc-sync fn-arena fn-cat fn-lbc)))
          (fn-lbcs-steps (- n 1) s fn-arena fn-cat fn-lbc)))
       ((and (>= op 12) (> cnt 0))
        (let* ((s (fn-lbcs-next s)) (target (mod (floor s 4096) cnt)))
          (if (fn-held-withdrawn (fn-cat-at target fn-cat))
              (fn-lbcs-steps (- n 1) s fn-arena fn-cat fn-lbc)
            (let ((fn-cat (fn-cat-withdraw target 0 fn-cat)))
              (fn-lbcs-steps (- n 1) s fn-arena fn-cat fn-lbc)))))
       (t
        (let* ((s (fn-lbcs-next s))
               (payload (fn-lbcs-pick s (list *fn-lbcs-pa* *fn-lbcs-pb* *fn-lbcs-pc*)))
               (msgid (concatenate 'string "<m" (coerce (explode-nonnegative-integer (mod (floor s 8) 9) 10 nil) 'string) "@fn.test>"))
               (h (fn-held-plain (fn-record-make cnt (+ 1 cnt) 0 msgid payload (fn-lbcs-groups s) "o" "s" "e" 1 (mod (floor s 16) 50)) cnt))
               (fn-cat (fn-cat-commit h fn-cat)))
          (fn-lbcs-steps (- n 1) s fn-arena fn-cat fn-lbc)))))))

(defun fn-lbcs-check-numbers (g k top fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-cat fn-lbc) :mode :program))
  (if (> k top) nil
    (append (if (equal (fn-lbc-number-get g k fn-lbc) (fn-cat-group-number g k fn-cat)) nil
              (list (list :number g k (fn-lbc-number-get g k fn-lbc) (fn-cat-group-number g k fn-cat))))
            (fn-lbcs-check-numbers g (+ k 1) top fn-cat fn-lbc))))
(defun fn-lbcs-cat-summary (g fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (list (fn-cat-group-live-count g fn-cat) (fn-cat-group-live-low g fn-cat)
        (fn-cat-group-live-high g fn-cat) (fn-cat-group-next g fn-cat)))
(defun fn-lbcs-check-groups (gs fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-cat fn-lbc) :mode :program))
  (if (atom gs) nil
    (let ((g (car gs)))
      (append (if (equal (fn-lbc-live-summary g fn-lbc) (fn-lbcs-cat-summary g fn-cat)) nil
                (list (list :summary g (fn-lbc-live-summary g fn-lbc) (fn-lbcs-cat-summary g fn-cat))))
              (fn-lbcs-check-numbers g 1 (- (fn-cat-group-next g fn-cat) 1) fn-cat fn-lbc)
              (fn-lbcs-check-groups (cdr gs) fn-cat fn-lbc)))))
(defun fn-lbcs-check-msgids (i fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-cat fn-lbc) :mode :program))
  (if (>= i 9) nil
    (let ((m (concatenate 'string "<m" (coerce (explode-nonnegative-integer i 10 nil) 'string) "@fn.test>")))
      (append (if (equal (fn-lbc-msgid-seqs m fn-lbc) (fn-cat-msgid-seqs m fn-cat)) nil
                (list (list :msgid m (fn-lbc-msgid-seqs m fn-lbc) (fn-cat-msgid-seqs m fn-cat))))
              (fn-lbcs-check-msgids (+ i 1) fn-cat fn-lbc)))))
(defun fn-lbcs-check-withdrawn (i fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-cat fn-lbc) :mode :program))
  (if (>= i (fn-cat-count fn-cat)) nil
    (append (if (equal (and (fn-lbc-withdrawn i fn-lbc) t) (and (fn-held-withdrawn (fn-cat-at i fn-cat)) t)) nil
              (list (list :withdrawn i)))
            (fn-lbcs-check-withdrawn (+ i 1) fn-cat fn-lbc))))
(defun fn-lbcs-check (fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-cat fn-lbc) :mode :program))
  (append (and (not (equal (fn-lbc-count fn-lbc) (fn-cat-count fn-cat))) (list :count))
          (fn-lbcs-check-groups '("a" "b" "c" "d") fn-cat fn-lbc)
          (fn-lbcs-check-msgids 0 fn-cat fn-lbc)
          (fn-lbcs-check-withdrawn 0 fn-cat fn-lbc)))

(defun fn-lbcs-one (seed n bad fn-arena fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-arena fn-cat fn-lbc) :mode :program))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-lbc (fn-lbc-clear-columns fn-lbc)) (fn-lbc (fn-lbc-slots-ensure fn-lbc)))
    (mv-let (fn-cat fn-lbc) (fn-lbcs-steps n seed fn-arena fn-cat fn-lbc)
      (let* ((fn-lbc (fn-lbc-sync fn-arena fn-cat fn-lbc))
             (fn-cat (if (and bad (> (fn-cat-count fn-cat) 0) (not (fn-held-withdrawn (fn-cat-at 0 fn-cat))))
                         (fn-cat-withdraw 0 0 fn-cat) fn-cat)))
        (mv (fn-lbcs-check fn-cat fn-lbc) fn-cat fn-lbc)))))
(defun fn-lbcs-run (seed n bad)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let ((r (with-local-stobj fn-cat
                 (mv-let (r fn-cat)
                   (with-local-stobj fn-lbc
                     (mv-let (r fn-cat fn-lbc)
                       (fn-lbcs-one seed n bad fn-arena fn-cat fn-lbc)
                       (mv r fn-cat)))
                   r))))
        (mv r fn-arena))
      r)))
(defun fn-lbcs-all (seeds n bad)
  (declare (xargs :mode :program))
  (if (zp seeds) nil
    (let ((r (fn-lbcs-run seeds n bad)))
      (if r (cons (list seeds r) (fn-lbcs-all (- seeds 1) n bad)) (fn-lbcs-all (- seeds 1) n bad)))))
(defun fn-lbcs-bad-count (seeds n)
  (declare (xargs :mode :program))
  (if (zp seeds) 0 (+ (if (fn-lbcs-run seeds n t) 1 0) (fn-lbcs-bad-count (- seeds 1) n))))

(with-guard-checking-event :none
 (assert-event (equal (fn-lbcs-all 300 40 nil) nil)))
(with-guard-checking-event :none
 (assert-event (< 0 (fn-lbcs-bad-count 50 20))))
