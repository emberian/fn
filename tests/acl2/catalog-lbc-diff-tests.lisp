;; Route A1 differential: random post/withdraw sequences over three groups and
;; nine message-ids (duplicates, a dot-stuffed line, a malformed payload) are
;; applied to the abstract rows (fn-cat$a-commit / fn-cat$a-withdraw) and, in
;; step, to the columns through fn-lbc-commit-row / fn-lbc-withdraw-row.  Every
;; group summary, number lookup, msgid lookup and withdrawn flag must agree.
;; The teeth run applies one extra withdrawal to the columns only; it must
;; be caught.
(in-package "ACL2")
(include-book "../../books/catalog-columns-load")

(defconst *fn-lbcd-pa* '(83 117 98 106 101 99 116 58 32 97 13 10 70 114 111 109 58 32 120 13 10 13 10 97 13 10 46 100 13 10))
(defconst *fn-lbcd-pb* '(83 117 98 106 101 99 116 58 32 98 13 10 13 10 98 13 10))
(defconst *fn-lbcd-pc* '(104 105))
(defun fn-lbcd-next (s) (declare (xargs :mode :program)) (mod (+ (* s 1103515245) 12345) 2147483648))
(defun fn-lbcd-pick (s l) (declare (xargs :mode :program)) (nth (mod (floor s 65536) (len l)) l))
(defun fn-lbcd-groups (s)
  (declare (xargs :mode :program))
  (let ((m (mod (floor s 1024) 7)))
    (case m (0 '("a")) (1 '("b")) (2 '("c")) (3 '("a" "b")) (4 '("b" "c")) (5 '("a" "c")) (t '("a" "b" "c")))))
(defun fn-lbcd-entry-loc (row log)
  (declare (xargs :mode :program))
  (let* ((e (fn-lb-log-model-row-entry row log)) (seg (fn-lb-log-model-row-segment row log)))
    (mv-let (l0 l1) (fn-loc-make seg (nth 3 e) (nth 4 e))
      (list l0 l1 (fn-arx-entry-ok (fn-lb-entry-octets seg (nth 3 e) log)
                                   (fn-lb-entry-protected-len seg (nth 3 e) log))))))
;; returns (mv abs log fn-lbc)
(defun fn-lbcd-steps (n s abs log fn-lbc)
  (declare (xargs :stobjs fn-lbc :mode :program))
  (if (zp n) (mv abs log fn-lbc)
    (let* ((s (fn-lbcd-next s)) (cnt (len abs)) (op (mod (floor s 256) 10)))
      (if (and (>= op 8) (> cnt 0))
          (let* ((s (fn-lbcd-next s)) (target (mod (floor s 4096) cnt)))
            (let ((fn-lbc (fn-lbc-withdraw-row target cnt 0 fn-lbc)))
              (fn-lbcd-steps (- n 1) s (fn-cat$a-withdraw target 0 abs) log fn-lbc)))
        (let* ((s (fn-lbcd-next s))
               (payload (fn-lbcd-pick s (list *fn-lbcd-pa* *fn-lbcd-pb* *fn-lbcd-pc*)))
               (msgid (concatenate 'string "<m" (coerce (explode-nonnegative-integer (mod (floor s 8) 9) 10 nil) 'string) "@fn.test>"))
               (h (fn-held-plain (fn-record-make cnt (+ 1 cnt) 0 msgid payload (fn-lbcd-groups s) "o" "s" "e" 1 (mod (floor s 16) 50)) cnt))
               (abs2 (fn-cat$a-commit h abs))
               (row (car (last abs2)))
               (log2 (fn-lb-log-model-append row payload 1 log))
               (loc (fn-lbcd-entry-loc row log2)))
          (let ((fn-lbc (fn-lbc-commit-row row payload (nth 0 loc) (nth 1 loc) (nth 2 loc) fn-lbc)))
            (fn-lbcd-steps (- n 1) s abs2 log2 fn-lbc)))))))
(defun fn-lbcd-check-numbers (g k top abs fn-lbc)
  (declare (xargs :stobjs fn-lbc :mode :program))
  (if (> k top) nil
    (append (if (equal (fn-lbc-number-get g k fn-lbc) (fn-cat$a-group-number g k abs)) nil
              (list (list :number g k (fn-lbc-number-get g k fn-lbc) (fn-cat$a-group-number g k abs))))
            (fn-lbcd-check-numbers g (+ k 1) top abs fn-lbc))))

(defun fn-lbcd-check-groups (gs abs fn-lbc)
  (declare (xargs :stobjs fn-lbc :mode :program))
  (if (atom gs) nil
    (let ((g (car gs)))
      (append (if (equal (fn-lbc-live-summary g fn-lbc)
                         (list (fn-cat$a-group-live-count g abs) (fn-cat$a-group-live-low g abs)
                               (fn-cat$a-group-live-high g abs) (fn-cat$a-group-next g abs)))
                  nil (list (list :summary g (fn-lbc-live-summary g fn-lbc)
                                  (list (fn-cat$a-group-live-count g abs) (fn-cat$a-group-live-low g abs)
                                        (fn-cat$a-group-live-high g abs) (fn-cat$a-group-next g abs)))))
              (fn-lbcd-check-numbers g 1 (- (fn-cat$a-group-next g abs) 1) abs fn-lbc)
              (fn-lbcd-check-groups (cdr gs) abs fn-lbc)))))

(defun fn-lbcd-check-msgids (i abs fn-lbc)
  (declare (xargs :stobjs fn-lbc :mode :program))
  (if (>= i 9) nil
    (let ((m (concatenate 'string "<m" (coerce (explode-nonnegative-integer i 10 nil) 'string) "@fn.test>")))
      (append (if (equal (fn-lbc-msgid-seqs m fn-lbc) (fn-cat$a-msgid-seqs m abs)) nil
                (list (list :msgid m (fn-lbc-msgid-seqs m fn-lbc) (fn-cat$a-msgid-seqs m abs))))
              (fn-lbcd-check-msgids (+ i 1) abs fn-lbc)))))
(defun fn-lbcd-check-withdrawn (i abs fn-lbc)
  (declare (xargs :stobjs fn-lbc :mode :program))
  (if (>= i (len abs)) nil
    (append (if (equal (and (fn-lbc-withdrawn i fn-lbc) t) (and (fn-held-withdrawn (nth i abs)) t)) nil
              (list (list :withdrawn i)))
            (fn-lbcd-check-withdrawn (+ i 1) abs fn-lbc))))
(defun fn-lbcd-one (seed n fn-lbc)
  (declare (xargs :stobjs fn-lbc :mode :program))
  (let* ((fn-lbc (fn-lbc-clear-columns fn-lbc)) (fn-lbc (fn-lbc-slots-ensure fn-lbc)))
    (mv-let (abs log fn-lbc) (fn-lbcd-steps n seed nil nil fn-lbc)
      (declare (ignore log))
      (mv (append (fn-lbcd-check-groups '("a" "b" "c" "d") abs fn-lbc)
                  (fn-lbcd-check-msgids 0 abs fn-lbc)
                  (fn-lbcd-check-withdrawn 0 abs fn-lbc))
          fn-lbc))))
(defun fn-lbcd-all (seeds n)
  (declare (xargs :mode :program))
  (if (zp seeds) nil
    (let ((r (with-local-stobj fn-lbc (mv-let (r fn-lbc) (fn-lbcd-one seeds n fn-lbc) r))))
      (if r (cons (list seeds r) (fn-lbcd-all (- seeds 1) n)) (fn-lbcd-all (- seeds 1) n)))))

(defun fn-lbcd-one-bad (seed n fn-lbc)
  (declare (xargs :stobjs fn-lbc :mode :program))
  (let* ((fn-lbc (fn-lbc-clear-columns fn-lbc)) (fn-lbc (fn-lbc-slots-ensure fn-lbc)))
    (mv-let (abs log fn-lbc) (fn-lbcd-steps n seed nil nil fn-lbc)
      (declare (ignore log))
      (let ((fn-lbc (fn-lbc-withdraw-row 0 999 0 fn-lbc)))
        (mv (append (fn-lbcd-check-groups '("a" "b" "c") abs fn-lbc) (fn-lbcd-check-withdrawn 0 abs fn-lbc)) fn-lbc)))))
(defun fn-lbcd-bad-all (seeds n)
  (declare (xargs :mode :program))
  (if (zp seeds) 0
    (+ (if (with-local-stobj fn-lbc (mv-let (r fn-lbc) (fn-lbcd-one-bad seeds n fn-lbc) r)) 1 0) (fn-lbcd-bad-all (- seeds 1) n))))

(with-guard-checking-event :none
 (assert-event (equal (fn-lbcd-all 300 30) nil)))
(with-guard-checking-event :none
 (assert-event (< 0 (fn-lbcd-bad-all 50 14))))
