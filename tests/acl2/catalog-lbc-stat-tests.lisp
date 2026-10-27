;; Route A3 differential for STAT: random stores built through the real fn-cat
;; exports, the columns caught up by fn-lbc-sync, then fn-lbc-stat-reply
;; compared with fn-rcompat-retrieval-cat at kind :stat over sessions (no
;; group, a group with and without a current article), argument forms (none,
;; numbers in and out of range, message-ids held and not held, a malformed
;; token) and pinned versions v from 0 to the count (the reachable set).  Payloads include a
;; reclaimed tombstone.  The teeth run withdraws row 0 at version 0 in the
;; columns only, after the sync (invisible at every pinned v >= 1); the replies must then differ for some seed.
(in-package "ACL2")
(include-book "../../books/catalog-columns-sync")
(include-book "../../books/catalog-columns-stat")
(include-book "../../books/reclaim-tombstone")
(include-book "../../books/served-catalog")

(defconst *fn-lbst-pa* '(83 117 98 106 101 99 116 58 32 97 13 10 70 114 111 109 58 32 120 13 10 13 10 97 13 10 46 100 13 10))
(defconst *fn-lbst-pb* '(83 117 98 106 101 99 116 58 32 98 13 10 13 10 98 13 10))
(defconst *fn-lbst-pc* '(104 105))
(defun fn-lbst-tomb ()
  (declare (xargs :mode :program))
  (append *fn-rcl-magic* (make-list *fn-rcl-tombstone-fixed* :initial-element 0)))
(defun fn-lbst-next (s) (declare (xargs :mode :program)) (mod (+ (* s 1103515245) 12345) 2147483648))
(defun fn-lbst-pick (s l) (declare (xargs :mode :program)) (nth (mod (floor s 65536) (len l)) l))
(defun fn-lbst-groups (s)
  (declare (xargs :mode :program))
  (let ((m (mod (floor s 1024) 7)))
    (case m (0 '("a")) (1 '("b")) (2 '("c")) (3 '("a" "b")) (4 '("b" "c")) (5 '("a" "c")) (t '("a" "b" "c")))))
(defun fn-lbst-msgid (k)
  (declare (xargs :mode :program))
  (concatenate 'string "<m" (coerce (explode-nonnegative-integer k 10 nil) 'string) "@fn.test>"))

(defun fn-lbst-build (n s fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (if (zp n) fn-cat
    (let* ((s (fn-lbst-next s)) (cnt (fn-cat-count fn-cat)) (op (mod (floor s 256) 10)))
      (if (and (>= op 8) (> cnt 0))
          (let* ((s (fn-lbst-next s)) (target (mod (floor s 4096) cnt)))
            (let ((fn-cat (if (fn-held-withdrawn (fn-cat-at target fn-cat)) fn-cat (fn-cat-withdraw target 0 fn-cat))))
              (fn-lbst-build (- n 1) s fn-cat)))
        (let* ((s (fn-lbst-next s))
               (payload (fn-lbst-pick s (list *fn-lbst-pa* *fn-lbst-pb* *fn-lbst-pc* (fn-lbst-tomb))))
               (h (fn-held-plain (fn-record-make cnt (+ 1 cnt) 0 (fn-lbst-msgid (mod (floor s 8) 9)) payload
                                                 (fn-lbst-groups s) "o" "s" "e" 1 (mod (floor s 16) 50)) cnt)))
          (let ((fn-cat (fn-cat-commit h fn-cat)))
            (fn-lbst-build (- n 1) s fn-cat)))))))

(defun fn-lbst-sessions-for (g cs)
  (declare (xargs :mode :program))
  (if (atom cs) nil (cons (fn-nntp-make-session t g (car cs) nil) (fn-lbst-sessions-for g (cdr cs)))))
(defun fn-lbst-sessions-all (gs)
  (declare (xargs :mode :program))
  (if (atom gs) nil
    (append (fn-lbst-sessions-for (car gs) '(nil 0 1 2 3 5 99)) (fn-lbst-sessions-all (cdr gs)))))
(defun fn-lbst-sessions ()
  (declare (xargs :mode :program))
  (cons (fn-nntp-make-session t nil nil nil) (fn-lbst-sessions-all '("a" "b" "c" "zz"))))
(defun fn-lbst-args-of (toks)
  (declare (xargs :mode :program))
  (if (atom toks) nil (cons (list (fn-nntp-string-octets (car toks))) (fn-lbst-args-of (cdr toks)))))
(defun fn-lbst-args ()
  (declare (xargs :mode :program))
  (cons nil (fn-lbst-args-of
    (append '("0" "1" "2" "3" "4" "5" "6" "99")
            (list (fn-lbst-msgid 0) (fn-lbst-msgid 1) (fn-lbst-msgid 2) (fn-lbst-msgid 3) (fn-lbst-msgid 4)
                  (fn-lbst-msgid 5) (fn-lbst-msgid 6) (fn-lbst-msgid 7) (fn-lbst-msgid 8) (fn-lbst-msgid 9))
            '("<bad" "x")))))

(defun fn-lbst-diffs-1 (session args v fn-arena fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-arena fn-cat fn-lbc) :mode :program))
  (let ((old (fn-rcompat-retrieval-cat session nil nil :stat args nil v fn-arena fn-cat))
        (new (fn-lbc-stat-reply session args v fn-lbc)))
    (if (equal old new) nil (list (list session args v)))))
(defun fn-lbst-diffs-args (session as v fn-arena fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-arena fn-cat fn-lbc) :mode :program))
  (if (atom as) nil
    (append (fn-lbst-diffs-1 session (car as) v fn-arena fn-cat fn-lbc)
            (fn-lbst-diffs-args session (cdr as) v fn-arena fn-cat fn-lbc))))
(defun fn-lbst-diffs-sessions (ss as v fn-arena fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-arena fn-cat fn-lbc) :mode :program))
  (if (atom ss) nil
    (append (fn-lbst-diffs-args (car ss) as v fn-arena fn-cat fn-lbc)
            (fn-lbst-diffs-sessions (cdr ss) as v fn-arena fn-cat fn-lbc))))
(defun fn-lbst-diffs-views (vs as ss fn-arena fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-arena fn-cat fn-lbc) :mode :program))
  (if (atom vs) nil
    (append (fn-lbst-diffs-sessions ss as (car vs) fn-arena fn-cat fn-lbc)
            (fn-lbst-diffs-views (cdr vs) as ss fn-arena fn-cat fn-lbc))))
(defun fn-lbst-views (cnt)
  (declare (xargs :mode :program))
  (if (zp cnt) '(0) (cons cnt (fn-lbst-views (- cnt 1)))))

(defun fn-lbst-one (seed n bad fn-arena fn-cat fn-lbc)
  (declare (xargs :stobjs (fn-arena fn-cat fn-lbc) :mode :program))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-lbc (fn-lbc-clear-columns fn-lbc)) (fn-lbc (fn-lbc-slots-ensure fn-lbc))
         (fn-cat (fn-lbst-build n seed fn-cat))
         (fn-lbc (fn-lbc-sync fn-arena fn-cat fn-lbc))
         (fn-lbc (if (and bad (> (fn-lbc-count fn-lbc) 0)) (fn-lbc-withdraw-row 0 0 0 fn-lbc) fn-lbc)))
    (mv (fn-lbst-diffs-views (fn-lbst-views (fn-cat-count fn-cat)) (fn-lbst-args) (fn-lbst-sessions)
                             fn-arena fn-cat fn-lbc)
        fn-cat fn-lbc)))
(defun fn-lbst-run (seed n bad)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let ((r (with-local-stobj fn-cat
                 (mv-let (r fn-cat)
                   (with-local-stobj fn-lbc
                     (mv-let (r fn-cat fn-lbc)
                       (fn-lbst-one seed n bad fn-arena fn-cat fn-lbc)
                       (mv r fn-cat)))
                   r))))
        (mv r fn-arena))
      r)))
(defun fn-lbst-all (seeds n)
  (declare (xargs :mode :program))
  (if (zp seeds) nil
    (let ((r (fn-lbst-run seeds n nil)))
      (if r (cons (list seeds (take (min 2 (len r)) r)) (fn-lbst-all (- seeds 1) n)) (fn-lbst-all (- seeds 1) n)))))
(defun fn-lbst-bad-count (seeds n)
  (declare (xargs :mode :program))
  (if (zp seeds) 0 (+ (if (fn-lbst-run seeds n t) 1 0) (fn-lbst-bad-count (- seeds 1) n))))

(with-guard-checking-event :none
 (assert-event (equal (fn-lbst-all 60 14) nil)))
(with-guard-checking-event :none
 (assert-event (< 0 (fn-lbst-bad-count 30 14))))
