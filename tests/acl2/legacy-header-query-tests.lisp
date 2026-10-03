; Literal source/readiness/work witnesses plus original field projection.
(in-package "ACL2")
(include-book "../../books/legacy-header-query")

(defconst *lhqt-folded*
 '(88 45 67 117 115 116 111 109 58 13 10 32 102 105 114 115 116 13 10
   9 102 111 108 100 101 100 13 10 88 45 67 117 115 116 111 109 58
   32 105 103 110 111 114 101 100 13 10 13 10 65 13 10))
(defconst *lhqt-name* '(88 45 99 85 83 116 79 109))

(defun lhqt-finish (cursor fuel steps fn-arena)
  (declare (xargs :stobjs fn-arena :measure (nfix steps) :verify-guards nil))
  (if (or (zp steps) (not (eq (fn-lhq-verdict cursor) :yield))) cursor
    (mv-let (next used) (fn-lhq-tick cursor fuel fn-arena)
      (declare (ignore used))
      (lhqt-finish next fuel (- steps 1) fn-arena))))

(defun lhqt-case (bytes field fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arena-seal-list bytes fn-arena))
         (start (fn-lhq-begin 0 (len bytes) '(:captured 23) field)))
    (mv-let (one used) (fn-lhq-tick start fuel fn-arena)
      (let* ((done (lhqt-finish start fuel (+ 1 (len bytes)) fn-arena))
         (span (fn-lhq-field done))
         (parsed (fn-article-parse bytes))
         (ok (fn-article-result-okp parsed)))
    (mv
     (and (fn-lhq-ready-p start fn-arena)
          (natp used)
          (<= used (nfix fuel))
          (fn-lhq-ready-p one fn-arena)
          (let ((out (fn-lpc-at 0 one)) (s (fn-lpc-at 0 start)))
            (and (equal (fn-lpc-at 0 out) (fn-lpc-at 0 s))
                 (equal (fn-lpc-at 1 out) (fn-lpc-at 1 s))
                 (equal (fn-lpc-at 2 out) (fn-lpc-at 2 s))))
          (equal (fn-lhq-verdict done) (if ok :valid :invalid))
          (if ok
              (equal (if span
                         (fn-nov-scrub (subseq bytes (fn-lpc-at 1 span)
                                              (+ (fn-lpc-at 1 span) (fn-lpc-at 2 span)))) nil)
                     (fn-nov-header-content (fn-article-result-article parsed) field))
            (not span))
          (or (not span) (equal (fn-lpc-at 3 span) '(:captured 23)))) fn-arena)))))

(defun lhqt-exec (bytes field fuel)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (lhqt-case bytes field fuel fn-arena) answer)))

(assert-event (and (lhqt-exec *lhqt-folded* *lhqt-name* 1)
                   (lhqt-exec *lhqt-folded* *lhqt-name* 3)
                   (lhqt-exec *lhqt-folded* '(109 105 115 115 105 110 103) 1)
                   (lhqt-exec '(88 58 32 111 107 13 10 66 97 100 13 10 13 10) '(88) 1)))

; Changing the retained pin really changes the source identity conclusion.
(assert-event
 (let* ((s (fn-lhq-begin 0 7 :original '(120)))
        (wrong (fn-lhq-begin 0 7 :different '(120))))
   (and (equal (fn-lpc-at 2 (fn-lpc-at 0 s)) :original)
        (not (equal (fn-lpc-at 2 (fn-lpc-at 0 wrong)) :original)))))
