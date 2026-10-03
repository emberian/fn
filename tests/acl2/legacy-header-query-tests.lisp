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
          (fn-lhq-bounds-p start)
          (fn-lhq-bounds-p one)
          (fn-lhq-bounds-p done)
          (fn-lpc-span-bound-p span 0 '(:captured 23) (len bytes))
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

; Hypothesis-removal witnesses, deliberately corrupted retained cursor state.
; Each checks the other retained hypothesis and negates the omitted predicate.
(defun lhqt-hyp-removal-case (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((bytes '(88 58 32 120 13 10 13 10))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arena-seal-list bytes fn-arena))
         (header (fn-lpc-put 0 :body (fn-lpc-header-begin)))
         (bad-bounds
           (list (fn-lpc-put 4
                   (fn-lpc-put 8 '((0 40 1 :pin) nil nil nil nil) header)
                   (fn-lpc-put 3 8 (fn-lpc-begin 0 8 :pin))) nil))
         (bad-ready
           (list (fn-lpc-put 4
                   (fn-lpc-put 8 '((0 0 1 :pin) nil nil nil nil) header)
                   (fn-lpc-put 3 1 (fn-lpc-begin 0 0 :pin))) nil)))
    (mv (and (fn-lhq-ready-p bad-bounds fn-arena)
             (not (fn-lhq-bounds-p bad-bounds))
             (not (fn-lpc-span-bound-p (fn-lhq-field bad-bounds) 0 :pin 8))
             (fn-lhq-bounds-p bad-ready)
             (not (fn-lhq-ready-p bad-ready fn-arena))
             (not (fn-lpc-span-bound-p (fn-lhq-field bad-ready) 0 :pin 0))) fn-arena)))
(defun lhqt-hyp-removal-exec ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (lhqt-hyp-removal-case fn-arena) answer)))
(assert-event (lhqt-hyp-removal-exec))

; Literal source boundary and scheduling teeth. READY is affirmed on the
; positive witness and removed explicitly on the shorter captured-length
; corruption; that corruption reads only valid physical offsets.
(defun lhqt-continuation-case (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((bytes '(88 45 84 101 115 116 58 32 118 13 10 13 10))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arena-seal-list bytes fn-arena))
         (start (fn-lhq-begin 0 (len bytes) :pin '(88 45 84 101 115 116)))
         (bad-ready (fn-lhq-begin 0 5 :pin '(88 45 84 101 115 116))))
    (mv-let (first used-a) (fn-lhq-tick start 1 fn-arena)
      (mv-let (split used-b) (fn-lhq-tick first 2 fn-arena)
        (mv-let (whole used-ab) (fn-lhq-tick start 3 fn-arena)
          (mv-let (wrong used-wrong) (fn-lhq-tick start 4 fn-arena)
            (mv-let (source source-used) (fn-lhq-list-tick bytes 3 start)
              (mv-let (bad bad-used) (fn-lhq-tick bad-ready 8 fn-arena)
                (mv-let (bad-source bad-source-used)
                  (fn-lhq-list-tick bytes 8 bad-ready)
                  (mv (and (fn-lhq-ready-p start fn-arena)
                           (equal split whole) (equal (+ used-a used-b) used-ab)
                           (equal whole source) (equal used-ab source-used)
                           (not (equal wrong whole)) (not (equal used-wrong used-ab))
                           (not (fn-lhq-ready-p bad-ready fn-arena))
                           (not (equal bad bad-source))
                           (not (equal bad-used bad-source-used)))
                      fn-arena))))))))))

(defun lhqt-continuation-exec ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (ok fn-arena) (lhqt-continuation-case fn-arena) ok)))

; Deliberately remove the public READ guard for the corrupt-length witness;
; the positive witness above explicitly establishes that guard.
(assert-event (with-guard-checking :none (lhqt-continuation-exec)))
