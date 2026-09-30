(in-package "ACL2")
(include-book "../../books/history-page-reader")

(defun fn-hsr-test-run (words c)
  (declare (xargs :guard t :measure (len words)))
  (if (consp words)
      (mv-let (v next) (fn-hsr-scan-word (car words) c)
        (if (equal v :continue) (fn-hsr-test-run (cdr words) next) c))
    c))

(defun fn-hsr-test-tracep (words c)
  (declare (xargs :guard t :verify-guards nil :measure (len words)))
  (if (consp words)
      (let ((word (car words)) (rest (cdr words)))
        (mv-let (v next) (fn-hsr-scan-word word c)
          (and (fn-hsr-scan-invariantp c)
               (< (fn-hsr-field 0 c) (fn-hsr-field 1 c))
               (unsigned-byte-p 64 word)
               (equal v :continue) (fn-hsr-scan-invariantp next)
               (equal (fn-hsr-field 0 next) (+ 1 (fn-hsr-field 0 c)))
               (equal (fn-hsr-field 1 next) (fn-hsr-field 1 c))
               (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
               (equal (fn-hsr-field 3 next) (fn-hsr-field 3 c))
               (equal (fn-hsr-field 4 next) (fn-hsr-field 4 c))
               (equal (fn-hsr-field 7 next) (fn-hsr-field 7 c))
               (equal (fn-hsr-field 8 next) (fn-hsr-field 8 c))
               (equal (append (fn-hsr-field 5 c)
                              (fn-hsr-selected-rest (fn-hsr-field 0 c) (fn-hsr-field 3 c) words))
                      (append (fn-hsr-field 5 next)
                              (fn-hsr-selected-rest (fn-hsr-field 0 next) (fn-hsr-field 3 next) rest)))
               (equal (or (fn-hsr-field 6 c)
                          (not (fn-hsr-words-okp (fn-hsr-field 0 c) (fn-hsr-field 2 c)
                                                 (fn-hsr-field 4 c) words)))
                      (or (fn-hsr-field 6 next)
                          (not (fn-hsr-words-okp (fn-hsr-field 0 next) (fn-hsr-field 2 next)
                                                 (fn-hsr-field 4 next) rest))))
               (fn-hsr-test-tracep rest next))))
    (and (fn-hsr-scan-invariantp c)
         (equal (fn-hsr-field 0 c) (fn-hsr-field 1 c))
         (equal (len (fn-hsr-field 5 c)) 6)
         (equal (fn-hsr-scan-entry c) (pgs-decode-entry (fn-hsr-field 5 c))))))

(defconst *fn-hsr-test-entry* '(77 9 123456789012345678901234567890))
(defconst *fn-hsr-test-words* (append (pgs-entry-words *fn-hsr-test-entry*) '(0 0)))
(defconst *fn-hsr-test-begin* (fn-hsr-scan-begin 8 1 0 10 '(:root 31) '(:borrow 17)))

; Complete literal initial antecedents and conclusion, not an empty scan.
(assert-event
 (and (unsigned-byte-p 64 8) (unsigned-byte-p 64 1)
      (unsigned-byte-p 64 0) (unsigned-byte-p 64 10)
      (<= (* 6 1) 8) (< 0 1)
      (fn-hsr-scan-invariantp *fn-hsr-test-begin*)))
(assert-event (fn-hsr-test-tracep *fn-hsr-test-words* *fn-hsr-test-begin*))
(assert-event
 (let ((last (fn-hsr-test-run *fn-hsr-test-words* *fn-hsr-test-begin*)))
   (and (equal (fn-hsr-scan-entry last) *fn-hsr-test-entry*)
        (not (fn-hsr-field 6 last)))))

(defun fn-hsr-test-codec-conclusion (selected count words)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (len (ec-call (fn-hsr-selected-rest 0 selected words))) 6)
       (equal (pgs-decode-entry (ec-call (fn-hsr-selected-rest 0 selected words)))
              (ec-call (nth selected (ec-call (pgs-decode-table words count)))))))
(assert-event
 (and (natp 0) (natp 1) (< 0 1) (<= (+ 6 (* 6 0)) (len *fn-hsr-test-words*))
      (fn-hsr-test-codec-conclusion 0 1 *fn-hsr-test-words*)))

; Actual directory codec: entry341 starts at2046 and straddles the16KiB page
; boundary. One scan continuation spans both page reads and retains six words.
(defun fn-hsr-test-repeat (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons x (fn-hsr-test-repeat (1- n) x))))
(defconst *fn-hsr-cross-entries*
  (append (fn-hsr-test-repeat 341 '(100 9 17)) (list *fn-hsr-test-entry*)))
(defconst *fn-hsr-cross-words* (pgs-encode-run *fn-hsr-cross-entries* 2))
(assert-event
 (let* ((begin (fn-hsr-scan-begin 4096 342 341 10 :root :borrow))
        (first (fn-hsr-test-run (take 2048 *fn-hsr-cross-words*) begin))
        (last (fn-hsr-test-run (nthcdr 2048 *fn-hsr-cross-words*) first)))
   (and (fn-hsr-scan-invariantp begin) (fn-hsr-scan-invariantp first)
        (equal (len (fn-hsr-field 5 first)) 2)
        (fn-hsr-scan-invariantp last)
        (equal (fn-hsr-scan-entry last) *fn-hsr-test-entry*)
        (not (fn-hsr-field 6 last))
        (natp 341) (natp 342) (< 341 342)
        (<= (+ 6 (* 6 341)) (len *fn-hsr-cross-words*))
        (fn-hsr-test-codec-conclusion 341 342 *fn-hsr-cross-words*))))

; A bad txid in an unselected entry is latched too; selected entry stays exact.
(assert-event
 (let* ((words (pgs-encode-run (list '(100 11 17) *fn-hsr-test-entry*) 1))
        (last (fn-hsr-test-run words (fn-hsr-scan-begin 2048 2 1 10 :root :borrow))))
   (and (fn-hsr-scan-invariantp last) (fn-hsr-field 6 last)
        (equal (fn-hsr-scan-entry last) *fn-hsr-test-entry*))))
; Nonzero trailing padding is malformed, never ignored.
(assert-event
 (let ((last (fn-hsr-test-run (append (pgs-entry-words *fn-hsr-test-entry*) '(0 1))
                             *fn-hsr-test-begin*)))
   (and (fn-hsr-scan-invariantp last) (fn-hsr-field 6 last)
        (equal (fn-hsr-scan-entry last) *fn-hsr-test-entry*))))

(defun fn-hsr-test-progress-conclusion (word c)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v next) (fn-hsr-scan-word word c)
    (and (equal v :continue) (fn-hsr-scan-invariantp next)
         (equal (fn-hsr-field 0 next) (+ 1 (fn-hsr-field 0 c)))
         (equal (fn-hsr-field 1 next) (fn-hsr-field 1 c))
         (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
         (equal (fn-hsr-field 3 next) (fn-hsr-field 3 c))
         (equal (fn-hsr-field 4 next) (fn-hsr-field 4 c)))))
(defun fn-hsr-test-selection-conclusion (word c rest)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v next) (fn-hsr-scan-word word c)
    (declare (ignore v))
    (equal (append (fn-hsr-field 5 c)
                   (fn-hsr-selected-rest (fn-hsr-field 0 c) (fn-hsr-field 3 c) (cons word rest)))
           (append (fn-hsr-field 5 next)
                   (fn-hsr-selected-rest (fn-hsr-field 0 next) (fn-hsr-field 3 next) rest)))))
(defun fn-hsr-test-verdict-conclusion (word c rest)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v next) (fn-hsr-scan-word word c)
    (declare (ignore v))
    (equal (or (fn-hsr-field 6 c)
               (not (fn-hsr-words-okp (fn-hsr-field 0 c) (fn-hsr-field 2 c)
                                      (fn-hsr-field 4 c) (cons word rest))))
           (or (fn-hsr-field 6 next)
               (not (fn-hsr-words-okp (fn-hsr-field 0 next) (fn-hsr-field 2 next)
                                      (fn-hsr-field 4 next) rest))))))

; Literal hypothesis removals below are argument/cursor mutations, not claims
; that the composed reader can reach corrupted metadata.

(assert-event
 (let ((total (expt 2 64)) (count 1) (selected 0) (txid 9))
   (and (not (unsigned-byte-p 64 total))
        (unsigned-byte-p 64 count)
        (unsigned-byte-p 64 selected)
        (unsigned-byte-p 64 txid)
        (<= (* 6 count) total)
        (< selected count)
        (not (fn-hsr-scan-invariantp (fn-hsr-scan-begin total count selected txid :c :l))))))

(assert-event
 (let ((total 12) (count 3/2) (selected 0) (txid 9))
   (and (unsigned-byte-p 64 total)
        (not (unsigned-byte-p 64 count))
        (unsigned-byte-p 64 selected)
        (unsigned-byte-p 64 txid)
        (<= (* 6 count) total)
        (< selected count)
        (not (fn-hsr-scan-invariantp (fn-hsr-scan-begin total count selected txid :c :l))))))

(assert-event
 (let ((total 6) (count 1) (selected -1) (txid 9))
   (and (unsigned-byte-p 64 total)
        (unsigned-byte-p 64 count)
        (not (unsigned-byte-p 64 selected))
        (unsigned-byte-p 64 txid)
        (<= (* 6 count) total)
        (< selected count)
        (not (fn-hsr-scan-invariantp (fn-hsr-scan-begin total count selected txid :c :l))))))

(assert-event
 (let ((total 6) (count 1) (selected 0) (txid -1))
   (and (unsigned-byte-p 64 total)
        (unsigned-byte-p 64 count)
        (unsigned-byte-p 64 selected)
        (not (unsigned-byte-p 64 txid))
        (<= (* 6 count) total)
        (< selected count)
        (not (fn-hsr-scan-invariantp (fn-hsr-scan-begin total count selected txid :c :l))))))

(assert-event
 (let ((total 5) (count 1) (selected 0) (txid 9))
   (and (unsigned-byte-p 64 total)
        (unsigned-byte-p 64 count)
        (unsigned-byte-p 64 selected)
        (unsigned-byte-p 64 txid)
        (not (<= (* 6 count) total))
        (< selected count)
        (not (fn-hsr-scan-invariantp (fn-hsr-scan-begin total count selected txid :c :l))))))

(assert-event
 (let ((total 6) (count 1) (selected 1) (txid 9))
   (and (unsigned-byte-p 64 total)
        (unsigned-byte-p 64 count)
        (unsigned-byte-p 64 selected)
        (unsigned-byte-p 64 txid)
        (<= (* 6 count) total)
        (not (< selected count))
        (not (fn-hsr-scan-invariantp (fn-hsr-scan-begin total count selected txid :c :l))))))

(assert-event
 (let ((selected -1) (count 1) (words (fn-hsr-test-repeat 6 0)))
   (and (not (natp selected))
        (natp count)
        (< selected count)
        (<= (+ 6 (* 6 selected)) (len words))
        (not (with-guard-checking :none (fn-hsr-test-codec-conclusion selected count words))))))

(assert-event
 (let ((selected 0) (count 1/2) (words (fn-hsr-test-repeat 6 0)))
   (and (natp selected)
        (not (natp count))
        (< selected count)
        (<= (+ 6 (* 6 selected)) (len words))
        (not (with-guard-checking :none (fn-hsr-test-codec-conclusion selected count words))))))

(assert-event
 (let ((selected 0) (count 0) (words (fn-hsr-test-repeat 6 0)))
   (and (natp selected)
        (natp count)
        (not (< selected count))
        (<= (+ 6 (* 6 selected)) (len words))
        (not (with-guard-checking :none (fn-hsr-test-codec-conclusion selected count words))))))

(assert-event
 (let ((selected 0) (count 1) (words (fn-hsr-test-repeat 5 0)))
   (and (natp selected)
        (natp count)
        (< selected count)
        (not (<= (+ 6 (* 6 selected)) (len words)))
        (not (with-guard-checking :none (fn-hsr-test-codec-conclusion selected count words))))))

(assert-event
 (let ((c '(0 6 1 0 9 (0) nil :c :l)) (word 1))
   (and (not (fn-hsr-scan-invariantp c))
        (< (fn-hsr-field 0 c) (fn-hsr-field 1 c))
        (unsigned-byte-p 64 word)
        (not (fn-hsr-test-progress-conclusion word c)))))

(assert-event
 (let ((c '(6 6 1 0 9 (0 0 0 0 0 0) nil :c :l)) (word 1))
   (and (fn-hsr-scan-invariantp c)
        (not (< (fn-hsr-field 0 c) (fn-hsr-field 1 c)))
        (unsigned-byte-p 64 word)
        (not (fn-hsr-test-progress-conclusion word c)))))

(assert-event
 (let ((c '(0 6 1 0 9 nil nil :c :l)) (word -1))
   (and (fn-hsr-scan-invariantp c)
        (< (fn-hsr-field 0 c) (fn-hsr-field 1 c))
        (not (unsigned-byte-p 64 word))
        (not (fn-hsr-test-progress-conclusion word c)))))

(assert-event
 (let ((c '(1 6 1 0 9 (0 0 0 0 0 0) nil :c :l)) (word 10))
   (and (not (fn-hsr-scan-invariantp c))
        (< (fn-hsr-field 0 c) (fn-hsr-field 1 c))
        (unsigned-byte-p 64 word)
        (not (fn-hsr-test-verdict-conclusion word c nil)))))

(assert-event
 (let ((c '(6 6 1 0 9 (0 0 0 0 0 0) nil :c :l)) (word 1))
   (and (fn-hsr-scan-invariantp c)
        (not (< (fn-hsr-field 0 c) (fn-hsr-field 1 c)))
        (unsigned-byte-p 64 word)
        (not (fn-hsr-test-verdict-conclusion word c nil)))))

(assert-event
 (let ((c '(1 6 1 0 9 (0) nil :c :l)) (word (expt 2 64)))
   (and (fn-hsr-scan-invariantp c)
        (< (fn-hsr-field 0 c) (fn-hsr-field 1 c))
        (not (unsigned-byte-p 64 word))
        (not (fn-hsr-test-verdict-conclusion word c nil)))))
(assert-event
 (let ((c '(0 6 1 0 9 (0 0 0 0 0 0) nil :c :l)) (word 1))
   (and (not (fn-hsr-scan-invariantp c)) (unsigned-byte-p 64 word)
        (not (fn-hsr-test-selection-conclusion word c nil)))))
(assert-event
 (let ((c '(0 6 1 0 9 nil nil :c :l)) (word -1))
   (and (fn-hsr-scan-invariantp c) (not (unsigned-byte-p 64 word))
        (not (fn-hsr-test-selection-conclusion word c nil)))))
(assert-event
 (let ((c '(6 6 1 0 9 nil nil :c :l)))
   (and (not (fn-hsr-scan-invariantp c))
        (equal (fn-hsr-field 0 c) (fn-hsr-field 1 c))
        (not (and (equal (len (fn-hsr-field 5 c)) 6)
                  (equal (fn-hsr-scan-entry c) (pgs-decode-entry (fn-hsr-field 5 c))))))))
(assert-event
 (let ((c '(0 6 1 0 9 nil nil :c :l)))
   (and (fn-hsr-scan-invariantp c)
        (not (equal (fn-hsr-field 0 c) (fn-hsr-field 1 c)))
        (not (and (equal (len (fn-hsr-field 5 c)) 6)
                  (equal (fn-hsr-scan-entry c) (pgs-decode-entry (fn-hsr-field 5 c))))))))
(assert-event
 (let ((c '(bad 6 1 0 9 nil nil :captured :borrow)))
   (mv-let (v next) (fn-hsr-scan-word 1 c)
     (and (equal v '(:refused :scan-word))
          (equal (fn-hsr-field 7 next) (fn-hsr-field 7 c))
          (equal (fn-hsr-field 8 next) (fn-hsr-field 8 c))))))
