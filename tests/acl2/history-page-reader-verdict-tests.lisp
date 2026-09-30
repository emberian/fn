(in-package "ACL2")
(include-book "../../books/history-page-reader-verdict")

(defun fn-hsr-test-shape-equality (count txid words)
  (declare (xargs :guard t :verify-guards nil))
  (equal (fn-hsr-words-okp 0 count txid words)
         (and (pgs-ptab-txids-ok (pgs-decode-table words count) txid)
              (fn-hsr-zero-wordsp (nthcdr (* 6 count) words)))))
(defun fn-hsr-test-dir-equality (rec observed words)
  (declare (xargs :guard t :verify-guards nil))
  (let ((nt (pgs-x-ntables (pgs-rec-npages rec))))
    (equal (fn-hsr-page-verdict
            :directory 0 (pgs-rec-dir-addr rec) (pgs-rec-dir-digest rec)
            observed (not (fn-hsr-words-okp 0 nt (pgs-rec-txid rec) words)))
           (or (pgs-dir-verdict rec (pgs-decode-table words nt) observed)
               (if (fn-hsr-zero-wordsp (nthcdr (* 6 nt) words)) nil
                 (list :dir-malformed (pgs-rec-dir-addr rec)))))))
(defun fn-hsr-test-table-equality (entry rem txid tp observed words)
  (declare (xargs :guard t :verify-guards nil))
  (let ((count (min 341 (nfix rem))))
    (equal (fn-hsr-page-verdict
            :table tp (first entry) (third entry) observed
            (not (fn-hsr-words-okp 0 count txid words)))
           (cond ((equal (pgs-entry-verdict entry txid :eager observed) :damaged)
                  (list :table-damaged tp (first entry)))
                 ((not (fn-hsr-zero-wordsp (nthcdr (* 6 count) words)))
                  (list :table-malformed tp))
                 ((not (pgs-table-ok (pgs-decode-table words count) rem txid))
                  (list :table-malformed tp))
                 (t nil)))))

(defconst *fn-hsr-vwords* (pgs-encode-table '((123 5 99) (456 4 87))))
(defconst *fn-hsr-vroot* '(:pgs-commit 5 4567 342 99 0))
; All three literal theorem antecedents/conclusions, on nonempty current bytes.
(assert-event
 (and (natp 2) (natp 5) (nat-listp *fn-hsr-vwords*)
      (fn-hsr-test-shape-equality 2 5 *fn-hsr-vwords*)
      (fn-hsr-words-okp 0 2 5 *fn-hsr-vwords*)))
(assert-event
 (and (nat-listp *fn-hsr-vwords*)
      (fn-hsr-test-dir-equality *fn-hsr-vroot* 99 *fn-hsr-vwords*)
      (not (fn-hsr-page-verdict :directory 0 4567 99 99 nil))))
(assert-event
 (and (natp 5) (nat-listp *fn-hsr-vwords*)
      (fn-hsr-test-table-equality '(8000 5 42) 2 5 7 42 *fn-hsr-vwords*)
      (not (fn-hsr-page-verdict :table 7 8000 42 42 nil))))
; Digest failure keeps its existing priority over malformed data.
(assert-event
 (and (equal (fn-hsr-page-verdict :directory 0 4567 99 100 t) '(:dir-damaged 4567))
      (equal (fn-hsr-page-verdict :directory 0 4567 99 99 t) '(:dir-malformed 4567))
      (equal (fn-hsr-page-verdict :table 7 8000 42 43 t) '(:table-damaged 7 8000))
      (equal (fn-hsr-page-verdict :table 7 8000 42 42 t) '(:table-malformed 7))
      (equal (fn-hsr-page-verdict :data 11 9000 32 33 nil) '(:page-damaged 11 9000))))
; Missing words are zero-padded by the old logical decoder: the length premise
; was proved redundant and removed; I/O completion separately requires 16KiB.
(assert-event
 (and (natp 2) (natp 5) (nat-listp '(123))
      (fn-hsr-test-shape-equality 2 5 '(123))
      (fn-hsr-test-dir-equality *fn-hsr-vroot* 99 '(123))
      (fn-hsr-test-table-equality '(8000 5 42) 2 5 7 42 '(123))))
; Literal hypothesis removals: all retained antecedents hold.
(assert-event
 (with-guard-checking :none
   (let ((count 1/2) (txid 0) (words '(0 1 0 0 0 0)))
     (and (not (natp count)) (natp txid) (nat-listp words)
          (not (fn-hsr-test-shape-equality count txid words))))))
(assert-event
 (with-guard-checking :none
   (let ((count 1) (txid -1) (words '(0 0 0 0 0 0)))
     (and (natp count) (not (natp txid)) (nat-listp words)
          (not (fn-hsr-test-shape-equality count txid words))))))
(assert-event
 (with-guard-checking :none
   (let ((count 1) (txid 0) (words '(0 1/2 0 0 0 0)))
     (and (natp count) (natp txid) (not (nat-listp words))
          (not (fn-hsr-test-shape-equality count txid words))))))
(assert-event
 (with-guard-checking :none
   (let ((words '(0 1/2 0 0 0 0)))
     (and (not (nat-listp words))
          (not (fn-hsr-test-dir-equality '(:pgs-commit 0 4567 1 99 0) 99 words))))))
(assert-event
 (with-guard-checking :none
   (let ((txid -1) (words '(0 0 0 0 0 0)))
     (and (not (natp txid)) (nat-listp words)
          (not (fn-hsr-test-table-equality '(8000 5 42) 1 txid 7 42 words))))))
(assert-event
 (with-guard-checking :none
   (let ((txid 0) (words '(0 1/2 0 0 0 0)))
     (and (natp txid) (not (nat-listp words))
          (not (fn-hsr-test-table-equality '(8000 5 42) 1 txid 7 42 words))))))
