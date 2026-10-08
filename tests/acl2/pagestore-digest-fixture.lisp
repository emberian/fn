; Shared concrete digest fixture for pagestore refinement witnesses.
(in-package "ACL2")
(include-book "../../books/pagestore-exec")
(include-book "../../books/pagestore-words-blake3")

(defun pgs-rt-wd (ws)
  (declare (xargs :guard t))
  (pgs-octets-be-nat (fn-blake3 (pgs-words-le-octets ws))))

(defun pgs-rt-rec-words (b)
  ; The sixteen words `pgs-x-write-rec' writes for the body B.
  (declare (xargs :guard (true-listp b)))
  (let ((d (nfix (fifth b))))
    (list *pgs-magic* (pgs-dlo (second b)) (pgs-dlo (third b)) (pgs-dlo (fourth b)) *pgs-page-words* 0 0 0
          (pgs-dlo (pgs-dhi (pgs-dhi (pgs-dhi d)))) (pgs-dlo (pgs-dhi (pgs-dhi d))) (pgs-dlo (pgs-dhi d)) (pgs-dlo d)
          0 0 0 0)))

(defconst *pgs-rt-empty* (pgs-rt-wd (pgs-encode-run nil 1)))   ; the empty table's page

(defun pgs-rt-digest (x)
  ; BLAKE3 of the words the executable hashes for X: a record body's
  ; sixteen words, a table's encoded run (the empty one's precomputed:
  ; every empty slot's validity asks for it), else X as words.
  (declare (xargs :guard t))
  (cond ((null x) *pgs-rt-empty*)
        ((and (true-listp x) (equal (len x) 5) (eq (car x) :pgs-commit))
         (pgs-rt-wd (pgs-rt-rec-words x)))
        ((pgs-ptab-p x) (pgs-rt-wd (pgs-encode-run x (pgs-ptab-run-pages (len x)))))
        (t (pgs-rt-wd x))))

(defattach pgs-digest pgs-rt-digest)

