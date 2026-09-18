; Work accounting regression vectors; the general bound is in the included book.
(in-package "ACL2")
(include-book "../../books/article-public-bound")

(defun fn-aw-test-repeat (n value)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil (cons value (fn-aw-test-repeat (1- n) value))))
(defun fn-aw-test-folds (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (append '(32 120 13 10) (fn-aw-test-folds (1- n)))))
(defun fn-aw-test-fields (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (append '(65 58 32 120 13 10) (fn-aw-test-fields (1- n)))))

; Empty article, malformed atoms, improper spines and nested non-octets.
(assert-event (equal (fn-aw-parse nil) '((:error :missing-separator) 6)))
(assert-event (equal (fn-aw-parse 7) '((:error :invalid-header) 3)))
(assert-event (equal (fn-aw-parse '(13 10 . bad)) '((:error :invalid-header) 7)))
(assert-event (equal (fn-aw-parse '((1))) '((:error :invalid-header) 4)))
(assert-event (equal (fn-aw-c (fn-aw-parse '(13 10))) 15))
(assert-event (fn-article-result-okp (fn-aw-v (fn-aw-parse '(13 10)))))
(assert-event (equal (fn-aw-c (fn-aw-parse (list (fn-aw-test-repeat 2000 1)))) 4))

; Prefix copies are charged by the old prefix, independently of the appended tail.
(assert-event
 (equal (fn-aw-c (fn-aw-add-fold '(((65) (66)) (97) (32 120 32 121)) '(32 122))) 9))
(assert-event (equal (fn-aw-c (fn-aw-header-add nil '(65 58 32 120))) 14))

; Exact source preflight boundary, including rejection before octet validation.
(defconst *fn-aw-test-max-source* (append '(13 10) (fn-aw-test-repeat 32766 0)))
(assert-event (fn-article-result-okp (fn-aw-v (fn-aw-parse *fn-aw-test-max-source*))))
(assert-event (equal (fn-aw-parse (cons '(not-an-octet) (fn-aw-test-repeat 32768 0)))
                     '((:error :limit) 32770)))

; Exact line, physical-header-line, and field-count boundaries.
(defconst *fn-aw-test-max-line*
  (append '(65 58 32) (fn-aw-test-repeat 995 120) '(13 10 13 10)))
(assert-event (fn-article-result-okp (fn-aw-v (fn-aw-parse *fn-aw-test-max-line*))))
(assert-event (equal (fn-aw-v (fn-aw-parse
  (append '(65 58 32) (fn-aw-test-repeat 996 120) '(13 10 13 10)))) '(:error :limit)))
(defconst *fn-aw-test-max-folds*
  (append '(65 58 32 120 13 10) (fn-aw-test-folds 127) '(13 10 0 255 13 10)))
(assert-event (fn-article-result-okp (fn-aw-v (fn-aw-parse *fn-aw-test-max-folds*))))
(assert-event (equal (fn-aw-v (fn-aw-parse
  (append '(65 58 32 120 13 10) (fn-aw-test-folds 128) '(13 10)))) '(:error :limit)))
(assert-event (fn-article-result-okp (fn-aw-v (fn-aw-parse
  (append (fn-aw-test-fields 64) '(13 10))))))
(assert-event (equal (fn-aw-v (fn-aw-parse
  (append (fn-aw-test-fields 65) '(13 10)))) '(:error :limit)))

(assert-event
 (<= (fn-aw-c (fn-aw-parse *fn-aw-test-max-folds*))
     (fn-article-parse-work-budget *fn-aw-test-max-folds*)))
(assert-event (equal (fn-aw-v (fn-aw-parse *fn-aw-test-max-folds*))
                     (fn-article-parse *fn-aw-test-max-folds*)))
