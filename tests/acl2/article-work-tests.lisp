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
; The source preflight runs at the codec ceiling `*fn-article-max-octets*'
; (D27), whose limit branch no test can reach by construction; the served
; paths refuse past the operator's bound first (`fn-inj-decide', the
; injection tests).  Below the ceiling a non-octet reaches octet validation.
(assert-event (equal (fn-aw-v (fn-aw-parse (cons '(not-an-octet)
                                                 (fn-aw-test-repeat 32768 0))))
                     '(:error :invalid-header)))
; The preflight itself refuses one octet past any bound before validation.
(assert-event (not (fn-aw-v (fn-aw-at-most (cons '(not-an-octet)
                                                 (fn-aw-test-repeat 32768 0))
                                           32768))))

; Exact line, physical-header-line, and field-count boundaries.
(defconst *fn-aw-test-max-line*
  (append '(65 58 32) (fn-aw-test-repeat 995 120) '(13 10 13 10)))
(assert-event (fn-article-result-okp (fn-aw-v (fn-aw-parse *fn-aw-test-max-line*))))
(assert-event (equal (fn-aw-v (fn-aw-parse
  (append '(65 58 32) (fn-aw-test-repeat 996 120) '(13 10 13 10)))) '(:error :limit)))
(defconst *fn-aw-test-fold-sample*
  (append '(65 58 32 120 13 10) (fn-aw-test-folds 127) '(13 10 0 255 13 10)))
(assert-event (fn-article-result-okp (fn-aw-v (fn-aw-parse *fn-aw-test-fold-sample*))))
; Retain the 128-line sample for comparable work measurements; exercise the
; current profile's exact 256-line acceptance boundary separately.
(defconst *fn-aw-test-max-folds*
  (append '(65 58 32 120 13 10) (fn-aw-test-folds 255) '(13 10 0 255 13 10)))
(assert-event (equal (len *fn-aw-test-max-folds*) 1032))
(assert-event (fn-article-result-okp (fn-aw-v (fn-aw-parse *fn-aw-test-max-folds*))))
(assert-event (equal (fn-aw-v (fn-aw-parse *fn-aw-test-max-folds*))
                     (fn-article-parse *fn-aw-test-max-folds*)))
(assert-event (equal (fn-aw-v (fn-aw-parse
  (append '(65 58 32 120 13 10) (fn-aw-test-folds 256) '(13 10)))) '(:error :limit)))
(assert-event (fn-article-result-okp (fn-aw-v (fn-aw-parse
  (append (fn-aw-test-fields 64) '(13 10))))))
(assert-event (equal (fn-aw-v (fn-aw-parse
  (append (fn-aw-test-fields 65) '(13 10)))) '(:error :limit)))

; The measured charge and the envelope quoted in specs/article-work.md.
(assert-event (equal (len *fn-aw-test-fold-sample*) 520))
(assert-event (equal (fn-aw-c (fn-aw-parse *fn-aw-test-fold-sample*)) 30195))
(assert-event
 (equal (fn-article-parse-work-budget *fn-aw-test-fold-sample*) 1103275316))
(assert-event
 (<= (fn-aw-c (fn-aw-parse *fn-aw-test-fold-sample*))
     (fn-article-parse-work-budget *fn-aw-test-fold-sample*)))
(assert-event (equal (fn-aw-v (fn-aw-parse *fn-aw-test-fold-sample*))
                     (fn-article-parse *fn-aw-test-fold-sample*)))

; Numeric documentation witnesses for the 256-header-line work bound: at the
; codec ceiling (the certified bound's own figure, 9.0e15 steps) and at the
; development profile's 32 768-octet article bound, which the served paths
; apply before the parse (6.9e10 steps, the pre-D27 figure).
(assert-event
 (equal (+ 3 (* 2 *fn-article-max-octets*)
           (fn-aw-budget (1+ *fn-article-max-header-lines*)
                         *fn-article-max-octets* 0))
        9006794391183396))
(assert-event
 (equal (+ 3 (* 2 32768)
           (fn-aw-budget (1+ *fn-article-max-header-lines*) 32768 0))
        69261680676))
