(in-package "ACL2")
(include-book "../../books/nov-line-projection")
; PRF-1103 / SCN-1015. All cited component theorems are unconditional.
; Their former true-listp accumulator hypothesis was removed only after
; proving the generalized equation; there is no hypothesis-removal case.
(defconst *nlpt-source* '(83 117 98 106 101 99 116 58 32 102 105 114 115 116 13 10 9 99 111 110 116 105 110 117 101 100 13 10 83 117 98 106 101 99 116 58 32 105 103 110 111 114 101 100 13 10 70 114 111 109 58 9 119 114 105 116 101 114 13 10 68 97 116 101 58 32 100 97 116 101 13 10 77 101 115 115 97 103 101 45 73 68 58 32 60 105 100 62 13 10 82 101 102 101 114 101 110 99 101 115 58 32 9 13 10 32 60 112 97 114 101 110 116 62 13 10 13 10 0 255 13 10))
(defconst *nlpt-parsed* (fn-article-parse *nlpt-source*))
(defconst *nlpt-view* (fn-article-result-article *nlpt-parsed*))
; Nonempty reachable positive: literal complete conclusion of the general
; parser accumulator theorem, plus independently expected normalized fields.
(assert-event
 (and (fn-article-result-okp *nlpt-parsed*)
      (equal (fn-novlp-parse-lines *nlpt-source* *fn-article-ceiling-limits*
              (1+ (fn-article-limit-lines *fn-article-ceiling-limits*)) 0 0
              (fn-novlp-columns nil *fn-novlp-names*) nil *fn-novlp-names*)
             (fn-novlp-result
              (fn-article-parse-lines *nlpt-source* *fn-article-ceiling-limits*
               (1+ (fn-article-limit-lines *fn-article-ceiling-limits*))
               0 0 nil nil nil) *fn-novlp-names*))))
(assert-event (equal (fn-novlp-parse *nlpt-source*)
 '(:ok ((102 105 114 115 116 32 99 111 110 116 105 110 117 101 100) (32 119 114 105 116 101 114) (100 97 116 101) (60 105 100 62) (32 32 60 112 97 114 101 110 116 62)))))
; Literal complete conclusion of the five-column composition theorem.
(assert-event
 (equal (fn-novlp-normalize (fn-novlp-columns (fn-article-fields *nlpt-view*) *fn-novlp-names*))
        (list (fn-nov-header-content *nlpt-view* *fn-nov-subject-name*)
              (fn-nov-header-content *nlpt-view* *fn-nov-from-name*)
              (fn-nov-header-content *nlpt-view* *fn-nov-date-name*)
              (fn-nov-header-content *nlpt-view* *fn-nov-message-id-name*)
              (fn-nov-header-content *nlpt-view* *fn-nov-references-name*))))
; Mutation witnesses: last-match replacement and stripping TAB as if it
; were the single initial SP both change the actual observable value.
(assert-event (not (equal (car (cadr (fn-novlp-parse *nlpt-source*))) '(105 103 110 111 114 101 100))))
(assert-event (not (equal (cadr (cadr (fn-novlp-parse *nlpt-source*))) '(119 114 105 116 101 114))))
(assert-event (and (equal (fn-novlp-parse '(82 101 102 101 114 101 110 99 101 115 58 13 10 13 10)) '(:error :invalid-header)) (equal (fn-novlp-parse '(82 101 102 101 114 101 110 99 101 115 58 13 10 13 10)) (fn-novlp-result (fn-article-parse '(82 101 102 101 114 101 110 99 101 115 58 13 10 13 10)) *fn-novlp-names*))))
(assert-event (and (equal (fn-novlp-parse '(83 117 98 106 101 99 116 58 32 120 10 10)) '(:error :invalid-header)) (equal (fn-novlp-parse '(83 117 98 106 101 99 116 58 32 120 10 10)) (fn-novlp-result (fn-article-parse '(83 117 98 106 101 99 116 58 32 120 10 10)) *fn-novlp-names*))))
(assert-event (and (equal (fn-novlp-parse '(83 117 98 106 101 99 116 58 32 120 13 10)) '(:error :missing-separator)) (equal (fn-novlp-parse '(83 117 98 106 101 99 116 58 32 120 13 10)) (fn-novlp-result (fn-article-parse '(83 117 98 106 101 99 116 58 32 120 13 10)) *fn-novlp-names*))))
(assert-event (and (equal (fn-novlp-parse '(9 120 13 10 13 10)) '(:error :invalid-header)) (equal (fn-novlp-parse '(9 120 13 10 13 10)) (fn-novlp-result (fn-article-parse '(9 120 13 10 13 10)) *fn-novlp-names*))))
(assert-event (and (equal (fn-novlp-parse '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 97 10 98)) '(:error :invalid-header)) (equal (fn-novlp-parse '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 97 10 98)) (fn-novlp-result (fn-article-parse '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 97 10 98)) *fn-novlp-names*))))
(assert-event (and (equal (fn-novlp-parse '(83 117 98 106 101 99 116 58 32 0 13 10 13 10)) '(:error :invalid-header)) (equal (fn-novlp-parse '(83 117 98 106 101 99 116 58 32 0 13 10 13 10)) (fn-novlp-result (fn-article-parse '(83 117 98 106 101 99 116 58 32 0 13 10 13 10)) *fn-novlp-names*))))
(assert-event (equal (fn-novlp-parse '(82 101 102 101 114 101 110 99 101 115 58 13 10 32 60 112 97 114 101 110 116 62 13 10 13 10)) '(:ok (nil nil nil nil (60 112 97 114 101 110 116 62)))))
