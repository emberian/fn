; Metadata MODEL only; no issued runtime authority or semantic execution.
(in-package "ACL2")
(include-book "../../books/admission-preparation-intent")
(defconst *fn-api-model-base*
 '(:ready 3 7 original-context field-carries cp7 cp-carries 0 0 (3 (7 9) 0 0)))
(defconst *fn-api-model-current*
 (list '(:admission-grant 11 3 7 7 9 :identity) '(1 0 0 0 1)
       :reserved *fn-api-model-base* nil))
(assert-event
 (and (fn-api-current-coordinatesp *fn-api-model-current* *fn-api-model-base*
                                  3 7 :record-staged 7 9)
      (not (fn-api-current-coordinatesp *fn-api-model-current* *fn-api-model-base*
                                       3 7 :record-staged 7 10))
      (not (fn-api-current-coordinatesp *fn-api-model-current* *fn-api-model-base*
                                       3 7 :record-attempted 7 9))))
(assert-event
 (not (fn-api-current-coordinatesp
        *fn-api-model-current*
        '(:ready 3 7 original-context field-carries cp7 cp-carries 0 0 (3 (7 10) 0 0))
        3 7 :record-staged 7 9)))

(assert-event
 (and (fn-api-reserved-coordinatesp *fn-api-model-current* *fn-api-model-base*
                                   3 7 :reserved 7 9)
      (not (fn-api-reserved-coordinatesp *fn-api-model-current* *fn-api-model-base*
                                        3 7 :record-staged 7 9))))
