; The denominator is checked against live declarations, including late arms.
(in-package "ACL2")
(include-book "../books/translation-validation")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-tv-kind-run-idle-children (x) (declare (ignore x)) 0)
(defun fn2-tv-kind-on-result-children (x) (declare (ignore x)) 1)
(table fn2-machine-kinds 'fn2-tv-kind
       '(:arms ((:idle (:idle))) :observe-arms ((:result (:nowake)))))

(fn2-tv-check-arm-inventory
 '((fn2-tv-kind :arms :idle :children fn2-tv-kind-run-idle-children fn2-tv-kind-run-idle ((:idle)) nil)
   (fn2-tv-kind :observe-arms :result :children fn2-tv-kind-on-result-children fn2-tv-kind-on-result ((:nowake)) nil)))

; Dropping a handler must not improve the coverage denominator.
(must-fail
 (fn2-tv-check-arm-inventory
  '((fn2-tv-kind :arms :idle :children fn2-tv-kind-run-idle-children fn2-tv-kind-run-idle ((:idle)) nil))))

(table fn2-machine-arm-bodies 'fn2-tv-kind '(:arms ((:ready (:yield)))))
; The prior export cannot stand in for a new late declaration.
(must-fail
 (fn2-tv-check-arm-inventory
  '((fn2-tv-kind :arms :idle :children fn2-tv-kind-run-idle-children fn2-tv-kind-run-idle ((:idle)) nil)
    (fn2-tv-kind :observe-arms :result :children fn2-tv-kind-on-result-children fn2-tv-kind-on-result ((:nowake)) nil))))

(fn2-tv-check-arm-inventory
 '((fn2-tv-kind :arms :ready :core fn2-tv-kind-run-ready fn2-tv-kind-run-ready ((:yield)) nil)
   (fn2-tv-kind :observe-arms :result :core fn2-tv-kind-on-result fn2-tv-kind-on-result ((:nowake)) nil)))

(defun fn2-tv-outer (x) (fn2-tv-kind-run-idle-children x))
(make-event
 (if (not (fn2-tv-matches-function (fn2-tv-function 'fn2-tv-missing (w state))
                                  'fn2-tv-missing (w state)))
     '(value-triple :nonfunction-export-rejected)
   (er soft 'closure-control "A nonexistent function was counted as an export.")))
(make-event
 `(fn2-tv-check-functions
   ',(list (cons 'fn2-tv-outer (fn2-tv-function 'fn2-tv-outer (w state))))))
(make-event
 `(must-fail
   (fn2-tv-check-functions
    ',(list (cons 'fn2-tv-outer
                  (update-nth 7 (fn2-tv-object nil)
                              (fn2-tv-function 'fn2-tv-outer (w state))))))))
(make-event
 (if (and (fn2-tv-closed-functions '(fn2-tv-outer fn2-tv-kind-run-idle-children)
                                  '(fn2-tv-outer fn2-tv-kind-run-idle-children) (w state))
          (not (fn2-tv-closed-functions '(fn2-tv-outer) '(fn2-tv-outer) (w state)))
          (not (fn2-tv-refused-functions '(fn2-tv-outer) (w state))))
     '(value-triple :missing-callee-and-false-refusal-rejected)
   (er soft 'closure-control "Closure omitted a live callee or accepted a false refusal.")))

; Packed strings must reconstruct the exact canonical symbol, including its
; package. Changing the package or name is not a compression equivalence.
(make-event
 `(fn2-tv-check-packed-functions
   ',(list (cons 'fn2-tv-outer
                 (update-nth 1 '(:packed-symbol "ACL2" "FN2-TV-OUTER")
                             (fn2-tv-function 'fn2-tv-outer (w state)))))))
(make-event
 `(must-fail
   (fn2-tv-check-packed-functions
    ',(list (cons 'fn2-tv-outer
                  (update-nth 1 '(:packed-symbol "COMMON-LISP" "FN2-TV-OUTER")
                              (fn2-tv-function 'fn2-tv-outer (w state))))))))
(make-event
 `(must-fail
   (fn2-tv-check-packed-functions
    ',(list (cons 'fn2-tv-outer
                  (update-nth 1 '(:packed-symbol "ACL2" "FN2-TV-OTHER")
                              (fn2-tv-function 'fn2-tv-outer (w state))))))))
