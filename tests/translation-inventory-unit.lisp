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
