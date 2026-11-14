; Demand construction controls; actual selected CNS controls are separate.
(in-package "ACL2")
(include-book "../books/attachment-validation")
(assert-event
 (mv-let (err demand count)
  (fn2-av-demand '(if x (quote a) (quote b)) nil (w state))
  (and (not err) (equal count 0)
       (equal demand '(and 't (if x 't 't))))))
(assert-event
 (mv-let (err demand count)
  (fn2-av-demand '((lambda (x) (if x 'a 'b)) y) nil (w state))
  (and (not err) (equal count 0)
       (equal demand '(and (and 't 't)
                           ((lambda (x) (and 't (if x 't 't))) y))))))
(assert-event
 (mv-let (err demand count)
  (fn2-av-demand '(return-last 'mbe1-raw x y) nil (w state))
  (declare (ignore demand count))
  (equal err :unsupported-special)))
(assert-event (not (fn2-av-packet nil (w state))))
