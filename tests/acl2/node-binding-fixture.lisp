; Explicit abstract test descriptor, not a production profile selection.
(in-package "ACL2")
(include-book "../../books/acceptance-binding")
(defconst *nbft-binding*
  (fn-ab-make :relay-v1
    (append *fn-ab-subject-head* (make-list 32 :initial-element 0))))
(assert-event (fn-ab-p *nbft-binding*))
