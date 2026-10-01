(in-package "ACL2")
(include-book "../../books/runtime-bootstrap-source")
; Structural tests only. This fixture is NOT an issued compiled capsule.
(defconst *rbst-request*
 (let ((profile '(:runtime-profile profile-source 10000 validation-source)))
  (list :runtime-bootstrap-request-budget-source 'runtime 'image profile
        (list :allocation-epoch-association 'runtime 'image profile 16 1000)
        'allocator-source 'participant-source nil 100 nil
        '((:request post-sample body 12 1))
        '((:request install body 18 1))
        '((:request ats body 30 1))
        '((:request resume body 5 1))
        '((:request rescue body 20 1)) 'roots 'cleanup-source)))
(assert-event
 (and (fn-rbs-sourcep *rbst-request*)
      (fn-rbs-request-budget-sourcep *rbst-request*)
      (not (fn-rbs-physical-sourcep *rbst-request*))))
(assert-event (not (fn-rbs-sourcep (update-nth 8 0 *rbst-request*))))
(assert-event (not (fn-rbs-sourcep (update-nth 8 1000 *rbst-request*))))
(assert-event (not (fn-rbs-sourcep (update-nth 7 1000000 *rbst-request*))))
(assert-event (not (fn-rbs-sourcep (update-nth 9 '(:footprint 1 0 0 0 0) *rbst-request*))))
(assert-event (not (fn-rbs-sourcep (update-nth 10 '((:request post-sample body -1 1)) *rbst-request*))))
