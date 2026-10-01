(in-package "ACL2")
(include-book "../../books/runtime-operation-compiled-source")
; Complete literal readouts, not positive runtime authority fixtures.
(assert-event
 (mv-let (status family roles prs)
  (fn-runtime-operation-compiled-source :owner-control-inspect)
  (equal (list status family roles prs)
         '(:runtime-operation-unavailable nil nil nil))))
(assert-event
 (mv-let (status coordinate) (fn-runtime-operation-compiled-coordinate)
  (equal (list status coordinate) '(:runtime-operation-unavailable nil))))
; Mutation: supplying a family-shaped object as KIND cannot install a row.
(assert-event
 (mv-let (status family roles prs)
  (fn-runtime-operation-compiled-source
   '(:runtime-operation-family :owner-control-inspect :runtime :image
     :profile :pool :source nil nil nil nil nil nil nil nil))
  (equal (list status family roles prs)
         '(:runtime-operation-unavailable nil nil nil))))
; Representation-only assembly preserves all six distinct request streams and
; the original retained/cleanup slots. It confers no status or admission.
(assert-event
 (equal (fn-roc-family :kind :runtime :image :profile :association :source
                       :primary :caller :firstuse :collector :external :control
                       :retained :cleanup)
        '(:runtime-operation-family :kind :runtime :image :profile :association
          :source :primary :caller :firstuse :collector :external :control
          :retained :cleanup)))

(assert-event
 (mv-let (word bytes)
  (fn-runtime-operation-compiled-body-cost :owner-control-inspect
                                           '(:forged-request) '(:forged-cache))
  (and (eq word :runtime-operation-unavailable) (equal bytes nil))))

(assert-event (equal (fn-runtime-operation-compiled-kinds) nil))
(assert-event
 (mv-let (status slot) (fn-runtime-operation-compiled-slot :recovery-file-issue)
  (and (equal status :runtime-operation-unavailable) (null slot))))

; Representation-only mapping tests, not protocol readiness evidence.
(assert-event
 (let* ((rows '((:owner-control-inspect :owner-control)
                (:account-adoption :owner-control)
                (:recovery-file-issue :recovery-file-issue)))
        (roles (fn-roc-executor-kinds rows)))
  (and (equal roles '(:owner-control :recovery-file-issue))
       (equal (fn-roc-operation-slots rows (fn-roc-slot-rows roles 0))
              '((:owner-control-inspect 0) (:account-adoption 0)
                (:recovery-file-issue 1))))))
(assert-event (equal (fn-roc-operation-slots nil '((:owner-control 0))) nil))
