; Terminal root publication metadata contains only retained generations.
(in-package "ACL2")
(include-book "../../host/history-root-host")
(assert-event
 (let* ((state (fn-owner-hroot-put 81 '(:retired nil nil) state))
        (present (fn-owner-hroot-get 81 state))
        (state (fn-owner-hroot-put 81 nil state)))
  (mv (and (equal present '(:retired nil nil))
           (equal (fn-owner-hroot-get 81 state) nil)
           (not (assoc-equal 81 (f-get-global 'fn-owner-history-roots state)))) state))
 :stobjs-out '(nil state))
