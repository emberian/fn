; Terminal root publication metadata contains only retained generations.
; Not a book: host/history-root-host.lisp is ld-only (it sits on host/owner-host.lisp).
; Run by tests/test_history_root_roster_host.py through
; tests/owner_feed_connection_host_check.py, which loads host/owner-host.lisp first.
(in-package "ACL2")
(ld "../host/history-root-host.lisp" :ld-error-action :error)
(assert-event
 (let* ((state (fn-owner-hroot-put 81 '(:retired nil nil) state))
        (present (fn-owner-hroot-get 81 state))
        (state (fn-owner-hroot-put 81 nil state)))
  (mv (and (equal present '(:retired nil nil))
           (equal (fn-owner-hroot-get 81 state) nil)
           (not (assoc-equal 81 (f-get-global 'fn-owner-history-roots state)))) state))
 :stobjs-out '(nil state))
