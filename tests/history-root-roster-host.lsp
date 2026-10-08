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
; The last refresh's status lives in the same table (reserved key :last-refresh):
; a refusal renders its line, a later installed word clears it, the generation
; row survives, and the roster still holds nothing.
(assert-event
 (let* ((state (f-put-global 'fn-owner-history-roots nil state))
        (state (fn-owner-hroot-put 7 '(:live nil nil) state))
        (none (fn-owner-hroot-status-lines state))
        (state (mv-let (erp val state)
                       (fn-owner-hroot-note '(:refused :history-root-reserve-exhausted 4096 0) state)
                  (declare (ignore erp val)) state))
        (refused (fn-owner-hroot-status-lines state))
        (held (fn-history-root-roster-heldp (f-get-global 'fn-owner-history-roots state)))
        (state (mv-let (erp val state) (fn-owner-hroot-note '(:installed 8 7) state)
                  (declare (ignore erp val)) state))
        (cleared (fn-owner-hroot-status-lines state)))
  (mv (and (equal none nil)
           (consp refused)
           (not held)
           (equal cleared nil)
           (equal (fn-owner-hroot-get 7 state) '(:live nil nil))
           (not (boundp-global 'fn-owner-history-root-status state)))
      state))
 :stobjs-out '(nil state))
