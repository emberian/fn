(in-package "ACL2")
(include-book "../../host/page-read-host")
(include-book "std/testing/assert-bang" :dir :system)

(assert-event
 (and (eq (symbol-class 'fn-owner-page-read-install (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-read-register (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-read-admit (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-read-settle (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-cache-evict (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-read-close (w state)) :common-lisp-compliant)))

(defun prh-run (fn-page-read-pool)
  (declare (xargs :mode :program :stobjs fn-page-read-pool))
  (mv-let (absent token0 fn-page-read-pool)
    (fn-owner-page-read-admit 7 11 200 64 999 fn-page-read-pool)
    (mv-let (installed fn-page-read-pool)
      (fn-owner-page-read-install '(10000 0 2 1 10) 8 3000 4 fn-page-read-pool)
      (mv-let (registered fn-page-read-pool)
        (fn-owner-page-read-register 11 fn-page-read-pool)
        (mv-let (admitted token fn-page-read-pool)
          (fn-owner-page-read-admit 7 11 200 64 999 fn-page-read-pool)
          (let ((issued (fn-owner-page-read-ledger fn-page-read-pool)))
            (mv-let (refused token1 fn-page-read-pool)
              (fn-owner-page-read-admit 8 11 200 64 999 fn-page-read-pool)
              (let ((same-refusal (equal issued (fn-owner-page-read-ledger fn-page-read-pool))))
                (mv-let (settled fn-page-read-pool)
                  (fn-owner-page-read-settle token t fn-page-read-pool)
                  (let ((cached (fn-owner-page-read-ledger fn-page-read-pool)))
                    (mv-let (duplicate fn-page-read-pool)
                      (fn-owner-page-read-settle token t fn-page-read-pool)
                      (mv-let (held fn-page-read-pool)
                        (fn-owner-page-read-close 11 fn-page-read-pool)
                        (mv-let (evicted fn-page-read-pool)
                          (fn-owner-page-cache-evict token fn-page-read-pool)
                          (mv-let (closed fn-page-read-pool)
                            (fn-owner-page-read-close 11 fn-page-read-pool)
                            (mv-let (reinstall fn-page-read-pool)
                              (fn-owner-page-read-install '(10000 0 2 1 10) 8 3000 4 fn-page-read-pool)
                              (mv (list absent token0 installed registered admitted token
                                        refused token1 same-refusal settled
                                        (fn-prl-nth 1 cached) duplicate held evicted closed reinstall
                                        (fn-prl-nth 1 (fn-owner-page-read-ledger fn-page-read-pool))
                                        (fn-prl-nth 2 (fn-owner-page-read-ledger fn-page-read-pool)))
                                  fn-page-read-pool))))))))))))))))

(defun prh-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-page-read-pool
    (mv-let (result fn-page-read-pool) (prh-run fn-page-read-pool) result)))

; Served adapter state effects, not just its pure ledger helper.
(assert!
 (equal (prh-exec)
        '(:read-resources-unavailable nil :installed :registered :admitted
          (0 7 11 200 64 999) :read-resources-unavailable nil t :settled
          (216 0 1 0 1) :stale :read-file-held :evicted :closed :already-installed
          (0 0 0 0 1) 1)))

(defun prh-preview-run (fn-page-read-pool)
  (declare (xargs :mode :program :stobjs fn-page-read-pool))
  (let ((offline (fn-owner-page-read-registration-mode fn-page-read-pool))
        (offline-close (fn-owner-page-read-close-preview 11 fn-page-read-pool)))
    (mv-let (installed fn-page-read-pool)
      (fn-owner-page-read-install '(10000 0 2 1 10) 8 3000 4 fn-page-read-pool)
      (let ((funded (fn-owner-page-read-registration-mode fn-page-read-pool)))
        (mv-let (registered fn-page-read-pool)
          (fn-owner-page-read-register 11 fn-page-read-pool)
          (let ((before (fn-owner-page-read-ledger fn-page-read-pool))
                (preview (fn-owner-page-read-close-preview 11 fn-page-read-pool)))
            (mv (list offline offline-close installed funded registered preview
                      (equal before (fn-owner-page-read-ledger fn-page-read-pool)))
                fn-page-read-pool)))))))
(defun prh-preview-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-page-read-pool
    (mv-let (result fn-page-read-pool) (prh-preview-run fn-page-read-pool) result)))
(assert!
 (equal (prh-preview-exec)
        '(:unfunded-offline :unfunded-offline :installed :funded-pool :registered :closable t)))
(assert-event
 (and (eq (symbol-class 'fn-owner-page-read-registration-mode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-read-close-preview (w state)) :common-lisp-compliant)))
