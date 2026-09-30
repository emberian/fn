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
      (fn-owner-page-read-install '(10000 0 2 1 10) 8 3000 4 100 fn-page-read-pool)
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
                              (fn-owner-page-read-install '(10000 0 2 1 10) 8 3000 4 100 fn-page-read-pool)
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
      (fn-owner-page-read-install '(10000 0 2 1 10) 8 3000 4 100 fn-page-read-pool)
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
        '(:read-resources-unavailable :read-resources-unavailable :installed :funded-pool :registered :closable t)))
(assert-event
 (and (eq (symbol-class 'fn-owner-page-read-registration-mode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-read-close-preview (w state)) :common-lisp-compliant)))

(defun prh-file-run (fn-page-read-pool)
  (declare (xargs :mode :program :stobjs fn-page-read-pool))
  (let ((offline (mv-list 3 (fn-owner-page-file-issue nil fn-page-read-pool))))
    (mv-let (installed fn-page-read-pool)
      (fn-owner-page-read-install '(10000 0 2 1 10) 8 0 4 2 fn-page-read-pool)
      (mv-let (registered fn-page-read-pool)
        (fn-owner-page-read-register-path 1 "/x" fn-page-read-pool)
        (mv (list offline installed registered
                  (fn-prl-nth 1 (fn-owner-page-read-ledger fn-page-read-pool))
                  (mv-list 3 (fn-owner-page-file-issue nil fn-page-read-pool))
                  (mv-list 3 (fn-owner-page-file-issue 2 fn-page-read-pool))
                  (mv-list 3 (fn-owner-page-file-issue 3 fn-page-read-pool)))
            fn-page-read-pool)))))
(defun prh-file-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-page-read-pool
    (mv-let (result fn-page-read-pool) (prh-file-run fn-page-read-pool) result)))
(assert!
 (equal (prh-file-exec)
        '((:read-resources-unavailable nil nil) :installed :registered (88 0 1 0 0)
          (:issued 2 1) (:issued 3 2) (:file-identities-exhausted 3 nil))))
(assert-event
 (and (eq (symbol-class 'fn-owner-page-file-issue (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-read-register-path (w state)) :common-lisp-compliant)))

(defun prh-baseline-run (fn-page-read-pool)
  (declare (xargs :mode :program :stobjs fn-page-read-pool))
  (mv-let (bad fn-page-read-pool)
    (fn-owner-page-read-install-baseline '(10000 0 2 1 10) '(10001 0 0 0 0) 8 4 100 fn-page-read-pool)
    (let ((absent (not (fn-prp-data fn-page-read-pool))))
      (mv-let (installed fn-page-read-pool)
        (fn-owner-page-read-install-baseline '(10000 0 2 1 10) '(3000 0 0 0 0) 8 4 100 fn-page-read-pool)
        (mv-let (registered fn-page-read-pool)
          (fn-owner-page-read-register 11 fn-page-read-pool)
          (mv-let (admitted token fn-page-read-pool)
            (fn-owner-page-read-admit 7 11 200 64 999 fn-page-read-pool)
            (mv-let (settled fn-page-read-pool)
              (fn-owner-page-read-settle token t fn-page-read-pool)
              (mv (list bad absent installed registered admitted settled
                        (fn-prl-baseline (fn-owner-page-read-ledger fn-page-read-pool))
                        (fn-prl-nth 1 (fn-owner-page-read-ledger fn-page-read-pool)))
                  fn-page-read-pool))))))))
(defun prh-baseline-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-page-read-pool
    (mv-let (result fn-page-read-pool) (prh-baseline-run fn-page-read-pool) result)))
(assert!
 (equal (prh-baseline-exec)
        '(:invalid-resource-profile t :installed :registered :admitted :settled
          (3000 0 0 0 0) (216 0 1 0 1))))
(assert-event (eq (symbol-class 'fn-owner-page-read-install-baseline (w state)) :common-lisp-compliant))

(defun prh-mode-run (mode fn-page-read-pool)
  (declare (xargs :mode :program :stobjs fn-page-read-pool))
  (let ((before (fn-owner-page-read-direct-mode fn-page-read-pool)))
    (mv-let (entered fn-page-read-pool) (fn-owner-page-read-enter-mode mode fn-page-read-pool)
      (mv-let (opened fn-page-read-pool) (fn-owner-page-read-open-context fn-page-read-pool)
        (mv-let (switch fn-page-read-pool) (fn-owner-page-read-enter-mode :offline fn-page-read-pool)
          (mv (list before entered opened switch
                    (fn-owner-page-read-direct-mode fn-page-read-pool)
                    (fn-owner-page-read-registration-mode fn-page-read-pool)
                    (mv-list 3 (fn-owner-page-file-issue nil fn-page-read-pool))) fn-page-read-pool))))))
(defun prh-mode-exec (mode)
  (declare (xargs :mode :program))
  (with-local-stobj fn-page-read-pool
    (mv-let (result fn-page-read-pool) (prh-mode-run mode fn-page-read-pool) result)))
(assert!
 (equal (prh-mode-exec :served)
        '(:read-resources-unavailable :served :served :invalid-resource-mode
          :read-resources-unavailable :read-resources-unavailable
          (:read-resources-unavailable nil nil))))
(assert!
 (equal (prh-mode-exec :offline)
        '(:read-resources-unavailable :offline :offline :offline
          :offline :unfunded-offline (:unfunded-offline 2 1))))

(defun prh-discovery-run (fn-page-read-pool)
  (declare (xargs :mode :program :stobjs fn-page-read-pool))
  (mv-let (installed fn-page-read-pool)
    (fn-owner-page-read-install-baseline '(10000 0 2 1 10) '(3000 0 0 0 0) 8 4 100 fn-page-read-pool)
    (mv-let (registered fn-page-read-pool) (fn-owner-page-read-register 11 fn-page-read-pool)
      (mv-let (admitted token fn-page-read-pool) (fn-owner-page-read-discovery-admit 11 200 64 fn-page-read-pool)
        (let ((held (fn-owner-page-read-close-preview 11 fn-page-read-pool)))
          (mv-let (released fn-page-read-pool) (fn-owner-page-read-discovery-release token fn-page-read-pool)
            (mv-let (duplicate fn-page-read-pool) (fn-owner-page-read-discovery-release token fn-page-read-pool)
              (mv (list installed registered admitted token held released duplicate
                        (fn-owner-page-read-close-preview 11 fn-page-read-pool)
                        (fn-prl-baseline (fn-owner-page-read-ledger fn-page-read-pool))
                        (fn-prl-nth 1 (fn-owner-page-read-ledger fn-page-read-pool))) fn-page-read-pool))))))))
(defun prh-discovery-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-page-read-pool
    (mv-let (result fn-page-read-pool) (prh-discovery-run fn-page-read-pool) result)))
(assert!
 (equal (prh-discovery-exec)
        '(:installed :registered :admitted (:discovery 0 11 200 64) :read-file-held
          :released :stale :closable (3000 0 0 0 0) (8 0 1 0 1))))
(assert-event
 (and (eq (symbol-class 'fn-owner-page-read-direct-mode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-read-enter-mode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-read-discovery-admit (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-owner-page-read-discovery-release (w state)) :common-lisp-compliant)))
