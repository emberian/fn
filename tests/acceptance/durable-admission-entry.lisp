;;; ENTRY PROBE ONLY: no POST driver/restart acceptance claim yet.
;;; Load after matched extracted core and CURRENT native source; no doubles.
(in-package "CL-USER")
(let ((entry (find-symbol "FNN-OWNER-RUN" "CL-USER"))
      (root (sb-ext:posix-getenv "FN_ACCEPTANCE_STORE"))
      (marker (sb-ext:posix-getenv "FN_ACCEPTANCE_OWNERSHIP"))
      (expected (sb-ext:posix-getenv "FN_ACCEPTANCE_EXPECTED_EXIT")))
  (unless (and entry (fboundp entry))
    (format *error-output* "MISSING-LOADING-INTERFACE: actual FNN-OWNER-RUN absent; no acceptance result.~%")
    (sb-ext:exit :code 2))
  (unless (and root marker expected
               (search "/build/acceptance-runs/" (namestring (truename root)))
               (with-open-file (s (merge-pathnames "../.fn-acceptance-owned" (pathname root)))
                 (equal marker (read-line s nil nil))))
    (error "Refusing an unowned acceptance Store; use the private fixture orchestrator."))
  ;; No generic condition remapping: actual typed failure/cleanup propagates.
  (let ((result (funcall entry root 0 t 1)))
    (unless (and (integerp result)
                 (= result (parse-integer expected :junk-allowed nil)))
      (error "Unexpected actual owner exit ~s" result))
    (format t "ACTUAL-OWNER-ENTRY-PROBE-EXIT: ~d~%" result)
    (sb-ext:exit :code result)))
