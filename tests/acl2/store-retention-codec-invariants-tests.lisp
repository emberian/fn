; Called owner retention event bytes: one valid authored event and the exact
; counterexample when the retention event predicate is dropped.
(in-package "ACL2")
(include-book "../../books/store-retention-codec-invariants")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-srci-test-retention*
  (fn-store-retention-event-make :undertake 1 1 1
                                  "obligation-1" "subject-1" "local" 1))
(defconst *fn-srci-test-invalid-retention*
  (fn-store-retention-event-make :undertake 1 1 1
                                  "obligation-1" "subject-1" "local" 0))

(assert-event
 (and (fn-store-retention-event-p *fn-srci-test-retention*)
      (equal (len (fn-srci-retention-items *fn-srci-test-retention*)) 10)
      (equal (fn-store-retention-event-decode-exact
              (fn-store-retention-event-encode *fn-srci-test-retention*))
             (list :ok *fn-srci-test-retention*))
      (equal (fn-store-event-decode-exact
              (fn-store-event-encode *fn-srci-test-retention*))
             (list :ok *fn-srci-test-retention*))))

(assert-event
 (and (not (fn-store-retention-event-p *fn-srci-test-invalid-retention*))
      (equal (fn-store-retention-event-encode *fn-srci-test-invalid-retention*)
             nil)
      (not (equal (fn-store-event-decode-exact
                   (fn-store-event-encode *fn-srci-test-invalid-retention*))
                  (list :ok *fn-srci-test-invalid-retention*)))))
(must-fail
 (assert-event
  (equal (fn-store-event-decode-exact
          (fn-store-event-encode *fn-srci-test-invalid-retention*))
         (list :ok *fn-srci-test-invalid-retention*))))
