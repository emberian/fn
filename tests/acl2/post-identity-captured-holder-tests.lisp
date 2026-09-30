(in-package "ACL2")
(include-book "../../books/post-identity-captured-holder")
(include-book "post-identity-captured-tests")

(defun pic-held-test-run (phase slot-token expected)
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-page-read-pool
    (mv-let (ok fn-page-read-pool)
      (let* ((carrier (fn-ibc-carrier '(:input-backing 4 3)
                         (list slot-token phase '(0 0 0 0 1))))
             (fn-page-read-pool (update-fn-prp-incoming-slot carrier fn-page-read-pool)))
        (mv
          (with-local-stobj fn-octets
            (mv-let (ok fn-octets)
              (let* ((fn-octets (fn-octets-from-list '(65 66 67) fn-octets))
                     (c (fn-pic-feed (pic-test-begin nil nil)
                          (list :payload-length *pic-test-selected* *pic-test-grant* 0 3))))
                (mv-let (word next left)
                  (fn-pic-held-next c 2 fn-octets fn-page-read-pool)
                  (mv (and (equal word expected) (natp left) (<= left 2)
                           (equal (fn-octets-list fn-octets) '(65 66 67))
                           (equal (fn-prp-incoming-slot fn-page-read-pool) carrier)
                           (equal (fn-pic-captured-context next) (fn-pic-captured-context c))
                           (if (equal expected :continue)
                               (and (equal (fn-ioh-access (fn-ibc-carrier-row carrier)
                                         (fn-pic-get incoming-token c) :read) :holder-readonly)
                                    (equal (list word next left)
                                      (mv-list 3 (fn-pic-next c 2 fn-octets)))
                                    (not (equal next c)))
                             (and (not (equal (fn-ioh-access (fn-ibc-carrier-row carrier)
                                          (fn-pic-get incoming-token c) :read) :holder-readonly))
                                  (equal next c) (equal left 2)))) fn-octets)))
              ok))
          fn-page-read-pool))
      ok)))
; Complete literal authorized-output/context/fuel positive for actual pool.
(assert-event (pic-held-test-run :readonly *pic-test-incoming* :continue))
; Refusal cases affirm their access denial, unchanged continuation and fuel.
(assert-event (pic-held-test-run :cancelled *pic-test-incoming* :incoming-busy))
(assert-event (pic-held-test-run :setup *pic-test-incoming* :holder-setup))
; Mutation witness: stale token, with otherwise readonly current row.
(assert-event (pic-held-test-run :readonly '(:incoming 5) :incoming-busy))
; The named frame is explicitly ghost/by-definition, with complete effects.
(defthm pic-held-test-input-frame-positive
  (let* ((c (make-list 23 :initial-element nil))
         (input (create-fn-octets)) (pool (create-fn-page-read-pool))
         (out (mv-list 5 (fn-pic-held-next-input-frame c 2 input pool))))
    (and (equal (nth 3 out) input) (equal (nth 4 out) pool)
         (equal (nth 0 out) (mv-nth 0 (fn-pic-held-next c 2 input pool)))
         (equal (nth 1 out) (mv-nth 1 (fn-pic-held-next c 2 input pool)))
         (equal (nth 2 out) (mv-nth 2 (fn-pic-held-next c 2 input pool)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pic-held-next-input-frame-by-definition
                         (c (make-list 23 :initial-element nil)) (fuel 2)
                         (fn-octets (create-fn-octets))
                         (fn-page-read-pool (create-fn-page-read-pool))))
                  :in-theory (disable fn-pic-held-next-input-frame fn-pic-held-next
                                      fn-pic-next create-fn-octets create-fn-page-read-pool))))
; Hypothesis removal for the shared-fuel theorem. Both actual stobjs are
; well-formed; this deliberately malformed logical fuel is outside the guard.
(defun pic-held-test-fuel-removal ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-page-read-pool
    (mv-let (ok fn-page-read-pool)
      (mv
        (with-local-stobj fn-octets
          (mv-let (ok fn-octets)
            (mv-let (word next left)
              (fn-pic-held-next (pic-test-begin nil nil) -1 fn-octets fn-page-read-pool)
              (declare (ignore word next))
              (mv (and (not (natp -1))
                       (not (and (natp left) (<= left -1)))) fn-octets))
            ok))
        fn-page-read-pool)
      ok)))
(assert-event (with-guard-checking :none (pic-held-test-fuel-removal)))
