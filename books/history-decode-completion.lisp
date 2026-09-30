; Actual authenticated provider completion consumer. No borrowed tree is walked.
; The provider emits this bundle only after Store columns, padding and MKEY.
(in-package "ACL2")
(include-book "history-decode-size")
(include-book "snapshot-source-token")

(defun fn-hds-completion (n bundle expected)
  (declare (xargs :guard (member-equal n '(0 6 7))
                  :guard-hints (("Goal" :in-theory (enable fn-omk-at)))))
  (let* ((source (fn-omk-at 1 bundle))
         (s (fn-omk-at 2 bundle))
         (lease (fn-hds-at 11 s)))
    (if (not (and (fn-omk-widthp bundle 6)
                  (eq (fn-omk-at 0 bundle) :parser-completion)
                  (fn-omk-token-matchp source expected)
                  (fn-hdc-statep s)
                  (equal (fn-hds-at 10 s) (fn-omk-at 0 source))
                  (fn-omk-widthp lease 2)
                  (natp (fn-omk-at 0 lease)) (natp (fn-omk-at 1 lease))
                  (equal (fn-omk-at 0 lease)
                         (fn-omk-at 0 (fn-omk-at 1 source)))
                  (equal (fn-omk-at 1 lease)
                         (fn-omk-at 1 (fn-omk-at 1 source)))))
        (mv :refused nil nil nil nil nil)
      (fn-hds-result n s (fn-omk-at 3 bundle) (fn-omk-at 5 bundle)))))

(local (defthm fn-hds-at-is-nth
 (implies (natp n) (equal (fn-hds-at n x) (nth n x)))
 :hints (("Goal" :in-theory (enable fn-hds-at nth)))))

(defthm fn-hds-completion-success-has-source-lifetime
 (implies (equal (mv-nth 0 (fn-hds-completion n bundle expected)) :ok)
  (and (fn-omk-token-matchp (fn-omk-at 1 bundle) expected)
       (equal (mv-nth 4 (fn-hds-completion n bundle expected))
              (fn-omk-at 0 (fn-omk-at 1 bundle)))
       (equal (fn-omk-at 0 (mv-nth 5 (fn-hds-completion n bundle expected)))
              (fn-omk-at 0 (fn-omk-at 1 (fn-omk-at 1 bundle))))
       (equal (fn-omk-at 1 (mv-nth 5 (fn-hds-completion n bundle expected)))
              (fn-omk-at 1 (fn-omk-at 1 (fn-omk-at 1 bundle))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-hds-completion)
                                (fn-hds-result fn-omk-token-matchp fn-hdc-statep fn-hds-at fn-omk-at)))))

(in-theory (disable fn-hds-completion))
