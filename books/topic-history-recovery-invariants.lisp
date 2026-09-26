; Topic projection at actual Store crash, recovery and observed open.
; These are boundary selector facts; the maintained live/history relation is
; proved separately in topic-history-store-invariants.
(in-package "ACL2")
(include-book "store-observed")

(defthm fn-thr-crash-resets-topic-by-definition
  (implies (and (fn-sn-statep s)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (equal (fn-sn-topic (fn-sn-crash s frontier-choice record-choice))
                  (fn-th-prefix-state :ok 0 nil nil nil nil nil)))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-crash)
                           (fn-sn-statep fn-sf-crash-choicep
                            fn-sn-update-indexed fn-sn-make-v6 fn-sn-make-v7)))))

(defthm fn-thr-successful-recover-rebuilds-topic-by-definition
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :replaying)
                (equal (fn-sf-phase (fn-sn-files (fn-sn-recover s)))
                       :recovering))
           (equal (fn-sn-topic (fn-sn-recover s))
                  (fn-th-prefix-project
                   (fn-sf-records (fn-sn-files (fn-sn-recover s))))))
  :hints (("Goal"
           :in-theory (e/d (fn-sn-recover)
                           (fn-sn-statep fn-sf-statep
                            fn-sn-update fn-sn-update-replayed
                            fn-sn-make-v6 fn-sn-make-v7 fn-th-prefix-project)))))

(defthm fn-thr-observed-open-rebuilds-exact-topic
  (implies (fn-sn-open-okp
            (fn-sn-open-observed groups capacity frontier records))
           (equal (fn-sn-topic
                   (fn-sn-open-state
                    (fn-sn-open-observed groups capacity frontier records)))
                  (fn-th-prefix-project records)))
  :hints (("Goal"
           :use (fn-sn-open-observed-success-exact-history
                 (:instance fn-thr-successful-recover-rebuilds-topic-by-definition
                   (s (fn-sn-observed-seed groups capacity frontier records))))
           :in-theory (e/d (fn-sn-open-observed fn-sn-open-okp
                            fn-sn-observed-seed)
                           (fn-sn-recover
                            fn-sn-statep fn-sf-statep
                            fn-th-prefix-project)))))
