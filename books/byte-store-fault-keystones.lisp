; Crash-model K7 at the byte syscall boundary.
(in-package "ACL2")
(include-book "byte-store-native-correspondence")

; A reported link error is uncertain only when the namespace operation may
; have been issued.  With the physical link preconditions explicit, the byte
; state retains a pending transaction-directory operation, the kernel fences,
; and only the recovery directory fence drains that operation.  The source and
; destination hypotheses are physical preconditions of link(2); the logical
; phase alone cannot manufacture a staging inode.
(defthm fn-bs-issued-record-link-error-needs-recovery-fence
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-data-durable)
                (fn-bs-inop (fn-bs-lookup bs :staging stage))
                (not (fn-bs-lookup bs :transactions name))
                (consp outcome)
                (equal (cdr outcome) :issued))
           (mv-let (result bs1)
             (fn-bs-link bs :staging stage :transactions name outcome)
             (and (equal result (car outcome))
                  (fn-sf-fencedp (fn-sf-record-link-result ks :error))
                  (not (fn-bs-dir-quietp bs1 :transactions))
                  (fn-bs-dir-quietp
                   (fn-bs-fence-dir bs1 :transactions) :transactions))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable fn-bs-link fn-bs-dir-quietp
                              fn-bs-fence-dir fn-bs-ops-for-dir
                              fn-sf-record-link-result fn-sf-fencedp))))

; The composed host-called observation enters the same fenced kernel phase.
(defthm fn-bs-native-record-link-error-fences-composed-subject
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-data-durable))
           (fn-sf-fencedp
            (fn-sn-files (fn-sn-io s :record-link :error))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-io fn-sn-file-step fn-sn-update
                                     fn-sf-record-link-result fn-sf-fencedp))))
