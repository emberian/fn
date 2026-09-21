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
           :use (fn-bs-store-relation-unfolds)
           :in-theory (enable fn-bs-link fn-bs-dir-quietp
                              fn-bs-fence-dir fn-bs-ops-for-dir
                              fn-bs-ops-for-dir-of-append
                              fn-sf-record-link-result fn-sf-fencedp))))

; The composed host-called observation enters the same fenced kernel phase.
(defthm fn-bs-native-record-link-error-fences-composed-subject
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-data-durable))
           (fn-sf-fencedp
            (fn-sn-files (fn-sn-io s :record-link :error))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-statep fn-sn-io fn-sn-file-step fn-sn-update
                                     fn-sf-record-link-result fn-sf-fencedp))))

; The allocator has the same issued-but-unobserved boundary at rename(2).
; The staging deletion is a separate operation, so the recovery obligation
; here is specifically the authority entry in :root.
(defthm fn-bs-issued-frontier-rename-error-needs-recovery-fence
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :frontier-data-durable)
                (fn-bs-inop (fn-bs-lookup bs :staging stage))
                (consp outcome)
                (equal (cdr outcome) :issued))
           (mv-let (result bs1)
             (fn-bs-rename bs :staging stage :root
                           *fn-bs-frontier-name* outcome)
             (and (equal result (car outcome))
                  (fn-sf-fencedp (fn-sf-frontier-replace-result ks :error))
                  (not (fn-bs-dir-quietp bs1 :root))
                  (fn-bs-dir-quietp
                   (fn-bs-fence-dir bs1 :root) :root))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds)
           :in-theory (enable fn-bs-rename fn-bs-dir-quietp
                              fn-bs-fence-dir fn-bs-ops-for-dir
                              fn-bs-ops-for-dir-of-append
                              fn-sf-frontier-replace-result fn-sf-fencedp))))

; This is the exact composed observation called after native os.rename.
(defthm fn-bs-native-frontier-rename-error-fences-composed-subject
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :frontier-data-durable))
           (fn-sf-fencedp
            (fn-sn-files (fn-sn-io s :frontier-replace :error))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-statep fn-sn-io fn-sn-file-step fn-sn-update
                                     fn-sf-frontier-replace-result fn-sf-fencedp))))
