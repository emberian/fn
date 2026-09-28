; Crash-model K7 at the byte syscall boundary.
(in-package "ACL2")
(include-book "byte-store-native-correspondence")

(local
 (defthm fn-bs-native-store-files-are-a-kernel-state
   (implies (fn-sn-statep s)
            (fn-sf-statep (fn-sn-files s)))
   :hints (("Goal" :in-theory (enable fn-sn-statep)))))

; A reported link error is uncertain only when the namespace operation may
; have been issued.  With the physical link preconditions explicit, the byte
; state retains a pending transaction-directory operation, the kernel fences,
; and only the recovery directory fence drains that operation.  The source and
; destination hypotheses are physical preconditions of link(2); the logical
; phase alone cannot manufacture a staging inode.
(defthm fn-bs-issued-record-link-error-needs-recovery-fence
  (implies (and (fn-sf-statep ks)
                (equal (fn-sf-phase ks) :record-data-durable)
                (fn-bs-inop (fn-bs-lookup bs :staging stage))
                (not (fn-bs-lookup bs :transactions name))
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
                              fn-bs-ops-for-dir-of-append
                              fn-sf-record-link-result fn-sf-fencedp))))

; The composed host-called observation enters the same fenced kernel phase.
(defthm fn-bs-native-record-link-error-fences-composed-subject
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-data-durable))
           (fn-sf-fencedp
            (fn-sn-files (fn-sn-io s :record-link :error))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-native-store-files-are-a-kernel-state
                 (:instance fn-bs-native-io-is-byte-observation
                            (operation :record-link) (result :error)))
           :in-theory (e/d (fn-bs-native-io-event fn-sf-dispatch
                            fn-sf-record-link-result fn-sf-fencedp)
                           (fn-sn-statep fn-sn-io fn-sn-update
                            fn-sf-statep)))))

; The allocator has the same issued-but-unobserved boundary at rename(2).
; The staging deletion is a separate operation, so the recovery obligation
; here is specifically the authority entry in :root.
(defthm fn-bs-issued-frontier-rename-error-needs-recovery-fence
  (implies (and (fn-sf-statep ks)
                (equal (fn-sf-phase ks) :frontier-data-durable)
                (fn-bs-inop (fn-bs-lookup bs :staging stage))
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
  :hints (("Goal"
           :use (fn-bs-native-store-files-are-a-kernel-state
                 (:instance fn-bs-native-io-is-byte-observation
                            (operation :frontier-replace) (result :error)))
           :in-theory (e/d (fn-bs-native-io-event fn-sf-dispatch
                            fn-sf-frontier-replace-result fn-sf-fencedp)
                           (fn-sn-statep fn-sn-io fn-sn-update
                            fn-sf-statep)))))

; An error return from the transaction-directory barrier resolves some
; physical outcome but cannot report commitment.  The byte syscall drains
; that directory's pending choice either way; the kernel enters the recovery
; fence and therefore cannot continue publication.
(defthm fn-bs-record-directory-error-resolves-choice-and-fences
  (implies (and (fn-sf-statep ks)
                (equal (fn-sf-phase ks) :record-attempted)
                (consp outcome))
           (mv-let (result bs1)
             (fn-bs-fsync-dir bs :transactions outcome)
             (and (equal result (car outcome))
                  (fn-bs-dir-quietp bs1 :transactions)
                  (fn-sf-fencedp (fn-sf-record-dir-result ks :error)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-ops-for-dir-of-ops-not-for-dir
                            (ops (fn-bs-pending bs)) (dir :transactions)))
           :in-theory (enable fn-bs-fsync-dir fn-bs-dir-quietp
                              fn-bs-ops-for-dir fn-bs-ops-not-for-dir
                              fn-sf-record-dir-result fn-sf-fencedp))))

(defthm fn-bs-native-record-directory-error-fences-composed-subject
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :record-attempted))
           (fn-sf-fencedp
            (fn-sn-files (fn-sn-io s :record-directory :error))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-native-store-files-are-a-kernel-state
                 (:instance fn-bs-native-io-is-byte-observation
                            (operation :record-directory) (result :error)))
           :in-theory (e/d (fn-bs-native-io-event fn-sf-dispatch
                            fn-sf-record-dir-result fn-sf-fencedp)
                           (fn-sn-statep fn-sn-io fn-sn-update
                            fn-sf-statep)))))

(defthm fn-bs-frontier-directory-error-resolves-choice-and-fences
  (implies (and (fn-sf-statep ks)
                (equal (fn-sf-phase ks) :frontier-attempted)
                (consp outcome))
           (mv-let (result bs1)
             (fn-bs-fsync-dir bs :root outcome)
             (and (equal result (car outcome))
                  (fn-bs-dir-quietp bs1 :root)
                  (fn-sf-fencedp (fn-sf-frontier-dir-result ks :error)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-ops-for-dir-of-ops-not-for-dir
                            (ops (fn-bs-pending bs)) (dir :root)))
           :in-theory (enable fn-bs-fsync-dir fn-bs-dir-quietp
                              fn-bs-ops-for-dir fn-bs-ops-not-for-dir
                              fn-sf-frontier-dir-result fn-sf-fencedp))))

(defthm fn-bs-native-frontier-directory-error-fences-composed-subject
  (implies (and (fn-sn-statep s)
                (equal (fn-sf-phase (fn-sn-files s)) :frontier-attempted))
           (fn-sf-fencedp
            (fn-sn-files (fn-sn-io s :frontier-directory :error))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-native-store-files-are-a-kernel-state
                 (:instance fn-bs-native-io-is-byte-observation
                            (operation :frontier-directory) (result :error)))
           :in-theory (e/d (fn-bs-native-io-event fn-sf-dispatch
                            fn-sf-frontier-dir-result fn-sf-fencedp)
                           (fn-sn-statep fn-sn-io fn-sn-update
                            fn-sf-statep)))))
