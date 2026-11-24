; Every fitting head in a consistent request directory passes the bounded
; dequeue checks. A malformed self-link invalidates this implication.
(in-package "ACL2")
(include-book "owed-accounts")
(include-book "account-fifo-head")

(defthm fn2-account-chosen-in-range
  (let ((p (fn2-account-core-grant-next c)))
    (implies (not (equal p *fn2-none*))
             (and (natp p) (< p (fn2-accounts-rows (fn2-core-accounts c)))
                  (unsigned-byte-p 32 (+ 1 p)))))
  :hints (("Goal" :use ((:instance fn2-account-grant-scan-range
                         (fn2-accounts (fn2-core-accounts c))
                         (k (nfix (fn2-accounts-rows (fn2-core-accounts c))))
                         (i (fn2-account-grant-cursor (fn2-core-accounts c)))))
           :in-theory (e/d (fn2-account-core-grant-next fn2-account-grant-next)
                           (fn2-accounts-rows fn2-account-grant-scan fn2-account-grant-cursor
                            fn2-accountsp fn2-accounts-wfp fn2-accounts-shapep)))))
(defthm fn2-account-invariant-selected-links
  (implies (and (fn2-corep c) (fn2-core-wfp c) (natp (fn2-accounts-rows (fn2-core-accounts c))) (fn2-account-core-invariantp c) (natp p) (< p (fn2-accounts-rows (fn2-core-accounts c))))
           (fn2-account-fifo-head-linksp (fn2-accounts-wait-head p (fn2-core-accounts c))
                                         (fn2-accounts-wait-tail p (fn2-core-accounts c))
                                         (fn2-core-machines c)))
  :hints (("Goal" :use ((:instance fn2-account-all-fifos-head-links
                         (acts (fn2-core-accounts c)) (machines (fn2-core-machines c))
                         (rows (fn2-accounts-rows (fn2-core-accounts c))) (seen nil)))
           :in-theory (e/d (fn2-account-core-invariantp) (fn2-account-fifo-head-linksp
                            fn2-account-fifos-visit fn2-accounts-rows fn2-accounts-wait-head
                            fn2-accounts-wait-tail fn2-core-stop-reason fn2-core-stopped-p)))))
(defthm fn2-account-invariant-pending-ready
  (implies (and (fn2-corep c) (fn2-core-wfp c) (fn2-account-core-invariantp c)
                (fn2-account-grant-pending c))
           (fn2-account-grant-ready c))
  :hints (("Goal" :use ((:instance fn2-account-invariant-selected-links (p (fn2-account-core-grant-next c)))
                         fn2-account-chosen-in-range)
           :in-theory (e/d (fn2-account-fifo-head-linksp fn2-account-grant-ready fn2-account-grant-entry
                            fn2-account-grant-head fn2-account-grant-pending fn2-account-core-ends fn2-machine-idp
                            fn2-machine-ready-next fn2-machine-ready-prev fn2-machine-wait-reason)
                           (fn2-account-core-invariantp fn2-account-core-grant-next fn2-corep fn2-core-wfp
                            fn2-accounts-wfp fn2-accountsp fn2-accounts-shapep fn2-accounts-wait-head
                            fn2-accounts-wait-tail fn2-accounts-rows fn2-machines-rows fn2-machines-ready-next
                            fn2-machines-ready-prev fn2-machines-wait-reason fn2-core-stopped-p)))))
