; Read the actual holding, head and directory after the composed grant.
(in-package "ACL2")
(include-book "assembly-access")
(include-book "account-grant-effect")

(defthm fn2-account-hold-of-grant-at
  (equal (fn2-account-hold p d (fn2-accounts-set-grant-at row v acts))
         (fn2-account-hold p d acts))
  :hints (("Goal" :in-theory (enable fn2-account-hold fn2-account-holdv fn2-accounts-rows
                                   fn2-accounts-set-grant-at update-fn2-accounts-grant-at$ai))))
(defthm fn2-account-core-grant-adds-holding
  (implies (equal (mv-nth 0 (fn2-account-core-grant p fn2-core)) :ok)
           (equal (fn2-account-core-hold p *fn2-account-request-dim* (mv-nth 1 (fn2-account-core-grant p fn2-core)))
                  (+ 1 (fn2-account-core-hold p *fn2-account-request-dim* fn2-core))))
  :hints (("Goal" :in-theory (e/d (fn2-account-core-hold fn2-account-core-grant fn2-accounts-rows)
                                (fn2-account-acquire fn2-account-hold fn2-accounts-set-grant-at
                                 fn2-accountsp fn2-accounts-wfp fn2-accounts-shapep)))))
(defthm fn2-account-hold-of-fifo-ends
  (and (equal (fn2-account-hold q d (fn2-accounts-set-wait-head p v acts)) (fn2-account-hold q d acts))
       (equal (fn2-account-hold q d (fn2-accounts-set-wait-tail p v acts)) (fn2-account-hold q d acts)))
  :hints (("Goal" :in-theory (enable fn2-account-hold fn2-account-holdv fn2-accounts-rows
                                   fn2-accounts-set-wait-head fn2-accounts-set-wait-tail
                                   update-fn2-accounts-wait-head$ai update-fn2-accounts-wait-tail$ai))))
(defthm fn2-account-set-ends-holding
  (equal (fn2-account-core-hold q d (fn2-account-core-set-ends p h tail fn2-core))
         (fn2-account-core-hold q d fn2-core))
  :hints (("Goal" :in-theory (e/d (fn2-account-core-hold fn2-account-core-set-ends fn2-accounts-rows)
                                 (fn2-account-hold fn2-accounts-set-wait-head fn2-accounts-set-wait-tail
                                  fn2-accountsp fn2-accounts-wfp fn2-accounts-shapep)))))

(defmacro fn2-account-directory-write-keeps-ledger (field)
  (let ((write (fn2-columns-sym 'fn2-machine-write- (symbol-name field)))
        (set (fn2-columns-sym 'fn2-machine-set- (symbol-name field))))
    `(defthm ,(fn2-columns-sym write "-PRESERVES-REQUEST-LEDGER")
       (equal (fn2-core-accounts (,write id v fn2-core)) (fn2-core-accounts fn2-core))
       :hints (("Goal" :in-theory (enable ,write ,set fn2-machine-refuse-write fn2-core-stop))))))
(fn2-account-directory-write-keeps-ledger ready-next)
(fn2-account-directory-write-keeps-ledger ready-prev)
(fn2-account-directory-write-keeps-ledger wait-reason)
(defthm fn2-account-set-ends-new-head
  (implies (and (mv-nth 0 (fn2-account-core-ends p fn2-core))
                (unsigned-byte-p 32 h) (unsigned-byte-p 32 tail))
           (equal (mv-nth 1 (fn2-account-core-ends p (fn2-account-core-set-ends p h tail fn2-core))) h))
  :hints (("Goal" :in-theory (e/d (fn2-account-core-ends fn2-account-core-set-ends fn2-accounts-rows
                                  fn2-accounts-wait-head)
                                (fn2-accounts-set-wait-head fn2-accounts-set-wait-tail fn2-accountsp
                                 fn2-accounts-wfp fn2-accounts-shapep)))))
(defthm fn2-account-granted-principal-has-ends
  (implies (equal (mv-nth 0 (fn2-account-core-grant p fn2-core)) :ok)
           (mv-nth 0 (fn2-account-core-ends p (mv-nth 1 (fn2-account-core-grant p fn2-core)))))
  :hints (("Goal" :in-theory (e/d (fn2-account-core-grant fn2-account-core-ends fn2-accounts-rows)
                                (fn2-account-acquire fn2-accounts-set-grant-at fn2-accountsp
                                 fn2-accounts-wfp fn2-accounts-shapep)))))
(defthm fn2-account-ready-grant-entry-values
  (let* ((e (fn2-account-grant-entry fn2-core)) (p (fn2-account-core-grant-next fn2-core))
         (id (mv-nth 2 e)))
    (implies (fn2-account-grant-ready fn2-core)
             (and (eq (mv-nth 0 e) :ready)
                  (equal (mv-nth 1 e) p)
                  (not (equal p *fn2-none*))
                  (unsigned-byte-p 32 (+ 1 p))
                  (equal id (mv-nth 1 (fn2-account-core-ends p fn2-core)))
                  (equal (mv-nth 3 e) (fn2-machine-ready-next id fn2-core))
                  (unsigned-byte-p 32 (mv-nth 3 e))
                  (unsigned-byte-p 32 (mv-nth 4 e)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-account-grant-entry fn2-account-grant-head fn2-account-grant-ready)
                                   (fn2-account-core-grant-next fn2-account-core-ends fn2-machine-idp
                                    fn2-machine-ready-next fn2-machine-ready-prev fn2-machine-wait-reason)))))

(defmacro fn2-account-directory-write-reads (field)
  (let ((write (fn2-columns-sym 'fn2-machine-write- (symbol-name field))))
    `(defthm ,(fn2-columns-sym write "-REQUEST-READS")
       (let ((c (,write id v fn2-core)))
         (and (equal (fn2-account-core-hold p d c) (fn2-account-core-hold p d fn2-core))
              (equal (fn2-account-core-ends p c) (fn2-account-core-ends p fn2-core))))
       :hints (("Goal" :in-theory (e/d (fn2-account-core-ends fn2-account-core-hold)
                                       (,write fn2-account-hold fn2-accounts-rows fn2-accountsp
                                        fn2-accounts-wfp fn2-accounts-shapep)))))))
(fn2-account-directory-write-reads ready-next)
(fn2-account-directory-write-reads ready-prev)
(fn2-account-directory-write-reads wait-reason)
(defthm fn2-account-ready-grant-exact
  (implies (fn2-account-grant-ready fn2-core)
           (let* ((p (fn2-account-core-grant-next fn2-core))
                  (head (mv-nth 1 (fn2-account-core-ends p fn2-core)))
                  (next (fn2-machine-ready-next head fn2-core))
                  (result (fn2-account-grant-take fn2-core))
                  (c2 (mv-nth 1 result)))
             (and (equal (mv-nth 0 result) head)
                  (equal (fn2-account-core-hold p *fn2-account-request-dim* c2)
                         (+ 1 (fn2-account-core-hold p *fn2-account-request-dim* fn2-core)))
                  (equal (mv-nth 1 (fn2-account-core-ends p c2)) next))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-account-ready-grant-entry-values fn2-account-core-chosen-acquires)
           :in-theory (e/d (fn2-account-grant-take)
                           (fn2-account-grant-entry fn2-account-grant-ready fn2-account-core-grant-next
                            fn2-account-core-grant fn2-account-core-ends fn2-account-core-hold
                            fn2-account-core-set-ends fn2-machine-ready-next unsigned-byte-p)))))
