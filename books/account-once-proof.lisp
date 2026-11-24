; A second grant cannot return the row whose reservation wait was cleared.
(in-package "ACL2")
(include-book "assembly-access")

(defthm fn2-account-returned-row-was-waiting
  (let ((id (mv-nth 0 (fn2-account-grant-take fn2-core))))
    (implies (not (equal id *fn2-none*))
             (equal (fn2-machine-wait-reason id fn2-core) *fn2-wait-principal-reservation*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-account-grant-take fn2-account-grant-entry)
                                  (fn2-account-grant-head fn2-account-core-ends fn2-account-core-grant
                                   fn2-machine-idp fn2-machine-wait-reason
                                   fn2-machine-ready-prev fn2-machine-ready-next)))))
(defthm fn2-account-clear-request-wait
  (implies (fn2-machine-idp id fn2-core)
           (equal (fn2-machine-wait-reason id
                    (fn2-machine-put id (wait-reason *fn2-wait-none*) (ready-prev *fn2-none*) (ready-next *fn2-none*)))
                  *fn2-wait-none*))
  :hints (("Goal" :in-theory (enable fn2-machine-write-wait-reason fn2-machine-write-ready-next
                               fn2-machine-write-ready-prev fn2-machine-set-ready-next
                               fn2-machine-set-ready-prev fn2-machine-set-wait-reason
                               fn2-machine-idp fn2-machines-rows fn2-machine-wait-reason
                               fn2-machine-wait-reason-read-code fn2-machines-wait-reason
                               fn2-machines-set-wait-reason fn2-machines-set-ready-next fn2-machines-set-ready-prev
                               update-fn2-machines-ready-next$ai update-fn2-machines-ready-prev$ai
                               update-fn2-machines-wait-reason$ai fn2-machines-wait-reason$ai))))
(defthm fn2-account-grant-keeps-directory-bounds
  (equal (fn2-machine-idp id (mv-nth 1 (fn2-account-core-grant p fn2-core)))
         (fn2-machine-idp id fn2-core))
  :hints (("Goal" :in-theory (enable fn2-machine-idp))))
(defthm fn2-account-ends-keep-directory-bounds
  (equal (fn2-machine-idp id (fn2-account-core-set-ends p head tail fn2-core))
         (fn2-machine-idp id fn2-core))
  :hints (("Goal" :in-theory (enable fn2-machine-idp fn2-account-core-set-ends))))
(defthm fn2-account-write-prev-keeps-directory-bounds
  (equal (fn2-machine-idp id (fn2-machine-write-ready-prev other *fn2-none* fn2-core))
         (fn2-machine-idp id fn2-core))
  :hints (("Goal" :in-theory (enable fn2-machine-idp fn2-machine-write-ready-prev
                                fn2-machine-set-ready-prev fn2-machines-set-ready-prev fn2-machines-rows
                                fn2-machine-refuse-write fn2-core-stop update-fn2-machines-ready-prev$ai))))

(defthm fn2-account-grant-entry-row-in-range
  (let ((entry (fn2-account-grant-entry fn2-core)))
    (implies (eq (mv-nth 0 entry) :ready) (fn2-machine-idp (mv-nth 2 entry) fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-account-grant-entry)
                                  (fn2-machine-idp fn2-account-grant-head fn2-account-core-ends)))))
(defthm fn2-account-returned-row-clears-wait
  (let* ((result (fn2-account-grant-take fn2-core)) (id (mv-nth 0 result)))
    (implies (not (equal id *fn2-none*))
             (equal (fn2-machine-wait-reason id (mv-nth 1 result)) *fn2-wait-none*)))
  :hints (("Goal" :in-theory (e/d (fn2-account-grant-take)
                                  (fn2-account-grant-entry fn2-account-core-grant fn2-account-core-set-ends
                                   fn2-machine-write-wait-reason fn2-machine-write-ready-next
                                   fn2-machine-write-ready-prev fn2-machine-idp fn2-machine-wait-reason)))))
(defthm fn2-account-no-consecutive-grants
  (let* ((result (fn2-account-grant-take fn2-core)) (id (mv-nth 0 result)))
    (implies (not (equal id *fn2-none*))
             (not (equal (mv-nth 0 (fn2-account-grant-take (mv-nth 1 result))) id))))
  :hints (("Goal" :use ((:instance fn2-account-returned-row-was-waiting
                           (fn2-core (mv-nth 1 (fn2-account-grant-take fn2-core))))
                        fn2-account-returned-row-clears-wait)
           :in-theory (disable fn2-account-grant-take fn2-account-returned-row-clears-wait))))
