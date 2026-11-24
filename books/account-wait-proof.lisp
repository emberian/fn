; Each visit either reaches the fitting head, observes a refusal, or moves
; the cursor strictly closer to its principal. Only a stopped core without a
; recorded reason can keep a fitting head pending without making progress.
(in-package "ACL2")
(include-book "owed-accounts")
(include-book "account-exact-proof")
(include-book "account-grant-order")

(defun-nx fn2-account-core-cursor (c) (fn2-account-grant-cursor (fn2-core-accounts c)))
(defthm fn2-account-rows-of-ends
  (equal (fn2-account-core-rows (fn2-account-core-set-ends p h tail c)) (fn2-account-core-rows c))
  :hints (("Goal" :in-theory (enable fn2-account-core-rows fn2-account-core-set-ends fn2-accounts-rows))))
(defthm fn2-account-cursor-of-ends
  (equal (fn2-account-core-cursor (fn2-account-core-set-ends p h tail c)) (fn2-account-core-cursor c))
  :hints (("Goal" :in-theory (enable fn2-account-core-cursor fn2-account-grant-cursor fn2-accounts-grant-at
                           fn2-account-core-set-ends fn2-accounts-rows fn2-accounts-set-wait-head
                           fn2-accounts-set-wait-tail update-fn2-accounts-wait-head$ai update-fn2-accounts-wait-tail$ai))))
(defmacro fn2-account-grant-position-frame (field)
  (let ((write (fn2-columns-sym 'fn2-machine-write- (symbol-name field))))
    `(defthm ,(fn2-columns-sym write "-KEEPS-GRANT-POSITION")
       (let ((c (,write id v fn2-core)))
         (and (equal (fn2-account-core-cursor c) (fn2-account-core-cursor fn2-core))
              (equal (fn2-account-core-rows c) (fn2-account-core-rows fn2-core))))
       :hints (("Goal" :in-theory (e/d (fn2-account-core-cursor fn2-account-core-rows)
                                       (,write fn2-account-grant-cursor fn2-accounts-rows)))))))
(fn2-account-grant-position-frame ready-next)
(fn2-account-grant-position-frame ready-prev)
(fn2-account-grant-position-frame wait-reason)
(defthm fn2-account-core-grant-rows
  (equal (fn2-account-core-rows (mv-nth 1 (fn2-account-core-grant p c)))
         (fn2-account-core-rows c))
  :hints (("Goal" :in-theory (e/d (fn2-account-core-grant fn2-account-core-rows fn2-accounts-rows)
                                  (fn2-account-acquire fn2-accounts-set-grant-at)))))
(defthm fn2-account-core-granted-cursor
  (implies (equal (mv-nth 0 (fn2-account-core-grant p c)) :ok)
           (equal (fn2-account-core-cursor (mv-nth 1 (fn2-account-core-grant p c)))
                  (if (< (+ 1 p) (fn2-account-core-rows c)) (+ 1 p) 0)))
  :hints (("Goal" :in-theory (e/d (fn2-account-core-cursor fn2-account-core-rows fn2-account-core-grant
                                   fn2-account-grant-cursor fn2-accounts-grant-at fn2-accounts-rows
                                   fn2-accounts-set-grant-at update-fn2-accounts-grant-at$ai)
                                  (fn2-account-acquire fn2-accountsp fn2-accounts-wfp fn2-accounts-shapep)))))
(defthm fn2-account-ready-grant-position
  (let ((c2 (mv-nth 1 (fn2-account-grant-take c))) (p (fn2-account-core-grant-next c)))
    (implies (fn2-account-grant-ready c)
             (and (equal (fn2-account-core-rows c2) (fn2-account-core-rows c))
                  (equal (fn2-account-core-cursor c2)
                         (if (< (+ 1 p) (fn2-account-core-rows c)) (+ 1 p) 0)))))
  :hints (("Goal" :use ((:instance fn2-account-ready-grant-entry-values (fn2-core c))
                        (:instance fn2-account-core-chosen-acquires (fn2-core c)))
           :in-theory (e/d (fn2-account-grant-take)
                           (fn2-account-grant-ready fn2-account-grant-entry fn2-account-core-grant
                            fn2-account-core-grant-next fn2-account-core-rows fn2-account-core-cursor
                            fn2-account-core-set-ends unsigned-byte-p)))))

(defun-nx fn2-account-stop-recorded-p (c)
  (implies (fn2-core-stopped-p c) (not (equal (fn2-core-stop-reason c) *fn2-stop-reason-none*))))
(defthm fn2-account-refusal-records-reason
  (implies (not (fn2-core-stopped-p c))
           (equal (fn2-core-stop-reason (fn2-machine-refuse-write c)) *fn2-stop-reason-machine-write*))
  :hints (("Goal" :in-theory (enable fn2-core-stop-reason fn2-core-stopped-p fn2-machine-refuse-write
                                fn2-core-stop fn2-control-record-stop fn2-control-stop fn2-control-stop-reason
                                update-fn2-control-stop update-fn2-control-stop-reason))))
(defthm fn2-account-pending-unready-reason
  (implies (and (not (fn2-core-stopped-p c)) (fn2-account-grant-pending c)
                (not (fn2-account-grant-ready c)))
           (equal (fn2-core-stop-reason (mv-nth 1 (fn2-account-grant-take c)))
                  *fn2-stop-reason-machine-write*))
  :hints (("Goal" :in-theory (e/d (fn2-account-grant-pending fn2-account-grant-ready
                                  fn2-account-grant-entry fn2-account-grant-take)
                                 (fn2-account-grant-head fn2-machine-refuse-write fn2-core-stopped-p
                                  fn2-account-core-ends fn2-machine-idp fn2-core-stop-reason)))))
(defthm fn2-account-refusal-preserves-stop-record
  (implies (fn2-account-stop-recorded-p c) (fn2-account-stop-recorded-p (fn2-machine-refuse-write c)))
  :hints (("Goal" :in-theory (enable fn2-account-stop-recorded-p fn2-core-stop-reason fn2-core-stopped-p
                                fn2-machine-refuse-write fn2-core-stop fn2-control-record-stop fn2-control-stop
                                fn2-control-stop-reason update-fn2-control-stop update-fn2-control-stop-reason))))
(defthm fn2-account-grant-keeps-stop-record
  (and (equal (fn2-account-stop-recorded-p (mv-nth 1 (fn2-account-core-grant p c)))
              (fn2-account-stop-recorded-p c))
       (equal (fn2-account-stop-recorded-p (fn2-account-core-set-ends p h tail c))
              (fn2-account-stop-recorded-p c)))
  :hints (("Goal" :in-theory (enable fn2-account-core-set-ends fn2-account-stop-recorded-p
                                fn2-core-stop-reason fn2-core-stopped-p))))
(defmacro fn2-account-write-stop-frame (field)
  (let ((write (fn2-columns-sym 'fn2-machine-write- (symbol-name field)))
        (set (fn2-columns-sym 'fn2-machine-set- (symbol-name field))))
    `(progn
      (defthm ,(fn2-columns-sym set "-KEEPS-STOP-RECORD")
        (equal (fn2-account-stop-recorded-p (,set id v c)) (fn2-account-stop-recorded-p c))
        :hints (("Goal" :in-theory (enable ,set fn2-account-stop-recorded-p fn2-core-stop-reason fn2-core-stopped-p))))
      (defthm ,(fn2-columns-sym write "-KEEPS-STOP-RECORD")
        (implies (fn2-account-stop-recorded-p c)
                 (fn2-account-stop-recorded-p (,write id v c)))
        :hints (("Goal" :in-theory (e/d (,write) (fn2-account-stop-recorded-p fn2-machine-refuse-write ,set))))))))
(fn2-account-write-stop-frame wait-reason)
(fn2-account-write-stop-frame ready-prev)
(fn2-account-write-stop-frame ready-next)
(defthm fn2-account-take-keeps-stop-record
  (implies (fn2-account-stop-recorded-p c)
           (fn2-account-stop-recorded-p (mv-nth 1 (fn2-account-grant-take c))))
  :hints (("Goal" :in-theory (e/d (fn2-account-grant-take) (fn2-account-grant-entry fn2-account-stop-recorded-p
                            fn2-machine-refuse-write fn2-account-core-grant fn2-account-core-set-ends)))))

(defthm fn2-account-scan-head-exists
  (let ((q (fn2-account-grant-scan k i acts)))
    (implies (not (equal q *fn2-none*))
             (not (equal (fn2-accounts-wait-head q acts) *fn2-none*))))
  :hints (("Goal" :induct (fn2-account-grant-scan k i acts)
           :in-theory (e/d (fn2-account-grant-scan) (fn2-accounts-rows fn2-accounts-wait-head fn2-account-fits)))))
(defthm fn2-account-selected-pending
  (implies (and (not (fn2-core-stopped-p c)) (not (equal (fn2-account-core-grant-next c) *fn2-none*)))
           (fn2-account-grant-pending c))
  :hints (("Goal" :use ((:instance fn2-account-grant-scan-range
                          (i (fn2-account-grant-cursor (fn2-core-accounts c)))
                          (k (nfix (fn2-accounts-rows (fn2-core-accounts c))))
                          (fn2-accounts (fn2-core-accounts c))))
           :in-theory (e/d (fn2-account-grant-pending fn2-account-grant-head fn2-account-core-grant-next
                            fn2-account-core-ends fn2-account-grant-next fn2-accounts-rows)
                           (fn2-accountsp fn2-accounts-wfp fn2-accounts-shapep fn2-account-grant-scan
                            fn2-account-grant-cursor fn2-accounts-wait-head)))))
(defthm fn2-account-headed-distance
  (let ((rows (fn2-account-core-rows c)) (q (fn2-account-core-grant-next c)))
    (implies (fn2-account-core-headed-fits p h c)
             (and (not (equal q *fn2-none*)) (natp rows) (natp p) (< p rows)
                  (or (equal q p)
                      (< (fn2-account-grant-distance (+ 1 q) p rows)
                         (fn2-account-grant-distance (fn2-account-core-cursor c) p rows))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-account-grant-next-progress (fn2-accounts (fn2-core-accounts c))))
           :in-theory (e/d (fn2-account-core-grant-next fn2-account-core-headed-fits fn2-account-core-rows
                            fn2-account-core-cursor)
                           (fn2-account-grant-next fn2-account-grant-distance fn2-account-fits
                            fn2-accounts-rows fn2-accountsp fn2-accounts-wfp fn2-accounts-shapep
                            fn2-account-grant-cursor fn2-accounts-wait-head)))))
(defthm fn2-account-distance-cursor-wrap
  (implies (and (natp i) (natp rows) (<= rows i))
           (equal (fn2-account-grant-distance i p rows)
                  (fn2-account-grant-distance 0 p rows)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-account-grant-distance))))
(defthm fn2-account-headed-ready-own-row
  (implies (and (fn2-account-core-headed-fits p h c) (fn2-account-grant-ready c)
                (equal (fn2-account-core-grant-next c) p))
           (equal (mv-nth 0 (fn2-account-grant-take c)) h))
  :hints (("Goal" :use ((:instance fn2-account-ready-grant-exact (fn2-core c)))
           :in-theory (e/d (fn2-account-core-headed-fits fn2-account-core-ends)
                           (fn2-account-grant-ready fn2-account-grant-entry fn2-account-grant-take
                            fn2-account-core-grant-next fn2-account-fits fn2-accounts-rows
                            fn2-accountsp fn2-accounts-wfp fn2-accounts-shapep)))))

(defthm fn2-account-headed-grant-progress
  (let* ((rows (fn2-account-core-rows c)) (q (fn2-account-core-grant-next c))
         (after (mv-nth 1 (fn2-account-grant-take c))))
    (implies (and (fn2-account-core-headed-fits p h c) (fn2-account-grant-ready c)
                  (not (equal q p)))
             (< (fn2-account-grant-distance (fn2-account-core-cursor after) p (fn2-account-core-rows after))
                (fn2-account-grant-distance (fn2-account-core-cursor c) p rows))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-account-headed-distance fn2-account-ready-grant-position
                         (:instance fn2-account-distance-cursor-wrap (i (+ 1 (fn2-account-core-grant-next c)))
                          (rows (fn2-account-core-rows c))))
           :in-theory (e/d (fn2-account-core-grant-next fn2-account-grant-next)
                           (fn2-account-grant-ready fn2-account-core-rows fn2-account-grant-distance
                            fn2-account-core-cursor fn2-account-grant-take fn2-account-core-headed-fits
                            fn2-account-grant-scan fn2-account-grant-cursor fn2-accountsp
                            fn2-accounts-wfp fn2-accounts-shapep fn2-accounts-rows)))))
(defthm fn2-account-one-visit-progress
  (let* ((grant (fn2-account-grant-take c)) (after (mv-nth 1 grant)))
    (implies (and (fn2-account-stop-recorded-p c) (equal (fn2-core-stop-reason c) *fn2-stop-reason-none*)
                  (fn2-account-core-headed-fits p h c) (not (equal h (mv-nth 0 grant)))
                  (equal (fn2-core-stop-reason after) *fn2-stop-reason-none*))
             (< (fn2-account-grant-distance (fn2-account-core-cursor after) p (fn2-account-core-rows after))
                (fn2-account-grant-distance (fn2-account-core-cursor c) p (fn2-account-core-rows c)))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-account-headed-distance fn2-account-selected-pending
                         fn2-account-pending-unready-reason fn2-account-headed-grant-progress
                         fn2-account-headed-ready-own-row)
           :in-theory '(fn2-account-stop-recorded-p))))
(defthm fn2-account-grant-distance-natural
  (natp (fn2-account-grant-distance cursor p rows))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-account-grant-distance))))
(defthm fn2-account-stopped-wait-complete
  (implies (not (equal (fn2-core-stop-reason c) *fn2-stop-reason-none*))
           (mv-nth 0 (fn2-account-granted-within n p h c)))
  :hints (("Goal" :expand ((fn2-account-granted-within n p h c))
           :in-theory (disable fn2-account-granted-within fn2-core-stop-reason))))
(defthm fn2-account-wait-with-distance
  (implies (and (fn2-account-stop-recorded-p c)
                (< (fn2-account-grant-distance (fn2-account-core-cursor c) p (fn2-account-core-rows c))
                   (nfix n)))
           (mv-nth 0 (fn2-account-granted-within n p h c)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-account-granted-within n p h c)
           :in-theory (e/d (fn2-account-granted-within)
                           (fn2-account-grant-take fn2-account-grant-distance fn2-account-core-cursor
                            fn2-account-core-rows fn2-account-core-headed-fits fn2-account-stop-recorded-p
                            fn2-core-stop-reason)))
          (and stable-under-simplificationp
               '(:use (fn2-account-one-visit-progress fn2-account-take-keeps-stop-record)))))

(defthm fn2-account-unheaded-wait-complete
  (implies (not (fn2-account-core-headed-fits p h c))
           (mv-nth 0 (fn2-account-granted-within n p h c)))
  :hints (("Goal" :expand ((fn2-account-granted-within n p h c))
           :in-theory (disable fn2-account-granted-within fn2-account-core-headed-fits fn2-core-stop-reason))))
(defthm fn2-account-invariant-records-stop
  (implies (fn2-account-core-invariantp c) (fn2-account-stop-recorded-p c))
  :hints (("Goal" :in-theory '(fn2-account-core-invariantp fn2-account-stop-recorded-p iff implies))))
(defthm fn2-account-wait-within-principal-count
  (implies (fn2-account-stop-recorded-p c)
           (mv-nth 0 (fn2-account-granted-within (fn2-account-core-rows c) p h c)))
  :hints (("Goal" :use (fn2-account-headed-distance
                         (:instance fn2-account-grant-distance-bound (cursor (fn2-account-core-cursor c))
                          (rows (fn2-account-core-rows c)))
                         (:instance fn2-account-wait-with-distance (n (fn2-account-core-rows c)))
                         (:instance fn2-account-unheaded-wait-complete (n (fn2-account-core-rows c))))
           :in-theory '(nfix natp))))
