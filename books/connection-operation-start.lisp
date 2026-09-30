; Private installed operation composition. No public demand/tariff/ready flag.
; Native holds owner -> extent continuously across prepare/start/open/epilogue.
; The installation global has ONE genuine producer (the selected runtime
; installer); this leaf deliberately contains no installation setter.
(in-package "ACL2")
(include-book "owner-state-accessors")
(include-book "index-connection-start")
(include-book "connection-operation-cost")
(include-book "connection-operation-ticket")

; Ticket16: tag phase kind family address peer owner-id slot nonce epoch
; installation-serial descriptor-reference holdergrant fuel input-quantum token.
; This root is included in the operation envelope before LIST construction.
; It is not a second installation authority or a native per-CID table.
(defun fn-owner-index-connection-prepare
 (kind family address peer slot fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
  :guard (and (boundp-global 'fn-owner state) (fn-aec-pool-statep fn-page-read-pool))
  :verify-guards nil))
 (if (let ((prior (fn-owner-connection-operation-ticket state)))
       (and prior (not (eq (fn-omk-at 1 prior) :finished))))
     (mv nil :recovery-required nil fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
  (mv-let (entered nonce fn-allocation-turn-slots fn-page-read-pool)
   (fn-ats-enter-internal slot :connection-start fn-allocation-turn-slots fn-page-read-pool)
   (if (not (eq entered :gate-owned))
       (mv nil entered nonce fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
    ; Prior finished roots retire only under this freshly prepaid gate. A raw
    ; completion escape fenced the pool and cannot reach this successful entry.
    (let* ((installation (fn-owner-connection-operation-installation state))
          (state (f-put-global 'fn-owner-connection-operation-ticket nil state)))
     (mv-let (word demand fuel body quantum)
      (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
       (word demand fuel body quantum)
       (fn-cop-evaluate installation kind family address peer
                        (fn-ibp-slot-depth fn-index-backing))
       (mv word demand fuel body quantum))
      (if (not (eq word :derived))
          (mv-let (erp refused retained fn-allocation-turn-slots fn-page-read-pool state)
           (fn-owner-index-connection-refuse-internal slot nonce word
             fn-allocation-turn-slots fn-page-read-pool state)
           (mv erp refused retained fn-allocation-turn-slots fn-mio$c fn-page-read-pool state))
       (mv-let (paid fn-allocation-turn-slots fn-page-read-pool)
        (fn-ats-prepay-body-internal slot nonce (nfix body)
                                     fn-allocation-turn-slots fn-page-read-pool)
        (if (not (eq paid :prepaid))
            (if (eq paid :yield)
                (mv-let (erp refused retained fn-allocation-turn-slots fn-page-read-pool state)
                 (fn-owner-index-connection-refuse-internal slot nonce :yield
                   fn-allocation-turn-slots fn-page-read-pool state)
                 (mv erp refused retained fn-allocation-turn-slots fn-mio$c fn-page-read-pool state))
              (mv nil :recovery-required nonce fn-allocation-turn-slots fn-mio$c fn-page-read-pool state))
         (let ((state (f-put-global 'fn-owner-connection-operation-ticket
                       (list :connection-operation-ticket :prepaid kind family address peer
                             (fn-own-next-id (fn-owner-core state)) slot nonce
                             (fn-prp-alloc-epoch fn-page-read-pool)
                             (fn-omk-at 1 installation) installation demand fuel quantum nil)
                       state)))
          (mv nil :prepared nonce fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)))))))))))

(defun fn-owner-index-connection-start
 (kind family address peer fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool state)
  :guard (and (boundp-global 'fn-owner state)
              (fn-aec-pool-statep fn-page-read-pool)) :verify-guards nil))
 (let* ((ticket (fn-owner-connection-operation-ticket state))
        (installation (fn-owner-connection-operation-installation state))
        (quantum (nfix (fn-omk-at 14 ticket))))
  (cond
   ((not ticket) (mv nil :unsupported-runtime nil 0 fn-mio$c fn-page-read-pool state))
   ((not (and (fn-omk-widthp ticket 16)
               (symbolp kind) (symbolp family)
               (eq (fn-omk-at 0 ticket) :connection-operation-ticket)
               (eq (fn-omk-at 1 ticket) :prepaid)
               (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining))
               (posp (fn-prp-alloc-active-turns fn-page-read-pool))
               (eq kind (fn-omk-at 2 ticket)) (eq family (fn-omk-at 3 ticket))
               (fn-cop-octets-match address (fn-omk-at 4 ticket) quantum)
               (fn-cop-octets-match peer (fn-omk-at 5 ticket) quantum)
               (equal (fn-own-next-id (fn-owner-core state)) (fn-omk-at 6 ticket))
               (equal (fn-prp-alloc-epoch fn-page-read-pool) (fn-omk-at 9 ticket))
               (equal (fn-omk-at 1 installation) (fn-omk-at 10 ticket))))
    (mv nil :recovery-required (fn-omk-at 15 ticket) (nfix (fn-omk-at 13 ticket))
        fn-mio$c fn-page-read-pool state))
   (t
    ; Keep all input, receipt and descriptor roots BEFORE issuer effects. A raw
    ; escape keeps this intent and the pool A; it is never retried as prepaid.
    (let ((state (f-put-global 'fn-owner-connection-operation-ticket
                               (update-nth 1 :start-intent ticket) state)))
     (if (not (fn-cop-issuer-domainp (fn-owner-page-read-ledger fn-page-read-pool)
                                      (fn-omk-at 12 ticket) (fn-omk-at 4 installation)))
         (mv nil :recovery-required nil (nfix (fn-omk-at 13 ticket))
             fn-mio$c fn-page-read-pool state)
      (mv-let (word token left fn-mio$c fn-page-read-pool)
       (fn-mio-connection-reserve-register (fn-omk-at 6 ticket) (fn-omk-at 12 ticket)
                                           (nfix (fn-omk-at 13 ticket)) fn-mio$c fn-page-read-pool)
       (let ((state (f-put-global 'fn-owner-connection-operation-ticket
                     (update-nth 15 token
                      (update-nth 1 (cond ((eq word :reserved) :started)
                                          ((or token (eq word :recovery-required)) :start-intent)
                                          (t :refused)) ticket)) state)))
        (mv nil word token left fn-mio$c fn-page-read-pool state)))))))))

; Actual composed guards; local representation lemmas stay local to this book.
(local
 (defthm fn-cops-pool-body-state
  (implies (and (fn-aec-pool-statep fn-page-read-pool)
                (not (eq (fn-prp-alloc-mode fn-page-read-pool) :uninstalled)))
   (fn-aec-pool-statep (mv-nth 1 (fn-aec-pool-body-internal body nil fn-page-read-pool))))
  :hints (("Goal" :in-theory (disable fn-aec-statep fn-aec-body)
   :use ((:instance fn-aec-body-preserves-allocation-state
    (i (fn-prp-alloc-installation fn-page-read-pool)) (m (fn-prp-alloc-mode fn-page-read-pool))
    (e (fn-prp-alloc-epoch fn-page-read-pool)) (l (fn-prp-alloc-occupied fn-page-read-pool))
    (a (fn-prp-alloc-allocated fn-page-read-pool)) (n (fn-prp-alloc-active-turns fn-page-read-pool))
    (g (fn-prp-alloc-gc-nonce fn-page-read-pool)) (cleanup nil)))))))

(local
 (defthm fn-cops-ats-body-state
  (implies (fn-aec-pool-statep fn-page-read-pool)
   (fn-aec-pool-statep (mv-nth 2 (fn-ats-prepay-body-internal slot nonce body fn-allocation-turn-slots fn-page-read-pool))))
  :hints (("Goal" :in-theory (disable fn-aec-pool-statep fn-aec-pool-body-internal)))))

(verify-guards fn-owner-index-connection-prepare
 :hints (("Goal" :in-theory (disable fn-ats-enter-internal fn-ats-prepay-body-internal fn-owner-index-connection-refuse-internal fn-aec-pool-statep fn-cop-evaluate)
 :use ((:instance fn-atsh-entry-preserves-carried-pool-state (role :connection-start))))))

(local
 (defthm fn-cops-fixed-ticket-list
  (implies (fn-omk-widthp x n) (true-listp x))
  :hints (("Goal" :in-theory (enable fn-omk-widthp)))))

(local
 (defthm fn-cops-fixed-ticket-phase-list
  (implies (fn-omk-widthp x 16) (true-listp (update-nth 1 phase x)))
  :hints (("Goal" :in-theory (disable fn-omk-widthp update-nth true-listp)
    :use ((:instance fn-cops-fixed-ticket-list (n 16))
          (:instance true-listp-update-nth (l x) (key 1) (val phase)))))))

(verify-guards fn-owner-index-connection-start
 :hints (("Goal" :in-theory (e/d (true-listp-update-nth) (fn-aec-pool-statep fn-mio-connection-reserve-register fn-cop-issuer-domainp fn-owner-core fn-cop-octets-match fn-owner-connection-operation-ticket fn-owner-connection-operation-installation fn-omk-widthp)))))

(defthm fn-owner-index-connection-reserved-has-registered-receipt
 (implies
  (eq (mv-nth 1 (fn-owner-index-connection-start kind family address peer fn-mio$c fn-page-read-pool state)) :reserved)
  (let ((receipt
         (fn-ibp-connection-pending
          (fn-mio$c-provider
           (mv-nth 4 (fn-owner-index-connection-start kind family address peer fn-mio$c fn-page-read-pool state))))))
   (and (equal (fn-omk-at 1 receipt)
               (mv-nth 2 (fn-owner-index-connection-start kind family address peer fn-mio$c fn-page-read-pool state)))
        (eq (fn-omk-at 0 receipt) :connection-reservation)
        (eq (fn-omk-at 6 receipt) :registered))))
 :hints (("Goal" :in-theory
          (disable fn-ics-reserve-register fn-cop-issuer-domainp fn-owner-core
                   fn-owner-connection-operation-ticket fn-owner-connection-operation-installation
                   fn-cop-octets-match)
          :use ((:instance fn-ics-reserved-has-registered-receipt
                  (id (fn-omk-at 6 (fn-owner-connection-operation-ticket state)))
                  (demand (fn-omk-at 12 (fn-owner-connection-operation-ticket state)))
                  (fuel (nfix (fn-omk-at 13 (fn-owner-connection-operation-ticket state))))
                  (backing (fn-mio$c-provider fn-mio$c)) (pool fn-page-read-pool)))))
 :rule-classes nil)

(local
 (defthm fn-cops-entry-pool-state
  (implies (fn-aec-pool-statep fn-page-read-pool)
   (fn-aec-pool-statep (mv-nth 3 (fn-ats-enter-internal slot role fn-allocation-turn-slots fn-page-read-pool))))
  :hints (("Goal" :in-theory (disable fn-ats-enter-internal fn-aec-pool-statep)
   :use fn-atsh-entry-preserves-carried-pool-state))))
(local
 (defthm fn-cops-refuse-pool-state
  (implies (fn-aec-pool-statep fn-page-read-pool)
   (fn-aec-pool-statep (mv-nth 4 (fn-owner-index-connection-refuse-internal slot nonce reason fn-allocation-turn-slots fn-page-read-pool state))))
  :hints (("Goal" :in-theory (disable fn-ats-finish-owned fn-aec-pool-statep)
   :use fn-atsh-finish-preserves-carried-pool-state))))

(defthm fn-owner-index-connection-prepare-preserves-carried-pool
 (implies (fn-aec-pool-statep fn-page-read-pool)
  (fn-aec-pool-statep
   (mv-nth 5 (fn-owner-index-connection-prepare kind family address peer slot fn-allocation-turn-slots fn-mio$c fn-page-read-pool state))))
 :hints (("Goal" :in-theory
  (disable fn-ats-enter-internal fn-ats-prepay-body-internal fn-owner-index-connection-refuse-internal
           fn-aec-pool-statep fn-cop-evaluate fn-owner-connection-operation-ticket
           fn-owner-connection-operation-installation fn-owner-core fn-omk-at)))
 :rule-classes nil)

(local (defthm fn-cops-entry-frame-for-prepare
 (mv-let (word nonce next-fn-allocation-turn-slots next-fn-page-read-pool) (fn-ats-enter-internal slot role fn-allocation-turn-slots fn-page-read-pool)
  (declare (ignore word nonce))
  (and (equal (fn-ats-association next-fn-allocation-turn-slots) (fn-ats-association fn-allocation-turn-slots))
       (equal (fn-ats-count next-fn-allocation-turn-slots) (fn-ats-count fn-allocation-turn-slots))
       (equal (nth 2 next-fn-allocation-turn-slots) (nth 2 fn-allocation-turn-slots))
       (equal (fn-prp-alloc-installation next-fn-page-read-pool) (fn-prp-alloc-installation fn-page-read-pool))
       (equal (fn-prp-alloc-epoch next-fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool))
       (equal (fn-prp-alloc-occupied next-fn-page-read-pool) (fn-prp-alloc-occupied fn-page-read-pool))
       (equal (fn-prp-mode next-fn-page-read-pool) (fn-prp-mode fn-page-read-pool))
       (equal (fn-prp-incoming-slot next-fn-page-read-pool) (fn-prp-incoming-slot fn-page-read-pool))))
 :hints (("Goal" :in-theory (disable fn-ats-enter-internal) :use fn-atsh-entry-preserves-installed-roots))))

(local (defthm fn-cops-finish-frame-for-prepare
 (mv-let (word next-fn-allocation-turn-slots next-fn-page-read-pool) (fn-ats-finish-owned slot nonce fn-allocation-turn-slots fn-page-read-pool)
  (declare (ignore word))
  (and (equal (fn-ats-association next-fn-allocation-turn-slots) (fn-ats-association fn-allocation-turn-slots))
       (equal (fn-ats-count next-fn-allocation-turn-slots) (fn-ats-count fn-allocation-turn-slots))
       (equal (nth 2 next-fn-allocation-turn-slots) (nth 2 fn-allocation-turn-slots))
       (equal (nth 3 next-fn-allocation-turn-slots) (nth 3 fn-allocation-turn-slots))
       (equal (fn-prp-data next-fn-page-read-pool) (fn-prp-data fn-page-read-pool))
       (equal (fn-prp-alloc-installation next-fn-page-read-pool) (fn-prp-alloc-installation fn-page-read-pool))
       (equal (fn-prp-alloc-epoch next-fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool))
       (equal (fn-prp-alloc-occupied next-fn-page-read-pool) (fn-prp-alloc-occupied fn-page-read-pool))
       (equal (fn-prp-mode next-fn-page-read-pool) (fn-prp-mode fn-page-read-pool))
       (equal (fn-prp-incoming-slot next-fn-page-read-pool) (fn-prp-incoming-slot fn-page-read-pool))))
 :hints (("Goal" :in-theory (disable fn-ats-finish-owned) :use fn-atsh-finish-preserves-installed-roots))))

(local
 (defthm fn-cops-body-frame-for-prepare
  (let ((next (fn-ats-prepay-body-internal slot nonce body fn-allocation-turn-slots fn-page-read-pool)))
   (and (equal (fn-prp-alloc-installation (mv-nth 2 next)) (fn-prp-alloc-installation fn-page-read-pool))
        (equal (fn-prp-alloc-epoch (mv-nth 2 next)) (fn-prp-alloc-epoch fn-page-read-pool))
        (equal (fn-prp-alloc-occupied (mv-nth 2 next)) (fn-prp-alloc-occupied fn-page-read-pool))
        (equal (fn-ats-association (mv-nth 1 next)) (fn-ats-association fn-allocation-turn-slots))
        (equal (fn-ats-count (mv-nth 1 next)) (fn-ats-count fn-allocation-turn-slots))
        (equal (nth 2 (mv-nth 1 next)) (nth 2 fn-allocation-turn-slots))))
  :hints (("Goal" :in-theory (disable nth update-nth fn-aec-body)))))

(defthm fn-owner-index-connection-prepare-retains-installed-roots
 (let ((next (fn-owner-index-connection-prepare kind family address peer slot fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)))
  (and (equal (mv-nth 4 next) fn-mio$c)
       (equal (fn-prp-alloc-installation (mv-nth 5 next)) (fn-prp-alloc-installation fn-page-read-pool))
       (equal (fn-prp-alloc-epoch (mv-nth 5 next)) (fn-prp-alloc-epoch fn-page-read-pool))
       (equal (fn-prp-alloc-occupied (mv-nth 5 next)) (fn-prp-alloc-occupied fn-page-read-pool))
       (equal (fn-ats-association (mv-nth 3 next)) (fn-ats-association fn-allocation-turn-slots))
       (equal (fn-ats-count (mv-nth 3 next)) (fn-ats-count fn-allocation-turn-slots))
       (equal (nth 2 (mv-nth 3 next)) (nth 2 fn-allocation-turn-slots))))
 :hints (("Goal" :in-theory (disable nth update-nth fn-ats-enter-internal fn-ats-prepay-body-internal fn-ats-finish-owned fn-prp-alloc-installation fn-prp-alloc-epoch fn-prp-alloc-occupied fn-ats-association fn-ats-count fn-cop-evaluate fn-owner-connection-operation-ticket fn-owner-connection-operation-installation fn-owner-core fn-omk-at fn-omk-widthp)))
 :rule-classes nil)


(local
 (defthm fn-cops-keep-ledger-pool-state
  (equal (fn-aec-pool-statep (fn-owner-page-read-keep-ledger ledger pool)) (fn-aec-pool-statep pool))
  :hints (("Goal" :in-theory (disable fn-aec-pool-statep fn-owner-page-read-keep-ledger)
   :use fn-aec-keep-ledger-preserves-installed-state))))

(local
 (defthm fn-cops-reserve-pool-state
  (equal (fn-aec-pool-statep (mv-nth 3 (fn-icr-reserve id demand backing pool))) (fn-aec-pool-statep pool))
  :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-owner-page-read-keep-ledger fn-prs-issue fn-prs-vectorp fn-icr-candidate
            fn-owner-page-read-ledger fn-prl-nth fn-prl-build fn-omk-at)))))

(local
 (defthm fn-cops-settle-pool-state
  (equal (fn-aec-pool-statep (mv-nth 3 (fn-icr-settle token fuel backing pool))) (fn-aec-pool-statep pool))
  :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-owner-page-read-keep-ledger fn-ibp-connection-read fn-ibp-connection-release
            fn-ich-row-release-ready fn-prs-vectorp fn-prs-below fn-ich-tokenp fn-owner-page-read-ledger
            fn-prl-nth fn-prl-build fn-omk-at)))))

(local
 (defthm fn-cops-abort-pool-state
  (equal (fn-aec-pool-statep (mv-nth 3 (fn-icr-abort token fuel backing pool))) (fn-aec-pool-statep pool))
  :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-owner-page-read-keep-ledger fn-icr-settle fn-ibp-connection-event
            fn-prs-vectorp fn-prs-below fn-ich-tokenp fn-owner-page-read-ledger fn-prl-nth fn-prl-build fn-omk-at fn-omk-widthp)))))

(local
 (defthm fn-cops-reserve-register-pool-state
  (equal (fn-aec-pool-statep (mv-nth 4 (fn-ics-reserve-register id demand fuel backing pool))) (fn-aec-pool-statep pool))
  :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-icr-reserve fn-icr-register fn-icr-abort fn-omk-at floor)))))

(defthm fn-owner-index-connection-start-preserves-carried-pool
 (implies (fn-aec-pool-statep fn-page-read-pool)
  (fn-aec-pool-statep
   (mv-nth 5 (fn-owner-index-connection-start kind family address peer fn-mio$c fn-page-read-pool state))))
 :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-ics-reserve-register fn-cop-issuer-domainp fn-owner-core
            fn-owner-connection-operation-ticket fn-owner-connection-operation-installation fn-cop-octets-match)))
 :rule-classes nil)

(local
 (defthm fn-cops-keep-ledger-pool-rest
  (equal (cdr (fn-owner-page-read-keep-ledger ledger pool)) (cdr pool))
  :hints (("Goal" :in-theory (enable fn-owner-page-read-keep-ledger update-fn-prp-data)))))

(local
 (defthm fn-cops-reserve-pool-rest
  (equal (cdr (mv-nth 3 (fn-icr-reserve id demand backing pool))) (cdr pool))
  :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-owner-page-read-keep-ledger fn-prs-issue fn-prs-vectorp fn-icr-candidate
            fn-owner-page-read-ledger fn-prl-nth fn-prl-build fn-omk-at)))))

(local
 (defthm fn-cops-settle-pool-rest
  (equal (cdr (mv-nth 3 (fn-icr-settle token fuel backing pool))) (cdr pool))
  :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-owner-page-read-keep-ledger fn-ibp-connection-read fn-ibp-connection-release
            fn-ich-row-release-ready fn-prs-vectorp fn-prs-below fn-ich-tokenp fn-owner-page-read-ledger
            fn-prl-nth fn-prl-build fn-omk-at)))))

(local
 (defthm fn-cops-abort-pool-rest
  (equal (cdr (mv-nth 3 (fn-icr-abort token fuel backing pool))) (cdr pool))
  :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-owner-page-read-keep-ledger fn-icr-settle fn-ibp-connection-event
            fn-prs-vectorp fn-prs-below fn-ich-tokenp fn-owner-page-read-ledger fn-prl-nth fn-prl-build fn-omk-at fn-omk-widthp)))))

(local
 (defthm fn-cops-reserve-register-pool-rest
  (equal (cdr (mv-nth 4 (fn-ics-reserve-register id demand fuel backing pool))) (cdr pool))
  :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-icr-reserve fn-icr-register fn-icr-abort fn-omk-at floor)))))

(defthm fn-owner-index-connection-start-retains-allocation-frame
 (equal
  (cdr (mv-nth 5 (fn-owner-index-connection-start kind family address peer fn-mio$c fn-page-read-pool state)))
  (cdr fn-page-read-pool))
 :hints (("Goal" :in-theory
   (disable fn-aec-pool-statep fn-ics-reserve-register fn-cop-issuer-domainp fn-owner-core
            fn-owner-connection-operation-ticket fn-owner-connection-operation-installation fn-cop-octets-match)))
 :rule-classes nil)
