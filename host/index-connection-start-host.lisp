; Private installed operation composition. No public demand/tariff/ready flag.
; Native holds owner -> extent continuously across prepare/start/open/epilogue.
; The installation global has ONE genuine producer (the selected runtime
; installer); this leaf deliberately contains no installation setter.
(in-package "ACL2")
(include-book "../books/owner-state-accessors")
(include-book "../books/index-connection-start")
(include-book "../books/connection-operation-cost")
(include-book "connection-operation-ticket-host")

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
    (let ((installation (fn-owner-connection-operation-installation state))
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
  :guard (boundp-global 'fn-owner state) :verify-guards nil))
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
