; Actual START's input/identity guards, full five-coordinate issuer preflight,
; retained UPDATE-NTH/STATE branches. The reserve/register/abort callee remains
; an explicitly named refinement obligation, not assigned a guessed tariff.
(in-package "ACL2")
(include-book "connection-prepare-source-cost")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-copsc-start-raw-fields
 (and (equal (fn-atsc-value (list value cells ops calls)) value)
      (equal (fn-atsc-cells (list value cells ops calls)) (nfix cells))
      (equal (fn-atsc-ops (list value cells ops calls)) ops)
      (equal (fn-atsc-sites (list value cells ops calls)) calls))
 :hints (("Goal" :in-theory (enable fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-atsc-at)))))
(defun fn-copsc-start-check (ticket installation kind family address peer mode turns ownerid epoch)
 (declare (xargs :guard t))
 (let ((quantum (nfix (fn-omk-at 14 ticket))))
  (if (not (and (fn-omk-widthp ticket 16) (symbolp kind) (symbolp family)
                 (eq (fn-omk-at 0 ticket) :connection-operation-ticket)
                 (eq (fn-omk-at 1 ticket) :prepaid)
                 (member-eq mode '(:active :draining)) (posp turns)
                 (eq kind (fn-omk-at 2 ticket)) (eq family (fn-omk-at 3 ticket))))
      (list nil 0 nil (list (list :start-prefix ticket kind family mode turns)))
    (let ((a (fn-copc-octets-match address (fn-omk-at 4 ticket) quantum)))
     (if (not (fn-atsc-value a)) a
       (let ((p (fn-copc-octets-match peer (fn-omk-at 5 ticket) quantum)))
        (list (and (fn-atsc-value p) (equal ownerid (fn-omk-at 6 ticket))
                   (equal epoch (fn-omk-at 9 ticket))
                   (equal (fn-omk-at 1 installation) (fn-omk-at 10 ticket)))
              0 (fn-atsc-append (fn-atsc-ops a) (fn-atsc-ops p))
              (fn-atsc-append (fn-atsc-sites a) (fn-atsc-sites p)))))))))

(local (defthm fn-copsc-start-check-value
 (equal (fn-atsc-value (fn-copsc-start-check ticket installation kind family address peer mode turns ownerid epoch))
  (and (fn-omk-widthp ticket 16) (symbolp kind) (symbolp family)
       (eq (fn-omk-at 0 ticket) :connection-operation-ticket) (eq (fn-omk-at 1 ticket) :prepaid)
       (member-eq mode '(:active :draining)) (posp turns)
       (eq kind (fn-omk-at 2 ticket)) (eq family (fn-omk-at 3 ticket))
       (fn-cop-octets-match address (fn-omk-at 4 ticket) (nfix (fn-omk-at 14 ticket)))
       (fn-cop-octets-match peer (fn-omk-at 5 ticket) (nfix (fn-omk-at 14 ticket)))
       (equal ownerid (fn-omk-at 6 ticket)) (equal epoch (fn-omk-at 9 ticket))
       (equal (fn-omk-at 1 installation) (fn-omk-at 10 ticket))))
 :hints (("Goal" :in-theory (disable fn-copc-octets-match fn-cop-octets-match
                                     fn-atsc-value fn-atsc-ops fn-atsc-sites)))))

(defun fn-copsc-start (kind family address peer fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool state)
  :guard (and (boundp-global 'fn-owner state) (fn-aec-pool-statep fn-page-read-pool))
  :verify-guards nil))
 (let* ((ticket (fn-owner-connection-operation-ticket state))
        (installation (fn-owner-connection-operation-installation state)))
  (if (not ticket)
      (mv nil :unsupported-runtime nil 0 fn-mio$c fn-page-read-pool state (list nil 0 nil '(missing-ticket)))
    (let ((check (fn-copsc-start-check ticket installation kind family address peer
                   (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-active-turns fn-page-read-pool)
                   (fn-own-next-id (fn-owner-core state)) (fn-prp-alloc-epoch fn-page-read-pool))))
     (if (not (fn-atsc-value check))
         (mv nil :recovery-required (fn-omk-at 15 ticket) (nfix (fn-omk-at 13 ticket))
             fn-mio$c fn-page-read-pool state check)
       (let* ((intent (fn-coptc-update 1 :start-intent ticket))
              (state (f-put-global 'fn-owner-connection-operation-ticket (fn-atsc-value intent) state))
              (domain (fn-copc-issuer-domain (fn-owner-page-read-ledger fn-page-read-pool)
                           (fn-omk-at 12 ticket) (fn-omk-at 4 installation)))
              (prefix (fn-copsc-join check (fn-copsc-join intent domain))))
        (if (not (fn-atsc-value domain))
            (mv nil :recovery-required nil (nfix (fn-omk-at 13 ticket))
                fn-mio$c fn-page-read-pool state prefix)
          (mv-let (word token left fn-mio$c fn-page-read-pool)
           (fn-mio-connection-reserve-register (fn-omk-at 6 ticket) (fn-omk-at 12 ticket)
                                              (nfix (fn-omk-at 13 ticket)) fn-mio$c fn-page-read-pool)
           (let* ((phase (cond ((eq word :reserved) :started)
                              ((or token (eq word :recovery-required)) :start-intent) (t :refused)))
                  (middle (fn-coptc-update 1 phase ticket))
                  (done (fn-coptc-update 15 token (fn-atsc-value middle)))
                  (state (f-put-global 'fn-owner-connection-operation-ticket (fn-atsc-value done) state)))
            (mv nil word token left fn-mio$c fn-page-read-pool state
                (fn-copsc-join prefix (fn-copsc-join middle
                   (fn-copsc-join done (list nil 0 nil
                     (list (list 'fn-mio-connection-reserve-register
                       (list (fn-omk-at 6 ticket) (fn-omk-at 12 ticket) (nfix (fn-omk-at 13 ticket)))
                       (list word token left))))))))))))))))

)

(defthm fn-copsc-start-observes-complete-actual-result
 (equal (let ((seen (fn-copsc-start kind family address peer mio pool state)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen)
                (mv-nth 4 seen) (mv-nth 5 seen) (mv-nth 6 seen)))
        (fn-owner-index-connection-start kind family address peer mio pool state))
 :hints (("Goal" :in-theory
  (disable fn-copsc-start-check fn-copc-issuer-domain fn-cop-issuer-domainp
           fn-coptc-update fn-atsc-value fn-atsc-ops fn-atsc-sites fn-atsc-cells
           fn-copsc-join fn-mio-connection-reserve-register fn-owner-core
           fn-owner-connection-operation-ticket fn-owner-connection-operation-installation
           fn-omk-at fn-omk-widthp)))
 :rule-classes nil)

(local (defthm fn-copsc-start-width-list
 (implies (fn-omk-widthp x n) (true-listp x))
 :hints (("Goal" :in-theory (enable fn-omk-widthp)))))
(local (defthm fn-copsc-start-phase-list
 (implies (fn-omk-widthp x 16) (true-listp (update-nth 1 phase x)))
 :hints (("Goal" :in-theory (disable fn-omk-widthp update-nth true-listp)
  :use ((:instance fn-copsc-start-width-list (n 16))
        (:instance true-listp-update-nth (l x) (key 1) (val phase)))))))
(verify-guards fn-copsc-start
 :hints (("Goal" :in-theory
  (e/d (true-listp-update-nth)
       (fn-copsc-start-check fn-mio-connection-reserve-register fn-aec-pool-statep
        fn-copc-issuer-domain fn-copsc-join fn-owner-core fn-coptc-update
        fn-owner-connection-operation-ticket fn-owner-connection-operation-installation
        fn-omk-at fn-omk-widthp fn-atsc-value fn-atsc-ops fn-atsc-cells fn-atsc-sites)))))
