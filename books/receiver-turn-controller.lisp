; Receiver custody only: not connection publication/view authority.
; Admission remains supplied-demand SOURCE-NOTREADY until canonical operation
; and controller-constructor demand are qualified. No return/reset API exists
; before actual result/retained-job receipt and alias release are joined.
(in-package "ACL2")
(include-book "receiver-provider")
(include-book "page-read-pool-state")
(defstobj fn-receiver-turn
 (fn-rxt-ticket :initially nil)
 (fn-rxt-source :initially nil)
 (fn-rxt-phase :initially :idle)
 (fn-rxt-demand :initially nil)
 (fn-rxt-job :initially nil)
 (fn-rxt-receipt :initially nil)
 :inline t)
(defun fn-rxt-ticket-make (nonce)
 (declare (xargs :guard t))
 (list :receiver-turn nonce))
(defun fn-rxt-source-make (ticket receiver-token instance)
 (declare (xargs :guard t))
 (list :receiver-source ticket receiver-token instance))
(defun fn-rxt-issued-demandp (demand)
 (declare (xargs :guard t))
 (and (fn-prs-vectorp demand)
      (equal (fn-prl-nth 1 demand) 0)
      (equal (fn-prl-nth 2 demand) 0)
      (equal (fn-prl-nth 3 demand) 0)
      (equal (fn-prl-nth 4 demand) 1)))
(defun fn-rxt-installed-anchor-p (receiver-token fn-rx-provider fn-receiver-turn)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn)))
 (let ((receipt (fn-rxt-receipt fn-receiver-turn)))
  (and (consp receipt) (eq (car receipt) :receiver-install)
       (consp (cdr receipt)) (equal (cadr receipt) receiver-token)
       (consp (cddr receipt))
       (equal (caddr receipt) (fn-rxp-instance fn-rx-provider))
       (null (cdddr receipt)))))
(defun fn-owner-rx-turn-begin
 (receiver-token demand fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (cond
  ((not (and (eq (fn-prp-mode fn-page-read-pool) :served)
             (fn-rxp-currentp receiver-token fn-rx-provider)
             (fn-rxt-installed-anchor-p receiver-token fn-rx-provider fn-receiver-turn)))
   (mv :receiver-unavailable fn-receiver-turn fn-page-read-pool))
  ((not (and (eq (fn-rxt-phase fn-receiver-turn) :idle)
             (null (fn-rxt-ticket fn-receiver-turn))
             (null (fn-rxt-source fn-receiver-turn))
             (null (fn-rxt-demand fn-receiver-turn))
             (null (fn-rxt-job fn-receiver-turn))))
   (mv :receiver-turn-busy fn-receiver-turn fn-page-read-pool))
  ((not (fn-rxt-issued-demandp demand))
   (mv :invalid-receiver-turn-demand fn-receiver-turn fn-page-read-pool))
  (t
   (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
          (next (fn-prl-nth 2 ledger)))
    (mv-let (word next1 charged1)
      (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                    '(0 0 0 0 0) (fn-prl-nth 1 ledger)
                    next (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
      (if (not (eq word :admitted))
          (mv word fn-receiver-turn fn-page-read-pool)
       (let* ((ticket (fn-rxt-ticket-make next))
              (source (fn-rxt-source-make ticket receiver-token
                                        (fn-rxp-instance fn-rx-provider)))
              (fn-page-read-pool
               (fn-owner-page-read-keep-ledger
                (fn-prl-build (fn-prl-nth 0 ledger) charged1 next1
                              (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger))
                fn-page-read-pool))
              (fn-receiver-turn (update-fn-rxt-ticket ticket fn-receiver-turn))
              (fn-receiver-turn (update-fn-rxt-source source fn-receiver-turn))
              (fn-receiver-turn (update-fn-rxt-demand demand fn-receiver-turn))
              (fn-receiver-turn (update-fn-rxt-phase :live fn-receiver-turn)))
         (mv :admitted fn-receiver-turn fn-page-read-pool))))))))
(defun fn-owner-rx-turn-source (fn-receiver-turn)
 (declare (xargs :stobjs fn-receiver-turn))
 (if (and (eq (fn-rxt-phase fn-receiver-turn) :live)
          (fn-rxt-ticket fn-receiver-turn))
     (fn-rxt-source fn-receiver-turn) nil))
; The capacity-only provider range is not incoming custody authority. This
; paired gate reads the current fixed turn slot and the same pool. Its carried
; association is established by the paired installer and actual begin, not by
; equality of a connection id, publication holder, or served-step result.
(defun fn-rxt-owned-claim-p
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let* ((receiver-token (fn-rxp-token fn-rx-provider))
        (source (fn-rxt-source fn-receiver-turn))
        (ledger (fn-owner-page-read-ledger fn-page-read-pool))
        (charged (fn-prl-nth 1 ledger)))
  (and (eq (fn-prp-mode fn-page-read-pool) :served)
       (consp ticket) (eq (car ticket) :receiver-turn)
       (consp (cdr ticket)) (natp (cadr ticket)) (null (cddr ticket))
       (equal ticket (fn-rxt-ticket fn-receiver-turn))
       (natp (fn-prl-nth 2 ledger))
       (< (cadr ticket) (fn-prl-nth 2 ledger))
       (fn-rxt-installed-anchor-p receiver-token fn-rx-provider fn-receiver-turn)
       (consp source) (eq (car source) :receiver-source)
       (consp (cdr source)) (equal (cadr source) ticket)
       (consp (cddr source)) (equal (caddr source) receiver-token)
       (consp (cdddr source))
       (equal (cadddr source) (fn-rxp-instance fn-rx-provider))
       (null (cddddr source))
       (fn-rxt-issued-demandp (fn-rxt-demand fn-receiver-turn))
       (fn-prs-vectorp charged)
       (fn-prs-below (fn-rxt-demand fn-receiver-turn) charged))))
(defun fn-rxt-live-claim-p
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (and (eq (fn-rxt-phase fn-receiver-turn) :live)
      (null (fn-rxt-job fn-receiver-turn))
      (fn-rxp-currentp (fn-rxp-token fn-rx-provider) fn-rx-provider)
      (fn-rxt-owned-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)))
(defun fn-owner-rx-turn-fill-range
 (ticket n limits fuel fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (if (not (fn-rxt-live-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool))
     (mv :receiver-unavailable 0 0 fuel fn-rx-provider fn-receiver-turn fn-page-read-pool)
  (mv-let (word start end left fn-rx-provider)
    (fn-rxp-fill-range (fn-rxp-token fn-rx-provider) n limits fuel fn-rx-provider)
    (mv word start end left fn-rx-provider fn-receiver-turn fn-page-read-pool))))
; Admission returns a ticket only for the newly issued turn. Busy/refused
; callers must not acquire another request's retained ticket from this entry.
(defun fn-owner-rx-turn-start
 (receiver-token demand fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (mv-let (word fn-receiver-turn fn-page-read-pool)
   (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider fn-receiver-turn fn-page-read-pool)
   (mv word (if (eq word :admitted) (fn-rxt-ticket fn-receiver-turn) nil)
       fn-receiver-turn fn-page-read-pool)))
; One fixed pending tuple per turn. Repeated NEXT reuses it; it does not
; create another range or consume the quantum a second time. Its allocation
; and retained callback overlap remain part of canonical demand, not GC credit.
(defun fn-rxt-pending-rangep (x)
 (declare (xargs :guard t))
 (and (consp x) (eq (car x) :receiver-copy)
      (consp (cdr x)) (equal (cadr x) 0)
      (consp (cddr x)) (natp (caddr x)) (<= (caddr x) 4096)
      (consp (cdddr x)) (natp (cadddr x)) (null (cddddr x))))
(defun fn-owner-rx-turn-copy-next
 (ticket n limits fuel fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let ((pending (fn-rxt-job fn-receiver-turn)))
  (if (and (eq (fn-rxt-phase fn-receiver-turn) :copy-issued)
           (fn-rxt-owned-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
           (null (fn-rxp-capacity fn-rx-provider))
           (fn-rxt-pending-rangep pending)
           (equal n (caddr pending)))
      (mv :receive-copy (cadr pending) (caddr pending) (cadddr pending)
          fn-rx-provider fn-receiver-turn fn-page-read-pool)
   (mv-let (word start end left fn-rx-provider fn-receiver-turn fn-page-read-pool)
    (fn-owner-rx-turn-fill-range ticket n limits fuel fn-rx-provider fn-receiver-turn fn-page-read-pool)
    (if (not (eq word :receive-copy))
        (mv word start end left fn-rx-provider fn-receiver-turn fn-page-read-pool)
     (mv-let (fenced fn-rx-provider)
      (fn-rxp-fence (fn-rxp-token fn-rx-provider) fn-rx-provider)
      (declare (ignore fenced))
      (let* ((fn-receiver-turn
              (update-fn-rxt-job (list :receiver-copy start end left) fn-receiver-turn))
             (fn-receiver-turn (update-fn-rxt-phase :copy-issued fn-receiver-turn)))
       (mv :receive-copy start end left fn-rx-provider fn-receiver-turn fn-page-read-pool))))))))
; This helper is private to the paired ACK below. :copied is the named native
; primitive's observation after both copy and fill publication return. It is
; not a caller's alias-joined assertion, and never settles/refunds the turn.
(defun fn-rxt-copy-publish (end fn-rx-provider fn-receiver-turn)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn)))
 (stobj-let ((fn-octets-rx (fn-rxp-octets fn-rx-provider))
             (fn-rx-carry (fn-rxp-carry fn-rx-provider)))
            (word fn-rx-carry fn-receiver-turn)
            (if (equal (fn-octets-rx-len fn-octets-rx) end)
                (let* ((fn-receiver-turn (update-fn-rxt-phase :filled fn-receiver-turn))
                       (fn-rx-carry (update-fn-rxc-capacity 4096 fn-rx-carry)))
                 (mv :receive-recorded fn-rx-carry fn-receiver-turn))
              (mv :receiver-unavailable fn-rx-carry fn-receiver-turn))
            (mv word fn-rx-provider fn-receiver-turn)))
(defun fn-owner-rx-turn-copy-ack
 (ticket start end outcome fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let ((pending (fn-rxt-job fn-receiver-turn)))
  (if (not (and (eq (fn-rxt-phase fn-receiver-turn) :copy-issued)
                (fn-rxt-owned-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
                (null (fn-rxp-capacity fn-rx-provider))
                (fn-rxt-pending-rangep pending)
                (equal start (cadr pending)) (equal end (caddr pending))))
      (mv :receiver-unavailable fn-rx-provider fn-receiver-turn fn-page-read-pool)
   (cond
    ((eq outcome :uncertain)
     (let ((fn-receiver-turn (update-fn-rxt-phase :cancelled fn-receiver-turn)))
      (mv :receive-cancelled fn-rx-provider fn-receiver-turn fn-page-read-pool)))
    ((eq outcome :copied)
     (mv-let (word fn-rx-provider fn-receiver-turn)
       (fn-rxt-copy-publish end fn-rx-provider fn-receiver-turn)
       (mv word fn-rx-provider fn-receiver-turn fn-page-read-pool)))
    (t (mv :invalid-receive-outcome fn-rx-provider fn-receiver-turn fn-page-read-pool))))))
(defun fn-owner-rx-turn-consumablep
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (and (eq (fn-rxt-phase fn-receiver-turn) :filled)
      (fn-rxt-pending-rangep (fn-rxt-job fn-receiver-turn))
      (fn-rxp-currentp (fn-rxp-token fn-rx-provider) fn-rx-provider)
      (fn-rxt-owned-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)))
(defun fn-owner-rx-turn-consumer-source
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (if (fn-owner-rx-turn-consumablep ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
     (fn-rxt-source fn-receiver-turn) nil))
(defthm fn-owner-rx-turn-begin-uses-actual-pool-nonce
 (implies
  (equal (mv-nth 0 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider
                                        fn-receiver-turn fn-page-read-pool)) :admitted)
  (and
   (equal (fn-rxt-ticket
           (mv-nth 1 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider
                                           fn-receiver-turn fn-page-read-pool)))
          (fn-rxt-ticket-make (fn-prl-nth 2 (fn-owner-page-read-ledger fn-page-read-pool))))
   (equal (fn-owner-rx-turn-source
           (mv-nth 1 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider
                                           fn-receiver-turn fn-page-read-pool)))
          (fn-rxt-source-make
           (fn-rxt-ticket-make (fn-prl-nth 2 (fn-owner-page-read-ledger fn-page-read-pool)))
           receiver-token (fn-rxp-instance fn-rx-provider)))))
 :hints (("Goal" :in-theory (enable fn-owner-rx-turn-begin
                   fn-owner-rx-turn-source fn-rxt-ticket-make
                   fn-prs-issue fn-prl-nth)))
 :rule-classes nil)
(defthm fn-owner-rx-turn-busy-preserves-pool-and-controller
 (implies
  (equal (mv-nth 0 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider
                                        fn-receiver-turn fn-page-read-pool)) :receiver-turn-busy)
  (and (equal (mv-nth 1 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider
                                        fn-receiver-turn fn-page-read-pool)) fn-receiver-turn)
       (equal (mv-nth 2 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider
                                        fn-receiver-turn fn-page-read-pool)) fn-page-read-pool)))
 :hints (("Goal" :in-theory (enable fn-owner-rx-turn-begin fn-prs-issue)))
 :rule-classes nil)
(defthm fn-owner-rx-turn-begin-spends-pool-identity-once
 (implies
  (equal (mv-nth 0 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider
                                        fn-receiver-turn fn-page-read-pool)) :admitted)
  (equal (fn-prl-nth 2
          (fn-owner-page-read-ledger
           (mv-nth 2 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider
                                           fn-receiver-turn fn-page-read-pool))))
         (+ 1 (fn-prl-nth 2 (fn-owner-page-read-ledger fn-page-read-pool)))))
 :hints (("Goal" :in-theory (enable fn-owner-rx-turn-begin fn-prs-issue
                  fn-owner-page-read-ledger fn-owner-page-read-keep-ledger
                  fn-prl-build fn-prl-nth)))
 :rule-classes nil)
(defthm fn-owner-rx-turn-begin-preserves-installation-receipt
 (equal (fn-rxt-receipt
         (mv-nth 1 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider
                                         fn-receiver-turn fn-page-read-pool)))
        (fn-rxt-receipt fn-receiver-turn))
 :hints (("Goal" :in-theory (enable fn-owner-rx-turn-begin fn-prs-issue))))
(defthm fn-owner-rx-turn-fill-range-refines-provider-range-by-definition
 (implies
  (fn-rxt-live-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
  (equal
   (fn-owner-rx-turn-fill-range ticket n limits fuel fn-rx-provider fn-receiver-turn fn-page-read-pool)
   (mv-let (word start end left provider)
    (fn-rxp-fill-range (fn-rxp-token fn-rx-provider) n limits fuel fn-rx-provider)
    (mv word start end left provider fn-receiver-turn fn-page-read-pool))))
 :hints (("Goal" :in-theory (enable fn-owner-rx-turn-fill-range)))
 :rule-classes nil)
(defthm fn-owner-rx-turn-fill-range-refuses-without-current-claim-by-definition
 (implies
  (not (fn-rxt-live-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool))
  (equal
   (fn-owner-rx-turn-fill-range ticket n limits fuel fn-rx-provider fn-receiver-turn fn-page-read-pool)
   (mv :receiver-unavailable 0 0 fuel fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 :hints (("Goal" :in-theory (enable fn-owner-rx-turn-fill-range)))
 :rule-classes nil)
(defthm fn-owner-rx-turn-copy-next-revokes-reader-readiness
 (implies
  (equal (mv-nth 0 (fn-owner-rx-turn-copy-next ticket n limits fuel
                       fn-rx-provider fn-receiver-turn fn-page-read-pool)) :receive-copy)
  (and
   (null (fn-rxp-capacity
          (mv-nth 4 (fn-owner-rx-turn-copy-next ticket n limits fuel
                       fn-rx-provider fn-receiver-turn fn-page-read-pool))))
   (equal (fn-rxt-phase
          (mv-nth 5 (fn-owner-rx-turn-copy-next ticket n limits fuel
                       fn-rx-provider fn-receiver-turn fn-page-read-pool))) :copy-issued)
   (equal (mv-nth 6 (fn-owner-rx-turn-copy-next ticket n limits fuel
                       fn-rx-provider fn-receiver-turn fn-page-read-pool)) fn-page-read-pool)))
 :hints (("Goal" :in-theory (enable fn-owner-rx-turn-copy-next
   fn-owner-rx-turn-fill-range fn-rxt-live-claim-p fn-rxp-fill-range
   fn-rxc-fill-range fn-rxp-fence fn-rxc-fence fn-rxp-capacity)))
 :rule-classes nil)
