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
(defun fn-owner-rx-turn-begin
 (receiver-token demand fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (cond
  ((not (and (eq (fn-prp-mode fn-page-read-pool) :served)
             (fn-rxp-currentp receiver-token fn-rx-provider)))
   (mv :receiver-unavailable fn-receiver-turn fn-page-read-pool))
  ((not (and (eq (fn-rxt-phase fn-receiver-turn) :idle)
             (null (fn-rxt-ticket fn-receiver-turn))
             (null (fn-rxt-source fn-receiver-turn))
             (null (fn-rxt-demand fn-receiver-turn))
             (null (fn-rxt-job fn-receiver-turn))
             (null (fn-rxt-receipt fn-receiver-turn))))
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
