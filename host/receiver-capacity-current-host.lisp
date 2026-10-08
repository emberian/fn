; Exact frozen DATA6 current-RX source forms from a550e0f13/17-rx-callers.
; Include assembly only; no new admission, runtime funding or activation claim.
(in-package "ACL2")
(include-book "../books/receiver-capacity-current")
(include-book "receiver-turn-resource-host")
(include-book "../books/page-read-counter-transaction")
(defun fn-owner-rx-current-reserve
  (demand fn-rx-capacity-current fn-page-read-pool)
  (declare (xargs :stobjs (fn-rx-capacity-current fn-page-read-pool) :guard t))
  (cond ((not (eq (fn-prp-mode fn-page-read-pool) :served))
         (mv :receiver-pool-unavailable nil fn-rx-capacity-current fn-page-read-pool))
        ((not (fn-rxcc-freshp fn-rx-capacity-current))
         (mv :receiver-capacity-busy nil fn-rx-capacity-current fn-page-read-pool))
        ((not (and (fn-prs-vectorp demand)
                   (equal (fn-prl-nth 1 demand) 0)
                   (equal (fn-prl-nth 2 demand) 0)
                   (equal (fn-prl-nth 3 demand) 0)
                   (equal (fn-prl-nth 4 demand) 1)))
         (mv :invalid-capacity-request nil fn-rx-capacity-current fn-page-read-pool))
        (t
         (let ((ledger (fn-owner-page-read-ledger fn-page-read-pool)))
           (mv-let (word next charged)
             (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                           '(0 0 0 0 0) (fn-prl-nth 1 ledger)
                           (fn-prl-nth 2 ledger)
                           (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
             (if (not (eq word :admitted))
                 (mv word nil fn-rx-capacity-current fn-page-read-pool)
               (let* ((instance (fn-prl-nth 2 ledger))
                      (token (list :rx-capacity instance instance 4096))
                      (ledger1 (fn-prl-build (fn-prl-nth 0 ledger) charged next
                                  (fn-prl-nth 3 ledger) (fn-prl-baseline ledger)))
                      (fn-rx-capacity-current (update-fn-rxcc-token token fn-rx-capacity-current))
                      (fn-rx-capacity-current (update-fn-rxcc-claim demand fn-rx-capacity-current))
                      (fn-rx-capacity-current (update-fn-rxcc-instance instance fn-rx-capacity-current))
                      ; No ready :reserved state before the pool commit. Any
                      ; escape leaves a nonfresh, nonallocating controller.
                      (fn-rx-capacity-current (update-fn-rxcc-phase :issuing fn-rx-capacity-current))
                      )
                 (mv-let (publication receipt fn-page-read-pool)
                   (fn-owner-page-read-counter-begin ledger1 instance :receiver-issue
                     (list :receiver-issue token demand instance) fn-page-read-pool)
                   (if (not (eq publication :counter-publishing))
                       (let* ((intent (list :receiver-issuance-recovery
                                            (fn-prp-mode fn-page-read-pool)
                                            (fn-prp-data fn-page-read-pool) ledger1 token demand))
                              (fn-page-read-pool (update-fn-prp-mode intent fn-page-read-pool))
                              (fn-page-read-pool (update-fn-prp-alloc-mode :recovery fn-page-read-pool))
                              (fn-rx-capacity-current (update-fn-rxcc-phase :fenced fn-rx-capacity-current)))
                         (mv :receiver-issuance-recovery nil fn-rx-capacity-current fn-page-read-pool))
                     (let ((fn-rx-capacity-current (update-fn-rxcc-phase :reserved fn-rx-capacity-current)))
                       (mv-let (finished fn-page-read-pool)
                         (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
                         (if (eq finished :published)
                             (mv :admitted token fn-rx-capacity-current fn-page-read-pool)
                           (let ((fn-rx-capacity-current
                                  (update-fn-rxcc-phase :fenced fn-rx-capacity-current)))
                             (mv :receiver-issuance-recovery nil fn-rx-capacity-current fn-page-read-pool))))))))))))))

(defun fn-owner-rx-current-allocation-begin
  (token fn-rx-capacity-current fn-page-read-pool)
  (declare (xargs :stobjs (fn-rx-capacity-current fn-page-read-pool) :guard t))
  (if (not (eq (fn-prp-mode fn-page-read-pool) :served))
      (mv :receiver-pool-unavailable fn-rx-capacity-current fn-page-read-pool)
    (mv-let (word fn-rx-capacity-current)
      (fn-rxcc-allocation-begin token fn-rx-capacity-current)
      (mv word fn-rx-capacity-current fn-page-read-pool))))

(defun fn-rx-current-resize-return-prepare
  (token ledger fn-rx-capacity-current)
  (declare (xargs :stobjs fn-rx-capacity-current :guard t))
  (let* ((claim (fn-rxcc-claim fn-rx-capacity-current))
         (retained (list (fn-prl-nth 0 claim) 0 0 0 0)))
    (if (not (and (fn-rxcc-exactp token fn-rx-capacity-current)
                  (eq (fn-rxcc-phase fn-rx-capacity-current) :resizing)
                  (fn-prs-vectorp claim) (fn-prs-vectorp (fn-prl-nth 1 ledger))
                  (fn-prs-vectorp (fn-prl-baseline ledger))
                  (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                                  '(0 0 0 0 0) (fn-prl-nth 1 ledger))
                  (true-listp (fn-prl-nth 1 ledger))
                  (fn-prs-below retained (fn-prl-nth 1 ledger))))
        (mv :stale-capacity ledger fn-rx-capacity-current)
      (let* ((ledger1 (fn-iqr-promoted-ledger ledger retained))
             (fn-rx-capacity-current
              (update-fn-rxcc-phase :promoting fn-rx-capacity-current)))
        (mv :install-pool ledger1 fn-rx-capacity-current)))))

(defun fn-rx-current-install-children
  (token fn-octets-rx fn-rx-carry fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
  (declare (xargs :stobjs (fn-octets-rx fn-rx-carry fn-receiver-turn
                           fn-rx-capacity-current fn-page-read-pool) :guard t))
  (if (not (and (eq (fn-prp-mode fn-page-read-pool) :served)
                (fn-rxcc-exactp token fn-rx-capacity-current)
                (eq (fn-rxcc-phase fn-rx-capacity-current) :allocating)
                (fn-rxc-uninitializedp fn-rx-carry)
                (fn-rxt-installation-freshp fn-receiver-turn)))
      (mv :stale-capacity fn-octets-rx fn-rx-carry fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
    ; Retain CURRENT pool/control references before the fallible resize. A raw
    ; escape leaves this preparing intent and the actual child/controller held.
    (mv-let (prepared prepared-receipt fn-page-read-pool)
      (fn-owner-page-read-counter-prepare (fn-prl-nth 1 token) :receiver-install
        (list :receiver-install token (fn-rxcc-claim fn-rx-capacity-current)
              (fn-rxcc-instance fn-rx-capacity-current)) fn-page-read-pool)
      (if (not (eq prepared :counter-preparing))
          (mv prepared fn-octets-rx fn-rx-carry fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
        (let* ((fn-rx-capacity-current
                (update-fn-rxcc-phase :resizing fn-rx-capacity-current))
               (fn-octets-rx (fn-octets-rx-reserve 4096 fn-octets-rx)))
          (mv-let (word ledger1 fn-rx-capacity-current)
            (fn-rx-current-resize-return-prepare token (fn-owner-page-read-ledger fn-page-read-pool)
                                               fn-rx-capacity-current)
            (if (not (eq word :install-pool))
                (let ((fn-rx-capacity-current (update-fn-rxcc-phase :fenced fn-rx-capacity-current)))
                  (mv :receiver-install-publication-recovery fn-octets-rx fn-rx-carry
                      fn-receiver-turn fn-rx-capacity-current fn-page-read-pool))
              (mv-let (publication receipt fn-page-read-pool)
                (fn-owner-page-read-counter-apply ledger1 prepared-receipt fn-page-read-pool)
                (if (not (eq publication :counter-publishing))
                    ; No rollback: actual child storage, original claim and
                    ; preparing intent survive an unsuccessful ledger apply.
                    (let ((fn-rx-capacity-current (update-fn-rxcc-phase :fenced fn-rx-capacity-current)))
                      (mv :receiver-install-publication-recovery fn-octets-rx fn-rx-carry
                          fn-receiver-turn fn-rx-capacity-current fn-page-read-pool))
                  (mv-let (installed fn-rx-capacity-current)
                    (fn-rxcc-installed-publish token fn-rx-capacity-current)
                    (if (not (eq installed :installed))
                        (let ((fn-rx-capacity-current (update-fn-rxcc-phase :fenced fn-rx-capacity-current)))
                          (mv :receiver-install-publication-recovery fn-octets-rx fn-rx-carry
                              fn-receiver-turn fn-rx-capacity-current fn-page-read-pool))
                      (let* ((fn-rx-carry (update-fn-rxc-token token fn-rx-carry))
                             (fn-rx-carry (update-fn-rxc-instance (fn-rxcc-instance fn-rx-capacity-current) fn-rx-carry))
                             (fn-rx-carry (update-fn-rxc-capacity 4096 fn-rx-carry))
                             (fn-receiver-turn (update-fn-rxt-receipt
                               (list :receiver-install token (fn-rxcc-instance fn-rx-capacity-current))
                               fn-receiver-turn)))
                        (mv-let (finished fn-page-read-pool)
                          (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
                          (if (eq finished :published)
                              (mv :installed fn-octets-rx fn-rx-carry fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
                            (let* ((fn-rx-capacity-current (update-fn-rxcc-phase :fenced fn-rx-capacity-current))
                                   (fn-rx-carry (update-fn-rxc-capacity 0 fn-rx-carry)))
                              (mv :receiver-install-publication-recovery fn-octets-rx fn-rx-carry
                                  fn-receiver-turn fn-rx-capacity-current fn-page-read-pool))))))))))))))))

(defun fn-owner-rx-current-install
  (token fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
  (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn
                           fn-rx-capacity-current fn-page-read-pool) :guard t))
  (if (not (eq (fn-prp-mode fn-page-read-pool) :served))
      (mv :receiver-pool-unavailable fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
    (stobj-let ((fn-octets-rx (fn-rxp-octets fn-rx-provider))
                (fn-rx-carry (fn-rxp-carry fn-rx-provider)))
      (word fn-octets-rx fn-rx-carry fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
      (fn-rx-current-install-children token fn-octets-rx fn-rx-carry
                                    fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
      (mv word fn-rx-provider fn-receiver-turn fn-rx-capacity-current fn-page-read-pool))))

(defun fn-owner-rx-current-fence-current
  (fn-rx-capacity-current fn-page-read-pool)
  (declare (xargs :stobjs (fn-rx-capacity-current fn-page-read-pool) :guard t))
  (cond ((fn-rxcc-freshp fn-rx-capacity-current)
         (mv :receiver-capacity-empty fn-rx-capacity-current fn-page-read-pool))
        ((eq (fn-rxcc-phase fn-rx-capacity-current) :fenced)
         (mv :receiver-capacity-retained fn-rx-capacity-current fn-page-read-pool))
        (t (let ((fn-rx-capacity-current
                  (update-fn-rxcc-phase :fenced fn-rx-capacity-current)))
             (mv :receiver-capacity-retained fn-rx-capacity-current fn-page-read-pool)))))

(defthm fn-owner-rx-current-fence-preserves-shared-pool
  (equal (mv-nth 2 (fn-owner-rx-current-fence-current fn-rx-capacity-current fn-page-read-pool))
         fn-page-read-pool))

(verify-guards fn-owner-rx-current-reserve)

(verify-guards fn-owner-rx-current-allocation-begin)

(verify-guards fn-rx-current-resize-return-prepare)

(verify-guards fn-rx-current-install-children)

(verify-guards fn-owner-rx-current-install)

(verify-guards fn-owner-rx-current-fence-current)