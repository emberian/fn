; Staged SAME-pool fixed-current driver. Operation-derived constructor demand
; and selected guarded callback installation are separate prerequisites.
(in-package "ACL2")
(include-book "../books/receiver-capacity-current")
(include-book "receiver-turn-resource-host")
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
                      (fn-page-read-pool (fn-owner-page-read-keep-ledger ledger1 fn-page-read-pool))
                      (fn-rx-capacity-current (update-fn-rxcc-phase :reserved fn-rx-capacity-current)))
                 (mv :admitted token fn-rx-capacity-current fn-page-read-pool))))))))
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
  (if (not (and (fn-rxcc-exactp token fn-rx-capacity-current)
                (eq (fn-rxcc-phase fn-rx-capacity-current) :allocating)
                (fn-rxc-uninitializedp fn-rx-carry)
                (fn-rxt-installation-freshp fn-receiver-turn)))
      (mv :stale-capacity fn-octets-rx fn-rx-carry fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
    ; The actual factory supplies one fresh provider after the allocating
    ; fence. Unknown constructor/resize outcomes keep that fence and debt.
    (let* ((fn-rx-capacity-current
            (update-fn-rxcc-phase :resizing fn-rx-capacity-current))
           (fn-octets-rx (fn-octets-rx-reserve 4096 fn-octets-rx)))
      (mv-let (word ledger1 fn-rx-capacity-current)
        (fn-rx-current-resize-return-prepare token (fn-owner-page-read-ledger fn-page-read-pool)
                                           fn-rx-capacity-current)
        (if (not (eq word :install-pool))
            (mv word fn-octets-rx fn-rx-carry fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
          (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger1 fn-page-read-pool)))
            (mv-let (installed fn-rx-capacity-current)
              (fn-rxcc-installed-publish token fn-rx-capacity-current)
              (if (not (eq installed :installed))
                  (mv installed fn-octets-rx fn-rx-carry fn-receiver-turn fn-rx-capacity-current fn-page-read-pool)
                (let* ((fn-rx-carry (update-fn-rxc-token token fn-rx-carry))
                       (fn-rx-carry (update-fn-rxc-instance (fn-rxcc-instance fn-rx-capacity-current) fn-rx-carry))
                       (fn-rx-carry (update-fn-rxc-capacity 4096 fn-rx-carry))
                       ; Publish the once-only paired turn anchor last.
                       (fn-receiver-turn (update-fn-rxt-receipt
                         (list :receiver-install token (fn-rxcc-instance fn-rx-capacity-current))
                         fn-receiver-turn)))
                  (mv :installed fn-octets-rx fn-rx-carry fn-receiver-turn fn-rx-capacity-current fn-page-read-pool))))))))))
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
; Exception cleanup derives the retained authority from the actual control,
; including a cut before reserve returned its token. No host token guessing,
; refund, retry, reset or claim that a constructor/alias actually returned.
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
