; Mount-specific actual registered generation lifetime. HistorySource9 is
; not article authority. This uses current installed Pub19 and SAME PRS.
(in-package "ACL2")
(include-book "ninep-session")
(include-book "index-backing-generations")
(include-book "page-read-pool-state")
(include-book "page-read-counter-transaction")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-9pm-nats-true-list
 (implies (fn-prs-nats-p x) (true-listp x))
 :hints (("Goal" :in-theory (enable fn-prs-nats-p)))))
(local (defthm fn-9pm-vector-true-list
 (implies (fn-prs-vectorp x) (true-listp x))
 :hints (("Goal" :in-theory (enable fn-prs-vectorp)))))

(defun fn-9p-mount-current-generation (fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard t))
 (let* ((association (fn-ibp-current-publication fn-mio$c))
        (token (fn-omk-at 1 association)))
  (if (and (eq (fn-omk-at 0 association) :installed-publication)
           (fn-ibp-generation-tokenp token)) token nil)))

; Internal demand is the actual ninep-mount installed evaluator's result.
; Neither native entry nor a wire request accepts this argument. Public
; acquisition below refuses before this when that producer is absent.
; The whole allocator turn must cover entry/intent/PRS/retention/exit costs.
(defun fn-9p-mount-reserve-internal
 (demand fuel fn-ninep-session fn-mio$c fn-page-read-pool)
 (declare (xargs :stobjs (fn-ninep-session fn-mio$c fn-page-read-pool)
                 :guard (natp fuel) :verify-guards nil))
 (let ((generation (fn-9p-mount-current-generation fn-mio$c)))
  (cond ((not (and (eq (fn-prp-mode fn-page-read-pool) :served)
                   (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining))
                   (eq (fn-9ps-phase fn-ninep-session) :base)
                   (eq (fn-9ps-mount-phase fn-ninep-session) :empty)
                   (not (fn-9ps-mount-token fn-ninep-session))
                   (not (fn-9ps-mount-source fn-ninep-session))
                   (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)
                   generation))
         (mv :unavailable nil fuel fn-ninep-session fn-mio$c fn-page-read-pool))
        (t
         (mv-let (word row left) (fn-mio-generation-read generation fuel fn-mio$c)
          (if (not (and (eq word :present) (natp left)
                        (eq (fn-omk-at 7 row) :live)
                        (equal (fn-omk-at 3 row) 1)
                        (fn-ipub-shapep (fn-omk-at 2 row))))
              (mv (if (eq word :yield) :yield :unavailable) nil left
                  fn-ninep-session fn-mio$c fn-page-read-pool)
            (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
                   (next (fn-prl-nth 2 ledger))
                   (fn-ninep-session
                    (update-fn-9ps-mount-intent
                     (list :ninep-mount-intent nil generation demand :issue-intent
                           (fn-omk-at 2 row)) fn-ninep-session))
                   (fn-ninep-session (update-fn-9ps-mount-phase :issue-intent fn-ninep-session)))
             (mv-let (issued-word issued charged)
              (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
                            (fn-prl-nth 1 ledger) next
                            (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
              (if (not (eq issued-word :admitted))
                  (let ((fn-ninep-session (update-fn-9ps-mount-phase :refused fn-ninep-session)))
                   (mv issued-word nil left fn-ninep-session fn-mio$c fn-page-read-pool))
                (let* ((next-ledger (fn-prl-build (fn-prl-nth 0 ledger) charged issued
                                      (fn-prl-nth 3 ledger) (fn-prl-baseline ledger)))
                       (token (list :ninep-mount next))
                       (continuation (list :ninep-mount-issued token generation demand
                                           next-ledger (fn-omk-at 2 row))))
                 (mv-let (publication-word receipt fn-page-read-pool)
                  (fn-owner-page-read-counter-begin next-ledger next :ninep-mount
                                                    continuation fn-page-read-pool)
                  (if (not (eq publication-word :counter-publishing))
                      (let* ((fn-ninep-session
                              (update-fn-9ps-mount-intent continuation fn-ninep-session))
                             (fn-ninep-session (update-fn-9ps-mount-phase :fenced fn-ninep-session))
                             (fn-page-read-pool (update-fn-prp-mode continuation fn-page-read-pool))
                             (fn-page-read-pool (update-fn-prp-alloc-mode :recovery fn-page-read-pool)))
                       (mv :recovery-required nil left fn-ninep-session fn-mio$c fn-page-read-pool))
                    (let* ((fn-ninep-session
                            (update-fn-9ps-mount-intent
                             (list :ninep-mount-intent token generation demand :reserved
                                   (fn-omk-at 2 row)) fn-ninep-session))
                           (fn-ninep-session (update-fn-9ps-mount-token token fn-ninep-session))
                           (fn-ninep-session (update-fn-9ps-mount-phase :reserved fn-ninep-session)))
                     (mv-let (finish-word fn-page-read-pool)
                      (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
                      (if (eq finish-word :published)
                          (mv :reserved token left fn-ninep-session fn-mio$c fn-page-read-pool)
                        (let ((fn-ninep-session (update-fn-9ps-mount-phase :fenced fn-ninep-session)))
                         (mv :recovery-required nil left fn-ninep-session fn-mio$c fn-page-read-pool))))))))))))))))

)

; Retain intent precedes the actual generation counter change. A raw escape
; leaves :pin-intent and cannot retry retain. A successful retry of :held
; observes exactly the same immutable source and performs no second retain.
(defun fn-9p-mount-pin-step (fuel fn-ninep-session fn-mio$c)
 (declare (xargs :stobjs (fn-ninep-session fn-mio$c)
                 :guard (natp fuel) :verify-guards nil))
 (let* ((intent (fn-9ps-mount-intent fn-ninep-session))
        (generation (fn-omk-at 2 intent))
        (phase (fn-9ps-mount-phase fn-ninep-session)))
  (cond ((eq phase :held) (mv :held (fn-9ps-mount-token fn-ninep-session) fuel fn-ninep-session fn-mio$c))
        ((not (and (eq phase :reserved) (eq (fn-omk-at 0 intent) :ninep-mount-intent)
                   (equal (fn-omk-at 1 intent) (fn-9ps-mount-token fn-ninep-session))
                   (fn-ibp-generation-tokenp generation)))
         (mv :recovery-required nil fuel fn-ninep-session fn-mio$c))
        (t
         ; A full depth envelope avoids a partially traversed mutating call.
         (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
          (word publication left fn-ninep-session fn-index-backing)
          (let ((depth (fn-ibp-slot-depth fn-index-backing)))
           (if (<= fuel depth) (mv :yield nil fuel fn-ninep-session fn-index-backing)
            (let ((fn-ninep-session (update-fn-9ps-mount-phase :pin-intent fn-ninep-session)))
             (mv-let (word publication left fn-index-backing)
              (fn-ibp-generation-reference generation :retain :pin nil fuel fn-index-backing)
              (if (not (eq word :retained))
                  (let ((fn-ninep-session (update-fn-9ps-mount-phase :reserved fn-ninep-session)))
                   (mv word nil left fn-ninep-session fn-index-backing))
                (let* ((fn-ninep-session (update-fn-9ps-mount-source publication fn-ninep-session))
                       (fn-ninep-session (update-fn-9ps-mount-phase :held fn-ninep-session)))
                 (mv :held publication left fn-ninep-session fn-index-backing)))))))
          (mv word (if (eq word :held) (fn-9ps-mount-token fn-ninep-session) nil)
              left fn-ninep-session fn-mio$c))))))

; Quiescence is produced by the bounded session scan after definite returns,
; not a supplied joined flag. The generation drop and reusable refund each
; occur once; spent identity/NEXT survive. Unknown raw cuts fence the intent.
(defun fn-9p-mount-return-current (fuel fn-ninep-session fn-mio$c fn-page-read-pool)
 (declare (xargs :stobjs (fn-ninep-session fn-mio$c fn-page-read-pool)
                 :guard (natp fuel) :verify-guards nil))
 (let* ((intent (fn-9ps-mount-intent fn-ninep-session))
        (token (fn-9ps-mount-token fn-ninep-session))
        (generation (fn-omk-at 2 intent)) (demand (fn-omk-at 3 intent))
        (ledger (fn-owner-page-read-ledger fn-page-read-pool)))
  (cond
   ((not (and (eq (fn-prp-mode fn-page-read-pool) :served)
              (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining))))
    (mv :recovery-required fuel fn-ninep-session fn-mio$c fn-page-read-pool))
   ((eq (fn-9ps-mount-phase fn-ninep-session) :returned)
    (mv :already-returned fuel fn-ninep-session fn-mio$c fn-page-read-pool))
   ((not (and (eq (fn-9ps-phase fn-ninep-session) :mount-return-ready)
              (eq (fn-9ps-mount-phase fn-ninep-session) :held)
              (eq (fn-omk-at 0 intent) :ninep-mount-intent)
              (fn-omk-widthp token 2) (eq (fn-omk-at 0 token) :ninep-mount)
              (natp (fn-omk-at 1 token)) (equal (fn-omk-at 1 intent) token)
              (fn-ibp-generation-tokenp generation)
              (fn-prs-vectorp demand) (fn-prs-vectorp (fn-prl-nth 1 ledger))
              (fn-prs-below demand (fn-prl-nth 1 ledger))))
    (mv :unavailable fuel fn-ninep-session fn-mio$c fn-page-read-pool))
   (t
    (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
     (word left fn-ninep-session fn-index-backing fn-page-read-pool)
     (if (<= fuel (fn-ibp-slot-depth fn-index-backing))
         (mv :yield fuel fn-ninep-session fn-index-backing fn-page-read-pool)
       (mv-let (prepare-word prepared fn-page-read-pool)
        (fn-owner-page-read-counter-prepare (fn-omk-at 1 token) :ninep-mount-return
                                           intent fn-page-read-pool)
        (if (not (eq prepare-word :counter-preparing))
            (mv prepare-word fuel fn-ninep-session fn-index-backing fn-page-read-pool)
          (let ((fn-ninep-session (update-fn-9ps-mount-phase :return-intent fn-ninep-session)))
           (mv-let (drop-word publication left fn-index-backing)
            (fn-ibp-generation-reference generation :drop :pin nil fuel fn-index-backing)
            (declare (ignore publication))
            (if (not (member-eq drop-word '(:live :retiring)))
                (mv :recovery-required left fn-ninep-session fn-index-backing fn-page-read-pool)
              (mv-let (apply-word receipt fn-page-read-pool)
               (fn-owner-page-read-counter-apply
                (fn-prl-build (fn-prl-nth 0 ledger)
                              (fn-prs-release-reusable (fn-prl-nth 1 ledger) demand)
                              (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))
                prepared fn-page-read-pool)
               (if (not (eq apply-word :counter-publishing))
                   (mv :recovery-required left fn-ninep-session fn-index-backing fn-page-read-pool)
                 (let* ((fn-ninep-session (update-fn-9ps-mount-source nil fn-ninep-session))
                        (fn-ninep-session (update-fn-9ps-mount-token nil fn-ninep-session))
                        (fn-ninep-session (update-fn-9ps-mount-phase :returned fn-ninep-session)))
                  (mv-let (finish-word fn-page-read-pool)
                   (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
                   (if (eq finish-word :published)
                       (mv :returned left fn-ninep-session fn-index-backing fn-page-read-pool)
                     (let ((fn-ninep-session (update-fn-9ps-mount-phase :fenced fn-ninep-session)))
                      (mv :recovery-required left fn-ninep-session fn-index-backing fn-page-read-pool)))))))))))))
     (mv word left fn-ninep-session fn-mio$c fn-page-read-pool))))))

; Definite failure before any generation retain can settle its exact debit.
; :pin-intent/:return-intent are uncertain and categorically excluded.
(defun fn-9p-mount-abort-unpinned (fn-ninep-session fn-page-read-pool)
 (declare (xargs :stobjs (fn-ninep-session fn-page-read-pool) :guard t :verify-guards nil))
 (let* ((intent (fn-9ps-mount-intent fn-ninep-session))
        (token (fn-9ps-mount-token fn-ninep-session))
        (demand (fn-omk-at 3 intent))
        (ledger (fn-owner-page-read-ledger fn-page-read-pool)))
  (if (not (and (eq (fn-prp-mode fn-page-read-pool) :served)
                (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining))
                (eq (fn-9ps-mount-phase fn-ninep-session) :reserved)
                (not (fn-9ps-mount-source fn-ninep-session))
                (eq (fn-omk-at 0 intent) :ninep-mount-intent)
                (fn-omk-widthp token 2) (eq (fn-omk-at 0 token) :ninep-mount)
                (natp (fn-omk-at 1 token)) (equal (fn-omk-at 1 intent) token)
                (fn-prs-vectorp demand) (fn-prs-vectorp (fn-prl-nth 1 ledger))
                (fn-prs-below demand (fn-prl-nth 1 ledger))))
      (mv :unavailable fn-ninep-session fn-page-read-pool)
    (mv-let (word receipt fn-page-read-pool)
     (fn-owner-page-read-counter-begin
      (fn-prl-build (fn-prl-nth 0 ledger)
                    (fn-prs-release-reusable (fn-prl-nth 1 ledger) demand)
                    (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-baseline ledger))
      (fn-omk-at 1 token) :ninep-mount-abort intent fn-page-read-pool)
     (if (not (eq word :counter-publishing))
         (mv word fn-ninep-session fn-page-read-pool)
       (let* ((fn-ninep-session (update-fn-9ps-mount-phase :abort-intent fn-ninep-session))
              (fn-ninep-session (update-fn-9ps-mount-token nil fn-ninep-session))
              (fn-ninep-session (update-fn-9ps-mount-phase :returned fn-ninep-session)))
        (mv-let (finish-word fn-page-read-pool)
         (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
         (if (eq finish-word :published)
             (mv :aborted fn-ninep-session fn-page-read-pool)
           (let ((fn-ninep-session (update-fn-9ps-mount-phase :fenced fn-ninep-session)))
            (mv :recovery-required fn-ninep-session fn-page-read-pool))))))))))

(verify-guards fn-9p-mount-reserve-internal)
(verify-guards fn-9p-mount-pin-step)
(verify-guards fn-9p-mount-return-current
 :hints (("Goal" :in-theory
          (disable fn-ibp-generation-reference fn-ibp-generation-tokenp
                   fn-ninep-sessionp fn-page-read-poolp fn-prs-vectorp))))
(verify-guards fn-9p-mount-abort-unpinned
 :hints (("Goal" :in-theory
          (disable fn-ninep-sessionp fn-page-read-poolp fn-prs-vectorp))))

(defthm fn-9pm-held-replay-complete-effect
 (implies (equal (fn-9ps-mount-phase fn-ninep-session) :held)
  (equal (fn-9p-mount-pin-step fuel fn-ninep-session fn-mio$c)
         (list :held (fn-9ps-mount-token fn-ninep-session) fuel
               fn-ninep-session fn-mio$c)))
 :hints (("Goal" :in-theory (enable fn-9p-mount-pin-step))))

(defthm fn-9pm-returned-replay-complete-effect
 (implies (and (equal (fn-9ps-mount-phase fn-ninep-session) :returned)
               (eq (fn-prp-mode fn-page-read-pool) :served)
               (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining)))
  (equal (fn-9p-mount-return-current fuel fn-ninep-session fn-mio$c fn-page-read-pool)
         (list :already-returned fuel fn-ninep-session fn-mio$c fn-page-read-pool)))
 :hints (("Goal" :in-theory (enable fn-9p-mount-return-current))))

(defthm fn-9pm-uncertain-pin-cannot-abort-debit
 (implies (member-eq (fn-9ps-mount-phase fn-ninep-session) '(:pin-intent :return-intent))
  (equal (fn-9p-mount-abort-unpinned fn-ninep-session fn-page-read-pool)
         (list :unavailable fn-ninep-session fn-page-read-pool)))
 :hints (("Goal" :in-theory (enable fn-9p-mount-abort-unpinned))))
