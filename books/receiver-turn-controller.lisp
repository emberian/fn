; Receiver custody only: not connection publication/view authority.
; Admission remains supplied-demand SOURCE-NOTREADY until canonical operation
; and controller-constructor demand are qualified. No return/reset API exists
; before actual result/retained-job receipt and alias release are joined.
(in-package "ACL2")
(include-book "receiver-provider")
(include-book "reader-response-disposition")
(include-book "page-read-pool-state")
(include-book "page-read-counter-transaction")
(defstobj fn-receiver-turn
 (fn-rxt-ticket :initially nil)
 (fn-rxt-source :initially nil)
 (fn-rxt-phase :initially :idle)
 (fn-rxt-demand :initially nil)
 (fn-rxt-job :initially nil)
 (fn-rxt-receipt :initially nil)
 ; Retained ordinary output custody; the original six fields stay unchanged.
 (fn-rxt-output-bundle :initially nil)
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
  ((not (eq (fn-prp-mode fn-page-read-pool) :served))
   (mv :receiver-turn-recovery fn-receiver-turn fn-page-read-pool))
  ((not (and (fn-rxp-currentp receiver-token fn-rx-provider)
             (fn-rxt-installed-anchor-p receiver-token fn-rx-provider fn-receiver-turn)))
   (mv :receiver-unavailable fn-receiver-turn fn-page-read-pool))
  ((not (and (eq (fn-rxt-phase fn-receiver-turn) :idle)
             (null (fn-rxt-ticket fn-receiver-turn))
             (null (fn-rxt-source fn-receiver-turn))
             (null (fn-rxt-demand fn-receiver-turn))
             (null (fn-rxt-job fn-receiver-turn))
             (null (fn-rxt-output-bundle fn-receiver-turn))))
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
             (source (fn-rxt-source-make ticket receiver-token (fn-rxp-instance fn-rx-provider)))
             (proposed (fn-prl-build (fn-prl-nth 0 ledger) charged1 next1
                         (fn-prl-nth 3 ledger) (fn-prl-baseline ledger)))
             (continuation (list :receiver-turn-issue ticket source demand
                            (fn-rxt-receipt fn-receiver-turn))))
       (mv-let (publish-word receipt fn-page-read-pool)
        (fn-owner-page-read-counter-begin proposed next :receiver-turn continuation fn-page-read-pool)
        (if (not (eq publish-word :counter-publishing))
         (let* ((intent (list :receiver-turn-issue-recovery
                          (fn-prp-mode fn-page-read-pool) (fn-prp-data fn-page-read-pool)
                          proposed ticket source demand (fn-rxt-receipt fn-receiver-turn)))
                (fn-page-read-pool (update-fn-prp-mode intent fn-page-read-pool))
                (fn-page-read-pool (update-fn-prp-alloc-mode :recovery fn-page-read-pool)))
          (mv :receiver-turn-recovery fn-receiver-turn fn-page-read-pool))
         (let* ((fn-receiver-turn (update-fn-rxt-ticket ticket fn-receiver-turn))
                (fn-receiver-turn (update-fn-rxt-source source fn-receiver-turn))
                (fn-receiver-turn (update-fn-rxt-demand demand fn-receiver-turn))
                (fn-receiver-turn (update-fn-rxt-phase :live fn-receiver-turn)))
          (mv-let (finish-word fn-page-read-pool)
           (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
           (if (eq finish-word :published)
            (mv :admitted fn-receiver-turn fn-page-read-pool)
            (mv :receiver-turn-recovery fn-receiver-turn fn-page-read-pool)))))))))))))
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
      (null (fn-rxt-output-bundle fn-receiver-turn))
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
  (if (and (null (fn-rxt-output-bundle fn-receiver-turn))
           (eq (fn-rxt-phase fn-receiver-turn) :copy-issued)
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
  (if (not (and (null (fn-rxt-output-bundle fn-receiver-turn))
                (eq (fn-rxt-phase fn-receiver-turn) :copy-issued)
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
; One parser actor owns the complete filled input generation. START/END
; identify its current unconsumed span; the initial preOC is evidence only.
; RC/current wire/step are installed by the actual serialized STATE producer.
(defun fn-rxt-fixed-widthp (x width)
 (declare (xargs :guard (natp width) :measure (nfix width)))
 (if (zp width) (null x)
   (and (consp x) (fn-rxt-fixed-widthp (cdr x) (- width 1)))))
(defun fn-rxt-parser-jobp (job)
 (declare (xargs :guard t))
 (and (fn-rxt-fixed-widthp job 11)
      (eq (fn-prl-nth 0 job) :receiver-parser)
      (fn-rxt-pending-rangep (fn-prl-nth 3 job))
      (natp (fn-prl-nth 4 job)) (natp (fn-prl-nth 5 job))
      (<= (fn-prl-nth 4 job) (fn-prl-nth 5 job))
      (equal (fn-prl-nth 5 job) (fn-prl-nth 2 (fn-prl-nth 3 job)))
      (natp (fn-prl-nth 10 job))
      (<= (fn-prl-nth 10 job) (+ 1 (fn-prl-nth 4 job)))))
(defun fn-rxt-parser-currentp
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let ((job (fn-rxt-job fn-receiver-turn)))
  (and (member-eq (fn-rxt-phase fn-receiver-turn) '(:parser-owned :parser-installing :response-owned))
       (fn-rxt-parser-jobp job)
       (if (member-eq (fn-rxt-phase fn-receiver-turn) '(:parser-owned :parser-installing))
           (<= (fn-prl-nth 10 job) (fn-prl-nth 4 job)) t)
       (equal (fn-prl-nth 1 job) ticket)
       (equal (fn-prl-nth 2 job) (fn-rxt-source fn-receiver-turn))
       (if (eq (fn-rxt-phase fn-receiver-turn) :parser-owned)
           (and (null (fn-rxt-output-bundle fn-receiver-turn))
                (fn-rxp-currentp (fn-rxp-token fn-rx-provider) fn-rx-provider))
         (null (fn-rxp-capacity fn-rx-provider)))
       (fn-rxt-owned-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool))))
(defun fn-owner-rx-turn-parser-acquirablep
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (or (and (eq (fn-rxt-phase fn-receiver-turn) :parser-owned)
          (fn-rxt-parser-currentp ticket fn-rx-provider fn-receiver-turn fn-page-read-pool))
     (and (eq (fn-rxt-phase fn-receiver-turn) :filled)
          (null (fn-rxt-output-bundle fn-receiver-turn))
          (fn-rxt-pending-rangep (fn-rxt-job fn-receiver-turn))
          (fn-rxp-currentp (fn-rxp-token fn-rx-provider) fn-rx-provider)
          (fn-rxt-owned-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool))))
; INTERNAL: PREOC and WIRE are derived by the actual STATE wrapper, never a
; native tuple argument. The once-only filled->parser transition precedes parse.
(defun fn-owner-rx-turn-parser-acquire
 (ticket preOC wire fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (cond
  ((and (eq (fn-rxt-phase fn-receiver-turn) :parser-owned)
        (fn-rxt-parser-currentp ticket fn-rx-provider fn-receiver-turn fn-page-read-pool))
   (mv :already-parser-owned fn-receiver-turn fn-page-read-pool))
  ((not (fn-owner-rx-turn-parser-acquirablep ticket fn-rx-provider fn-receiver-turn fn-page-read-pool))
   (mv :receiver-unavailable fn-receiver-turn fn-page-read-pool))
  (t
   (let* ((range (fn-rxt-job fn-receiver-turn))
          (root (list :receiver-parser ticket (fn-rxt-source fn-receiver-turn)
                      range (cadr range) (caddr range) preOC nil wire nil 0))
          (fn-receiver-turn (update-fn-rxt-job root fn-receiver-turn))
          (fn-receiver-turn (update-fn-rxt-phase :parser-owned fn-receiver-turn)))
    (mv :parser-acquired fn-receiver-turn fn-page-read-pool)))))
; ACTUALSTEP comes from the serialized core RC/STATE completion producer.
; This cheap shape/scalar fence does not assert its full decoration-domain.
(defun fn-owner-rx-turn-parser-commit
 (ticket RC wire step fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let* ((job (fn-rxt-job fn-receiver-turn)) (consumed (fn-prl-nth 5 step)))
  (if (not (and (member-eq (fn-rxt-phase fn-receiver-turn) '(:parser-owned :parser-installing))
                (fn-rxt-parser-currentp ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
                (eq (fn-rrd-step-disposition step) :response)
                (natp consumed)
                (<= consumed (- (fn-prl-nth 5 job) (fn-prl-nth 4 job)))
                ; A zero-consumed response is terminal, never a rearmable
                ; episode at the same span. This flag is from ACTUAL STEP.
                (or (posp consumed) (eq (fn-prl-nth 2 step) t)
                    (fn-prl-nth 7 step))))
      (mv :receiver-unavailable nil fn-receiver-turn fn-page-read-pool)
   (let* ((episode (+ 1 (fn-prl-nth 10 job)))
          (response (list :receiver-response ticket episode))
          (root (list :receiver-parser (fn-prl-nth 1 job) (fn-prl-nth 2 job)
                     (fn-prl-nth 3 job) (fn-prl-nth 4 job) (fn-prl-nth 5 job)
                     (fn-prl-nth 6 job) RC wire step episode))
          (fn-receiver-turn (update-fn-rxt-job root fn-receiver-turn))
          (fn-receiver-turn (update-fn-rxt-phase :response-owned fn-receiver-turn)))
    (mv :response-recorded response fn-receiver-turn fn-page-read-pool)))))
; INTERNAL actual :parser-progress producer. Advancing the cursor is not
; detachment: current RC/wire and the whole input actor remain retained.
(defun fn-owner-rx-turn-parser-progress
 (ticket RC wire step fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let ((job (fn-rxt-job fn-receiver-turn)) (consumed (fn-prl-nth 5 step)))
  (if (not (and (member-eq (fn-rxt-phase fn-receiver-turn) '(:parser-owned :parser-installing))
                (fn-rxt-parser-currentp ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
                (eq (fn-rrd-step-disposition step) :parser-progress)
                (natp consumed)
                (<= consumed (- (fn-prl-nth 5 job) (fn-prl-nth 4 job)))))
      (mv :receiver-unavailable fn-receiver-turn fn-page-read-pool)
   (let* ((root (list :receiver-parser (fn-prl-nth 1 job) (fn-prl-nth 2 job)
                     (fn-prl-nth 3 job) (+ (fn-prl-nth 4 job) consumed)
                     (fn-prl-nth 5 job) (fn-prl-nth 6 job) RC wire step
                     (fn-prl-nth 10 job)))
          (fn-receiver-turn (update-fn-rxt-job root fn-receiver-turn)))
    (mv :parser-progress-recorded fn-receiver-turn fn-page-read-pool)))))
; INTERNAL refusal after the actual STATE producer may already have
; installed its result. Retain those exact roots and revoke all consumers.
; A successful fence is not a joined turn, rollback or reclaim observation.
(defun fn-owner-rx-turn-parser-fence
 (ticket RC wire step fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let ((job (fn-rxt-job fn-receiver-turn)))
  (if (not (and (member-eq (fn-rxt-phase fn-receiver-turn)
                            '(:parser-owned :parser-installing :response-owned :parser-recovery))
                (fn-rxt-parser-jobp job)
                (equal (fn-prl-nth 1 job) ticket)
                (equal (fn-prl-nth 2 job) (fn-rxt-source fn-receiver-turn))
                (fn-rxt-owned-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)))
      (mv :receiver-unavailable fn-rx-provider fn-receiver-turn fn-page-read-pool)
   (mv-let (word fn-rx-provider)
    (if (null (fn-rxp-capacity fn-rx-provider))
        (mv :receiver-fenced fn-rx-provider)
      (fn-rxp-fence (fn-rxp-token fn-rx-provider) fn-rx-provider))
    (if (not (eq word :receiver-fenced))
        (mv :receiver-unavailable fn-rx-provider fn-receiver-turn fn-page-read-pool)
     (let* ((root (list :receiver-parser (fn-prl-nth 1 job) (fn-prl-nth 2 job)
                       (fn-prl-nth 3 job) (fn-prl-nth 4 job) (fn-prl-nth 5 job)
                       (fn-prl-nth 6 job) RC wire step (fn-prl-nth 10 job)))
            (fn-receiver-turn (update-fn-rxt-job root fn-receiver-turn))
            (fn-receiver-turn (update-fn-rxt-phase :parser-recovery fn-receiver-turn)))
      (mv :parser-fenced fn-rx-provider fn-receiver-turn fn-page-read-pool)))))))
; Stage the actual evaluator result before the first STATE write. The root
; survives a later escape; capacity revocation blocks all public consumers.
(defun fn-owner-rx-turn-parser-stage
 (ticket RC fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let ((job (fn-rxt-job fn-receiver-turn)))
  (if (not (and (eq (fn-rxt-phase fn-receiver-turn) :parser-owned)
                (fn-rxt-parser-currentp ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)))
      (mv :receiver-unavailable fn-rx-provider fn-receiver-turn fn-page-read-pool)
   (let* ((root (list :receiver-parser (fn-prl-nth 1 job) (fn-prl-nth 2 job)
                     (fn-prl-nth 3 job) (fn-prl-nth 4 job) (fn-prl-nth 5 job)
                     (fn-prl-nth 6 job) RC (fn-prl-nth 8 job) nil
                     (fn-prl-nth 10 job)))
          (fn-receiver-turn (update-fn-rxt-job root fn-receiver-turn))
          (fn-receiver-turn (update-fn-rxt-phase :parser-installing fn-receiver-turn)))
    (mv-let (word fn-rx-provider)
     (fn-rxp-fence (fn-rxp-token fn-rx-provider) fn-rx-provider)
     (mv (if (eq word :receiver-fenced) :parser-staged :receiver-unavailable)
         fn-rx-provider fn-receiver-turn fn-page-read-pool))))))
(defun fn-owner-rx-turn-parser-staged-rc
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (if (and (eq (fn-rxt-phase fn-receiver-turn) :parser-installing)
          (fn-rxt-parser-currentp ticket fn-rx-provider fn-receiver-turn fn-page-read-pool))
     (mv :staged-result (fn-prl-nth 7 (fn-rxt-job fn-receiver-turn)))
   (mv :receiver-unavailable nil)))
; Publish readiness last, only after progress from the retained result.
(defun fn-rxt-parser-progress-publish (end fn-rx-provider)
 (declare (xargs :stobjs fn-rx-provider))
 (stobj-let ((fn-octets-rx (fn-rxp-octets fn-rx-provider))
             (fn-rx-carry (fn-rxp-carry fn-rx-provider)))
            (word fn-rx-carry)
            (if (equal (fn-octets-rx-len fn-octets-rx) end)
                (let ((fn-rx-carry (update-fn-rxc-capacity 4096 fn-rx-carry)))
                 (mv :parser-progress-recorded fn-rx-carry))
              (mv :receiver-unavailable fn-rx-carry))
            (mv word fn-rx-provider)))
(defun fn-owner-rx-turn-parser-finish
 (ticket wire step fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (mv-let (staged RC)
  (fn-owner-rx-turn-parser-staged-rc ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
  (if (not (eq staged :staged-result))
      (mv :receiver-unavailable nil fn-rx-provider fn-receiver-turn fn-page-read-pool)
   (if (eq (fn-rrd-step-disposition step) :parser-progress)
       (mv-let (word fn-receiver-turn fn-page-read-pool)
        (fn-owner-rx-turn-parser-progress ticket RC wire step fn-rx-provider fn-receiver-turn fn-page-read-pool)
        (if (eq word :parser-progress-recorded)
            (let ((fn-receiver-turn (update-fn-rxt-phase :parser-owned fn-receiver-turn)))
             (mv-let (ready fn-rx-provider)
              (fn-rxt-parser-progress-publish (fn-prl-nth 5 (fn-rxt-job fn-receiver-turn)) fn-rx-provider)
              (mv ready nil fn-rx-provider fn-receiver-turn fn-page-read-pool)))
          (mv-let (fenced fn-rx-provider fn-receiver-turn fn-page-read-pool)
           (fn-owner-rx-turn-parser-fence ticket RC wire step fn-rx-provider fn-receiver-turn fn-page-read-pool)
           (mv fenced nil fn-rx-provider fn-receiver-turn fn-page-read-pool))))
     (mv-let (word episode fn-receiver-turn fn-page-read-pool)
      (fn-owner-rx-turn-parser-commit ticket RC wire step fn-rx-provider fn-receiver-turn fn-page-read-pool)
      (if (eq word :response-recorded)
          (mv word episode fn-rx-provider fn-receiver-turn fn-page-read-pool)
        (mv-let (fenced fn-rx-provider fn-receiver-turn fn-page-read-pool)
         (fn-owner-rx-turn-parser-fence ticket RC wire step fn-rx-provider fn-receiver-turn fn-page-read-pool)
         (mv fenced nil fn-rx-provider fn-receiver-turn fn-page-read-pool))))))))
(encapsulate ()
(local (defun fn-rxst-nth-update-induct (i j l)
 (if (or (zp i) (zp j)) (list i j l)
  (fn-rxst-nth-update-induct (1- i) (1- j) (cdr l)))))
(local (defthm fn-rxst-nth-update
 (implies (and (natp i) (natp j))
  (equal (nth i (update-nth j v l))
         (if (equal i j) v (nth i l))))
 :hints (("Goal" :induct (fn-rxst-nth-update-induct i j l)))))
(local (defthm fn-rxst-cadr-nth
 (equal (cadr x) (nth 1 x))
 :hints (("Goal" :use fn-rxc-second-field-by-definition
          :in-theory (disable fn-rxc-second-field-by-definition)))))
(defthm fn-rxt-staged-success-retains-result-and-pool
 (let* ((out (fn-owner-rx-turn-parser-stage ticket RC fn-rx-provider fn-receiver-turn fn-page-read-pool))
        (provider (mv-nth 1 out)) (turn (mv-nth 2 out)))
  (implies (equal (mv-nth 0 out) :parser-staged)
   (and (equal (fn-prl-nth 7 (fn-rxt-job turn)) RC)
        (equal (fn-rxt-phase turn) :parser-installing)
        (null (fn-rxp-capacity provider))
        (equal (fn-rxt-source turn) (fn-rxt-source fn-receiver-turn))
        (equal (fn-rxt-demand turn) (fn-rxt-demand fn-receiver-turn))
        (equal (mv-nth 3 out) fn-page-read-pool))))
 :hints (("Goal" :in-theory (e/d (fn-owner-rx-turn-parser-stage fn-rxp-fence fn-rxc-fence fn-rxp-capacity fn-prl-nth)
                                 (fn-rxt-parser-currentp fn-rxt-owned-claim-p fn-rxc-currentp fn-bca-tokenp nth update-nth fn-rxc-second-field-by-definition))))
 :rule-classes nil)

)

(defun fn-owner-rx-turn-response-currentp
 (response fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let ((job (fn-rxt-job fn-receiver-turn)))
  (and (eq (fn-rxt-phase fn-receiver-turn) :response-owned)
       (fn-rxt-fixed-widthp response 3)
       (eq (car response) :receiver-response)
       (equal (fn-prl-nth 1 response) (fn-rxt-ticket fn-receiver-turn))
       (posp (fn-prl-nth 2 response))
       (equal (fn-prl-nth 2 response) (fn-prl-nth 10 job))
       (fn-rxt-parser-currentp (fn-prl-nth 1 response) fn-rx-provider
                               fn-receiver-turn fn-page-read-pool))))
; Response factory source only: this never authorizes parsing or readiness.
; The episode is the actual core-issued identity, not a lifetime ticket alone.
(defun fn-owner-rx-turn-response-source
 (response fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (if (fn-owner-rx-turn-response-currentp response fn-rx-provider fn-receiver-turn fn-page-read-pool)
     (fn-rxt-source fn-receiver-turn) nil))
; Factory-only borrowed references from the SAME recorded response episode.
; These references cannot authorize another STATE installation or parsing.
(defun fn-owner-rx-turn-response-result
 (response fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (if (not (fn-owner-rx-turn-response-currentp response fn-rx-provider fn-receiver-turn fn-page-read-pool))
     (mv :receiver-unavailable nil nil nil nil)
   (let ((job (fn-rxt-job fn-receiver-turn)))
    (mv :response-result (fn-rxt-source fn-receiver-turn)
        (fn-prl-nth 6 job) (fn-prl-nth 7 job) (fn-prl-nth 9 job)))))
; Readonly ordinary output custody. The actual issuer must construct this
; bundle from the SAME current parser root, admitted storage and issued job.
; This projection proves neither storage admission nor terminal alias return.
(defun fn-owner-rx-turn-output-current
 (response fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let* ((bundle (fn-rxt-output-bundle fn-receiver-turn))
        (parser (fn-prl-nth 1 bundle)))
  (if (and (fn-owner-rx-turn-response-currentp response fn-rx-provider
                                             fn-receiver-turn fn-page-read-pool)
           (fn-rxt-fixed-widthp bundle 4)
           (eq (car bundle) :reader-response-roots)
           (null (fn-prl-nth 2 bundle))
           (consp (fn-prl-nth 3 bundle))
           (fn-rxt-parser-jobp parser)
           (equal (fn-prl-nth 1 parser) (fn-rxt-ticket fn-receiver-turn))
           (equal (fn-prl-nth 2 parser) (fn-rxt-source fn-receiver-turn))
           (equal (fn-prl-nth 10 parser) (fn-prl-nth 2 response)))
      (mv :output-retained bundle)
    (mv :receiver-unavailable nil))))
(encapsulate ()
(local (defun fn-rxst-nth-update-induct (i j l)
 (if (or (zp i) (zp j)) (list i j l)
  (fn-rxst-nth-update-induct (1- i) (1- j) (cdr l)))))
(local (defthm fn-rxst-nth-update
 (implies (and (natp i) (natp j))
  (equal (nth i (update-nth j v l))
         (if (equal i j) v (nth i l))))
 :hints (("Goal" :induct (fn-rxst-nth-update-induct i j l)))))
(defthm fn-rxt-parser-stage-preserves-output-custody
 (equal (fn-rxt-output-bundle
          (mv-nth 2 (fn-owner-rx-turn-parser-stage ticket RC fn-rx-provider
                      fn-receiver-turn fn-page-read-pool)))
        (fn-rxt-output-bundle fn-receiver-turn))
 :hints (("Goal" :in-theory (e/d (fn-owner-rx-turn-parser-stage)
         (fn-rxt-parser-currentp fn-rxp-fence nth update-nth))))
 :rule-classes nil)
)
(defun fn-owner-rx-turn-consumablep
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (and (eq (fn-rxt-phase fn-receiver-turn) :parser-owned)
      (fn-rxt-parser-currentp ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)))
(defun fn-owner-rx-turn-consumer-source
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (if (fn-owner-rx-turn-consumablep ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
     (fn-rxt-source fn-receiver-turn) nil))
(defun fn-owner-rx-turn-consumer-range
 (ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (if (fn-owner-rx-turn-consumablep ticket fn-rx-provider fn-receiver-turn fn-page-read-pool)
     (let ((pending (fn-rxt-job fn-receiver-turn)))
      (mv :receiver-readable (fn-prl-nth 4 pending) (fn-prl-nth 5 pending)))
   (mv :receiver-unavailable 0 0)))
; Internal arithmetic for the forthcoming registered-receipt bridge. The
; consumed scalar must be derived there from the actual committed served-step,
; never supplied by a native return flag. This does not settle or resume a turn.
(defun fn-rxt-consumed-range (start end consumed)
 (declare (xargs :guard t))
 (if (not (and (natp start) (natp end) (natp consumed)
               (<= start end) (<= end 4096) (<= consumed (- end start))))
     (mv :invalid-receiver-consumption start end)
   (let ((next (+ start consumed)))
    (mv (if (equal next end) :receiver-exhausted :receiver-remainder) next end))))
(defthm fn-rxt-consumed-range-keeps-bounded-remainder
 (implies
  (not (equal (mv-nth 0 (fn-rxt-consumed-range start end consumed))
              :invalid-receiver-consumption))
  (and (natp (mv-nth 1 (fn-rxt-consumed-range start end consumed)))
       (<= start (mv-nth 1 (fn-rxt-consumed-range start end consumed)))
       (<= (mv-nth 1 (fn-rxt-consumed-range start end consumed)) end)
       (<= end 4096)
       (equal (mv-nth 2 (fn-rxt-consumed-range start end consumed)) end)))
 :hints (("Goal" :in-theory (enable fn-rxt-consumed-range)))
 :rule-classes nil)
(encapsulate ()
 (local (defthm fn-rxt-begin-nth-update-local
  (implies (and (natp i) (natp j))
   (equal (nth i (update-nth j v x)) (if (equal i j) v (nth i x))))
  :hints (("Goal" :in-theory (enable nth update-nth)))))
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
 :hints (("Goal" :in-theory (e/d
 (fn-owner-rx-turn-begin fn-owner-rx-turn-source fn-rxt-ticket-make fn-rxt-source-make fn-prl-nth)
 (fn-prs-issue fn-owner-page-read-counter-begin fn-owner-page-read-counter-finish
  fn-rxp-currentp fn-rxt-installed-anchor-p fn-rxt-issued-demandp
  fn-owner-page-read-ledger))))
 :rule-classes nil))

(encapsulate ()
 (local (defthm fn-rxt-begin-proof-nth-update-local
  (implies (and (natp i) (natp j))
   (equal (nth i (update-nth j v x)) (if (equal i j) v (nth i x))))
  :hints (("Goal" :in-theory (enable nth update-nth)))))
 (local (defthm fn-rxt-prs-issue-word-local
  (not (equal (car (fn-prs-issue B U R C next limit demand)) :receiver-turn-busy))
  :hints (("Goal" :in-theory (e/d (fn-prs-issue) (fn-prs-fundedp fn-prs-plus fn-prs-vectorp))))))
 (defthm fn-owner-rx-turn-busy-preserves-pool-and-controller
  (implies (equal (mv-nth 0 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider fn-receiver-turn fn-page-read-pool)) :receiver-turn-busy)
   (and (equal (mv-nth 1 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider fn-receiver-turn fn-page-read-pool)) fn-receiver-turn)
        (equal (mv-nth 2 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider fn-receiver-turn fn-page-read-pool)) fn-page-read-pool)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-owner-rx-turn-begin)
   (fn-prs-issue fn-rxp-currentp fn-rxt-installed-anchor-p fn-rxt-issued-demandp
    fn-owner-page-read-counter-begin fn-owner-page-read-counter-finish fn-owner-page-read-ledger fn-prl-nth update-nth nth)))))
 (defthm fn-owner-rx-turn-begin-preserves-installation-receipt
  (equal (fn-rxt-receipt (mv-nth 1 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider fn-receiver-turn fn-page-read-pool)))
         (fn-rxt-receipt fn-receiver-turn))
  :hints (("Goal" :in-theory (e/d (fn-owner-rx-turn-begin)
   (fn-prs-issue fn-rxp-currentp fn-rxt-installed-anchor-p fn-rxt-issued-demandp
    fn-owner-page-read-counter-begin fn-owner-page-read-counter-finish fn-owner-page-read-ledger fn-prl-nth update-nth nth))))))


(encapsulate ()
 (local (defthm fn-rxt-identity-nth-update-local
  (implies (and (natp i) (natp j))
   (equal (nth i (update-nth j v x)) (if (equal i j) v (nth i x))))
  :hints (("Goal" :in-theory (enable nth update-nth)))))
 (local (defthm fn-rxt-identity-prs-next-local
  (implies (eq (car (fn-prs-issue B U R C next limit demand)) :admitted)
   (equal (mv-nth 1 (fn-prs-issue B U R C next limit demand)) (+ 1 next)))
  :hints (("Goal" :in-theory (e/d (fn-prs-issue) (fn-prs-fundedp fn-prs-plus fn-prs-vectorp))))))
 (local (defthm fn-rxt-identity-finish-ledger-local
  (equal (fn-owner-page-read-ledger (mv-nth 1 (fn-owner-page-read-counter-finish receipt fn-page-read-pool)))
         (fn-owner-page-read-ledger fn-page-read-pool))
  :hints (("Goal" :in-theory (e/d
   (fn-owner-page-read-counter-finish fn-owner-page-read-ledger)
   (fn-prb-fixed-widthp fn-prb-counter-receipt-matchesp fn-prb-data-revision nth update-nth))))))
 (local (defthm fn-rxt-identity-begin-next-local
  (implies (eq (car (fn-owner-page-read-counter-begin next nonce kind continuation fn-page-read-pool)) :counter-publishing)
   (equal (fn-prl-nth 2 (fn-owner-page-read-ledger (mv-nth 2 (fn-owner-page-read-counter-begin next nonce kind continuation fn-page-read-pool))))
          (fn-prl-nth 2 next)))
  :hints (("Goal" :in-theory (e/d
   (fn-owner-page-read-counter-begin fn-owner-page-read-ledger fn-prb-data6 fn-prb-keep-current-bindings fn-prl-build fn-prl-nth)
   (fn-prb-data-revision nth update-nth))))))
 (defthm fn-owner-rx-turn-begin-spends-pool-identity-once
  (implies (equal (mv-nth 0 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider fn-receiver-turn fn-page-read-pool)) :admitted)
   (equal (fn-prl-nth 2 (fn-owner-page-read-ledger (mv-nth 2 (fn-owner-rx-turn-begin receiver-token demand fn-rx-provider fn-receiver-turn fn-page-read-pool))))
          (+ 1 (fn-prl-nth 2 (fn-owner-page-read-ledger fn-page-read-pool)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d
   (fn-owner-rx-turn-begin fn-prl-build fn-prl-nth)
   (fn-prs-issue fn-rxp-currentp fn-rxt-installed-anchor-p fn-rxt-issued-demandp
    fn-owner-page-read-counter-begin fn-owner-page-read-counter-finish
    fn-owner-page-read-ledger fn-prb-keep-current-bindings nth update-nth))))))




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
(defthm fn-owner-rx-turn-copy-ack-completion-keeps-custody
 (implies
  (equal (mv-nth 0 (fn-owner-rx-turn-copy-ack ticket start end outcome
                      fn-rx-provider fn-receiver-turn fn-page-read-pool)) :receive-recorded)
  (let ((provider (mv-nth 1 (fn-owner-rx-turn-copy-ack ticket start end outcome
                      fn-rx-provider fn-receiver-turn fn-page-read-pool)))
        (turn (mv-nth 2 (fn-owner-rx-turn-copy-ack ticket start end outcome
                      fn-rx-provider fn-receiver-turn fn-page-read-pool))))
   (and (equal (fn-rxp-capacity provider) 4096)
        (equal (fn-rxt-phase turn) :filled)
        (equal (fn-rxt-ticket turn) (fn-rxt-ticket fn-receiver-turn))
        (equal (fn-rxt-source turn) (fn-rxt-source fn-receiver-turn))
        (equal (fn-rxt-demand turn) (fn-rxt-demand fn-receiver-turn))
        (equal (fn-rxt-job turn) (fn-rxt-job fn-receiver-turn))
        (equal (fn-rxt-receipt turn) (fn-rxt-receipt fn-receiver-turn))
        (equal (mv-nth 3 (fn-owner-rx-turn-copy-ack ticket start end outcome
                      fn-rx-provider fn-receiver-turn fn-page-read-pool)) fn-page-read-pool))))
 :hints (("Goal" :in-theory (enable fn-owner-rx-turn-copy-ack
                                  fn-rxt-copy-publish fn-rxp-capacity)))
 :rule-classes nil)

(defthm fn-owner-rx-turn-response-recording-retains-input
 (let ((a (fn-owner-rx-turn-parser-commit ticket RC wire step
            fn-rx-provider fn-receiver-turn fn-page-read-pool)))
  (implies (equal (mv-nth 0 a) :response-recorded)
   (and (equal (mv-nth 1 a)
               (list :receiver-response ticket
                     (+ 1 (fn-prl-nth 10 (fn-rxt-job fn-receiver-turn)))))
        (equal (fn-rxt-phase (mv-nth 2 a)) :response-owned)
        (equal (fn-rxt-source (mv-nth 2 a)) (fn-rxt-source fn-receiver-turn))
        (equal (fn-rxt-demand (mv-nth 2 a)) (fn-rxt-demand fn-receiver-turn))
        (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 2 a))) RC)
        (equal (fn-prl-nth 8 (fn-rxt-job (mv-nth 2 a))) wire)
        (equal (fn-prl-nth 9 (fn-rxt-job (mv-nth 2 a))) step)
        (equal (mv-nth 3 a) fn-page-read-pool))))
 :hints (("Goal" :in-theory (e/d (fn-owner-rx-turn-parser-commit fn-prl-nth)
  (fn-rxt-parser-currentp fn-rrd-step-disposition))))
 :rule-classes nil)
; Progress is recorded in either parser phase (e3f6720ef: the staged path
; records progress from the retained result while :parser-installing) and
; keeps the phase it found.
(defthm fn-owner-rx-turn-progress-keeps-parser-custody
 (let ((a (fn-owner-rx-turn-parser-progress ticket RC wire step
            fn-rx-provider fn-receiver-turn fn-page-read-pool)))
  (implies (equal (mv-nth 0 a) :parser-progress-recorded)
   (and (equal (fn-rxt-phase (mv-nth 1 a)) (fn-rxt-phase fn-receiver-turn))
        (member-equal (fn-rxt-phase (mv-nth 1 a)) '(:parser-owned :parser-installing))
        (equal (fn-rxt-source (mv-nth 1 a)) (fn-rxt-source fn-receiver-turn))
        (equal (fn-rxt-demand (mv-nth 1 a)) (fn-rxt-demand fn-receiver-turn))
        (equal (fn-prl-nth 7 (fn-rxt-job (mv-nth 1 a))) RC)
        (equal (fn-prl-nth 8 (fn-rxt-job (mv-nth 1 a))) wire)
        (equal (fn-prl-nth 9 (fn-rxt-job (mv-nth 1 a))) step)
        (equal (fn-prl-nth 10 (fn-rxt-job (mv-nth 1 a)))
               (fn-prl-nth 10 (fn-rxt-job fn-receiver-turn)))
        (equal (mv-nth 2 a) fn-page-read-pool))))
 :hints (("Goal" :in-theory (e/d (fn-owner-rx-turn-parser-progress fn-prl-nth)
  (fn-rxt-parser-currentp fn-rrd-step-disposition))))
 :rule-classes nil)

(defthm fn-owner-rx-turn-issued-response-episode-fits-filled-span
 (let ((a (fn-owner-rx-turn-parser-commit ticket RC wire step
            fn-rx-provider fn-receiver-turn fn-page-read-pool)))
  (implies (equal (mv-nth 0 a) :response-recorded)
   (and (posp (fn-prl-nth 2 (mv-nth 1 a)))
        (<= (fn-prl-nth 2 (mv-nth 1 a)) 4097))))
 :hints (("Goal" :in-theory
  (e/d (fn-owner-rx-turn-parser-commit fn-rxt-parser-currentp
        fn-rxt-parser-jobp fn-rxt-pending-rangep fn-rxt-fixed-widthp fn-prl-nth)
       (fn-rxt-owned-claim-p fn-rxp-currentp fn-rrd-step-disposition))))
 :rule-classes nil)

; INTERNAL decision from the exact recorded response. No returned/joined
; flag and no update: this cannot authorize refill or release on its own.
(defun fn-rxt-recorded-response-continuation (job)
 (declare (xargs :guard t))
 (let* ((start (fn-prl-nth 4 job)) (end (fn-prl-nth 5 job))
        (step (fn-prl-nth 9 job)) (consumed (fn-prl-nth 5 step)))
  (cond
   ((not (and (fn-rxt-parser-jobp job)
              (eq (fn-rrd-step-disposition step) :response)
              (natp consumed) (<= consumed (- end start))))
    (mv :invalid-response start end))
   ((or (eq (fn-prl-nth 2 step) t) (fn-prl-nth 7 step))
    (mv :terminal-response (+ start consumed) end))
   ((not (posp consumed)) (mv :invalid-response start end))
   ((equal (+ start consumed) end) (mv :input-exhausted end end))
   (t (mv :same-input-remainder (+ start consumed) end)))))
(defthm fn-rxt-recorded-response-continuation-keeps-carried-range
 (let ((a (fn-rxt-recorded-response-continuation job)))
  (implies (fn-rxt-parser-jobp job)
   (and (natp (mv-nth 1 a)) (natp (mv-nth 2 a))
        (<= (mv-nth 1 a) (mv-nth 2 a))
        (equal (mv-nth 2 a) (fn-prl-nth 5 job))
        (<= (mv-nth 2 a) 4096))))
 :hints (("Goal" :in-theory
  (e/d (fn-rxt-recorded-response-continuation fn-rxt-parser-jobp
        fn-rxt-pending-rangep fn-rxt-fixed-widthp fn-prl-nth)
       (fn-rrd-step-disposition))))
 :rule-classes nil)
