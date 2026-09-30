; Actual prepare composition: source evaluator, same-pool ATS gate/body/leave,
; STATE root retirement/publication and the literal ticket constructor.
(in-package "ACL2")
(include-book "connection-operation-start")
(include-book "connection-operation-source-cost")
(include-book "connection-ticket-source-cost")
(local (include-book "arithmetic-5/top" :dir :system))
(local (defthm fn-copsc-at-mv-nth
 (implies (natp n) (equal (fn-atsc-at n x) (mv-nth n x)))
 :hints (("Goal" :induct (fn-atsc-at n x) :in-theory (enable fn-atsc-at)))))
(local (defthm fn-copsc-raw-fields
 (and (equal (fn-atsc-value (list value cells ops calls)) value)
      (equal (fn-atsc-cells (list value cells ops calls)) (nfix cells))
      (equal (fn-atsc-ops (list value cells ops calls)) ops)
      (equal (fn-atsc-sites (list value cells ops calls)) calls))
 :hints (("Goal" :in-theory (enable fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-atsc-at)))))

(defun fn-copsc-body-control (installation mode epoch occupied allocated turns nonce body)
 (declare (ignore epoch nonce) (xargs :guard
  (and (fn-aec-installationp installation) (natp occupied) (natp allocated) (natp turns) (natp body))))
 (cond ((and (eq mode :draining) (posp turns))
        (list (list :yield :draining allocated) 0 nil '(fn-aec-body)))
       ((or (not (eq mode :active)) (zp turns))
        (list (list :recovery-required :recovery allocated) 0 nil '(fn-aec-body)))
       (t (let* ((ceiling (fn-atsc-ceiling installation))
                 (pay (fn-atsc-prepay occupied allocated body (fn-aec-at 8 installation)
                         (fn-atsc-value ceiling) (fn-aec-at 2 installation))))
            (list (if (eq (fn-atsc-at 0 (fn-atsc-value pay)) :prepaid)
                      (list :prepaid :active (fn-atsc-at 1 (fn-atsc-value pay)))
                    (list :yield :draining allocated)) 0
                  (fn-atsc-append (fn-atsc-ops ceiling) (fn-atsc-ops pay))
                  '(fn-aec-body fn-aec-ceiling fn-aed-ordinary-prepay))))))
(defthm fn-copsc-body-control-observes-result
 (equal (fn-atsc-value (fn-copsc-body-control installation mode epoch occupied allocated turns nonce body))
        (fn-aec-body installation mode epoch occupied allocated turns nonce body nil))
 :hints (("Goal" :in-theory
  (disable fn-atsc-ceiling fn-aec-ceiling fn-atsc-prepay fn-aed-ordinary-prepay
           fn-atsc-value fn-atsc-ops fn-atsc-sites))))

(defun fn-copsc-body (slot nonce body fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool)
  :guard (and (fn-aec-pool-statep fn-page-read-pool) (natp body)) :verify-guards nil))
 (cond ((not (fn-ats-matchingp slot nonce fn-allocation-turn-slots fn-page-read-pool))
        (mv :stale fn-allocation-turn-slots fn-page-read-pool (list nil 0 nil '(fn-ats-prepay-body-internal))))
       ((not (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining)))
        (mv :recovery-required fn-allocation-turn-slots fn-page-read-pool (list nil 0 nil '(fn-ats-prepay-body-internal))))
       ((eql (fn-ats-phasesi slot fn-allocation-turn-slots) 3)
        (mv :prepaid fn-allocation-turn-slots fn-page-read-pool (list nil 0 nil '(fn-ats-prepay-body-internal))))
       ((not (eql (fn-ats-phasesi slot fn-allocation-turn-slots) 2))
        (mv :stale fn-allocation-turn-slots fn-page-read-pool (list nil 0 nil '(fn-ats-prepay-body-internal))))
       (t (let ((seen (fn-copsc-body-control (fn-prp-alloc-installation fn-page-read-pool)
                        (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool)
                        (fn-prp-alloc-occupied fn-page-read-pool) (fn-prp-alloc-allocated fn-page-read-pool)
                        (fn-prp-alloc-active-turns fn-page-read-pool) (fn-prp-alloc-gc-nonce fn-page-read-pool) body)))
            (mv-let (word fn-page-read-pool) (fn-aec-pool-body-internal body nil fn-page-read-pool)
             (let ((fn-allocation-turn-slots
                    (if (eq word :prepaid) (update-fn-ats-phasesi slot 3 fn-allocation-turn-slots) fn-allocation-turn-slots)))
              (mv word fn-allocation-turn-slots fn-page-read-pool seen)))))))
(defthm fn-copsc-body-observes-complete-actual-result
 (equal (let ((seen (fn-copsc-body slot nonce body slots pool)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen)))
        (fn-ats-prepay-body-internal slot nonce body slots pool))
 :hints (("Goal" :in-theory (disable fn-aec-pool-body-internal fn-copsc-body-control fn-ats-matchingp)))
 :rule-classes nil)
(local (defthm fn-copsc-carried-installation
 (implies (and (fn-aec-pool-statep pool) (not (eq (fn-prp-alloc-mode pool) :uninstalled)))
          (fn-aec-installationp (fn-prp-alloc-installation pool)))
 :hints (("Goal" :in-theory (e/d (fn-aec-pool-statep fn-aec-statep)
                                   (fn-aec-installationp fn-aec-ceiling fn-aec-at))))))
(local (defthm fn-copsc-carried-installation-list
 (implies (and (fn-aec-pool-statep pool) (not (eq (fn-prp-alloc-mode pool) :uninstalled)))
          (true-listp (fn-prp-alloc-installation pool)))
 :hints (("Goal" :use fn-copsc-carried-installation
  :in-theory (e/d (fn-aec-installationp)
                  (fn-aec-pool-statep fn-aec-statep fn-aec-ceiling fn-aec-at fn-aec-runtime-associationp))))))
(verify-guards fn-copsc-body
 :hints (("Goal" :in-theory (disable fn-aec-pool-body-internal fn-copsc-body-control fn-aec-pool-statep
           fn-prp-alloc-installation fn-aec-installationp))))

(defun fn-copsc-refuse (slot nonce reason fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
  :guard (fn-aec-pool-statep fn-page-read-pool)))
 (mv-let (word fn-allocation-turn-slots fn-page-read-pool cells ops calls)
  (fn-atsc-finish slot nonce fn-allocation-turn-slots fn-page-read-pool)
  (mv nil (if (eq word :left) reason :recovery-required) (if (eq word :left) nil nonce)
      fn-allocation-turn-slots fn-page-read-pool state (list nil cells ops calls))))
(defthm fn-copsc-refuse-observes-complete-actual-result
 (equal (let ((seen (fn-copsc-refuse slot nonce reason slots pool state)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen) (mv-nth 4 seen) (mv-nth 5 seen)))
        (fn-owner-index-connection-refuse-internal slot nonce reason slots pool state))
 :hints (("Goal" :in-theory (disable fn-atsc-finish fn-ats-finish-owned)
          :use fn-atsc-finish-observes-complete-actual-result))
 :rule-classes nil)

(defun fn-copsc-join (a b)
 (declare (xargs :guard t))
 (list nil (+ (fn-atsc-cells a) (fn-atsc-cells b))
       (fn-atsc-append (fn-atsc-ops a) (fn-atsc-ops b))
       (fn-atsc-append (fn-atsc-sites a) (fn-atsc-sites b))))

(defun fn-copsc-prepare
 (kind family address peer slot fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
  :guard (and (boundp-global 'fn-owner state) (fn-aec-pool-statep fn-page-read-pool))
  :verify-guards nil))
 (if (let ((prior (fn-owner-connection-operation-ticket state)))
       (and prior (not (eq (fn-omk-at 1 prior) :finished))))
     (mv nil :recovery-required nil fn-allocation-turn-slots fn-mio$c fn-page-read-pool state (list nil 0 nil (quote (prior-ticket-refusal))))
  (mv-let (entered nonce fn-allocation-turn-slots fn-page-read-pool gatecells gateops gatecalls)
   (fn-atsc-enter slot :connection-start fn-allocation-turn-slots fn-page-read-pool)
   (if (not (eq entered :gate-owned))
       (mv nil entered nonce fn-allocation-turn-slots fn-mio$c fn-page-read-pool state (list nil gatecells gateops gatecalls))
    ; Prior finished roots retire only under this freshly prepaid gate. A raw
    ; completion escape fenced the pool and cannot reach this successful entry.
    (let* ((installation (fn-owner-connection-operation-installation state))
          (state (f-put-global 'fn-owner-connection-operation-ticket nil state))
          (gate (list nil gatecells gateops gatecalls)))
     (let* ((evaluated
       (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
         (observed)
         (fn-copc-evaluate installation kind family address peer (fn-ibp-slot-depth fn-index-backing))
         observed))
       (word (fn-atsc-at 0 (fn-atsc-value evaluated)))
       (demand (fn-atsc-at 1 (fn-atsc-value evaluated)))
       (fuel (fn-atsc-at 2 (fn-atsc-value evaluated)))
       (body (fn-atsc-at 3 (fn-atsc-value evaluated)))
       (quantum (fn-atsc-at 4 (fn-atsc-value evaluated)))
       (prefix (fn-copsc-join gate evaluated)))
      (if (not (eq word :derived))
          (mv-let (erp refused retained fn-allocation-turn-slots fn-page-read-pool state refusal)
           (fn-copsc-refuse slot nonce word
             fn-allocation-turn-slots fn-page-read-pool state)
           (mv erp refused retained fn-allocation-turn-slots fn-mio$c fn-page-read-pool state (fn-copsc-join prefix refusal)))
       (mv-let (paid fn-allocation-turn-slots fn-page-read-pool payment)
        (fn-copsc-body slot nonce (nfix body)
                                     fn-allocation-turn-slots fn-page-read-pool)
        (if (not (eq paid :prepaid))
            (if (eq paid :yield)
                (mv-let (erp refused retained fn-allocation-turn-slots fn-page-read-pool state refusal)
                 (fn-copsc-refuse slot nonce :yield
                   fn-allocation-turn-slots fn-page-read-pool state)
                 (mv erp refused retained fn-allocation-turn-slots fn-mio$c fn-page-read-pool state (fn-copsc-join prefix (fn-copsc-join payment refusal))))
              (mv nil :recovery-required nonce fn-allocation-turn-slots fn-mio$c fn-page-read-pool state (fn-copsc-join prefix payment)))
         (let ((state (f-put-global 'fn-owner-connection-operation-ticket
                       (list :connection-operation-ticket :prepaid kind family address peer
                             (fn-own-next-id (fn-owner-core state)) slot nonce
                             (fn-prp-alloc-epoch fn-page-read-pool)
                             (fn-omk-at 1 installation) installation demand fuel quantum nil)
                       state)))
          (mv nil :prepared nonce fn-allocation-turn-slots fn-mio$c fn-page-read-pool state (fn-copsc-join prefix (fn-copsc-join payment (list nil 16 nil (quote (ticket16 f-put-global))))))))))))))))


(local (defthm fn-copsc-entry-selectors
 (and   (equal (mv-nth 0 (fn-atsc-enter slot role slots pool)) (mv-nth 0 (fn-ats-enter-internal slot role slots pool)))
  (equal (mv-nth 1 (fn-atsc-enter slot role slots pool)) (mv-nth 1 (fn-ats-enter-internal slot role slots pool)))
  (equal (mv-nth 2 (fn-atsc-enter slot role slots pool)) (mv-nth 2 (fn-ats-enter-internal slot role slots pool)))
  (equal (mv-nth 3 (fn-atsc-enter slot role slots pool)) (mv-nth 3 (fn-ats-enter-internal slot role slots pool))))
 :hints (("Goal" :in-theory (disable fn-atsc-enter fn-ats-enter-internal)
          :use fn-atsc-enter-observes-complete-actual-result))))

(local (defthm fn-copsc-body-selectors
 (and   (equal (mv-nth 0 (fn-copsc-body slot nonce body slots pool)) (mv-nth 0 (fn-ats-prepay-body-internal slot nonce body slots pool)))
  (equal (mv-nth 1 (fn-copsc-body slot nonce body slots pool)) (mv-nth 1 (fn-ats-prepay-body-internal slot nonce body slots pool)))
  (equal (mv-nth 2 (fn-copsc-body slot nonce body slots pool)) (mv-nth 2 (fn-ats-prepay-body-internal slot nonce body slots pool))))
 :hints (("Goal" :in-theory (disable fn-copsc-body fn-ats-prepay-body-internal)
          :use fn-copsc-body-observes-complete-actual-result))))

(local (defthm fn-copsc-refuse-selectors
 (and   (equal (mv-nth 0 (fn-copsc-refuse slot nonce reason slots pool state)) (mv-nth 0 (fn-owner-index-connection-refuse-internal slot nonce reason slots pool state)))
  (equal (mv-nth 1 (fn-copsc-refuse slot nonce reason slots pool state)) (mv-nth 1 (fn-owner-index-connection-refuse-internal slot nonce reason slots pool state)))
  (equal (mv-nth 2 (fn-copsc-refuse slot nonce reason slots pool state)) (mv-nth 2 (fn-owner-index-connection-refuse-internal slot nonce reason slots pool state)))
  (equal (mv-nth 3 (fn-copsc-refuse slot nonce reason slots pool state)) (mv-nth 3 (fn-owner-index-connection-refuse-internal slot nonce reason slots pool state)))
  (equal (mv-nth 4 (fn-copsc-refuse slot nonce reason slots pool state)) (mv-nth 4 (fn-owner-index-connection-refuse-internal slot nonce reason slots pool state)))
  (equal (mv-nth 5 (fn-copsc-refuse slot nonce reason slots pool state)) (mv-nth 5 (fn-owner-index-connection-refuse-internal slot nonce reason slots pool state))))
 :hints (("Goal" :in-theory (disable fn-copsc-refuse fn-owner-index-connection-refuse-internal)
          :use fn-copsc-refuse-observes-complete-actual-result))))

(local (defthm fn-copsc-evaluator-result
 (equal (fn-atsc-value (fn-copc-evaluate installation kind family address peer depth))
        (fn-cop-evaluate installation kind family address peer depth))
 :hints (("Goal" :use fn-copc-evaluate-observes-complete-actual-result
  :in-theory (disable fn-copc-evaluate fn-cop-evaluate)))))
(local (defthm fn-copsc-evaluator-width5
 (equal (list (mv-nth 0 (fn-cop-evaluate installation kind family address peer depth))
              (mv-nth 1 (fn-cop-evaluate installation kind family address peer depth))
              (mv-nth 2 (fn-cop-evaluate installation kind family address peer depth))
              (mv-nth 3 (fn-cop-evaluate installation kind family address peer depth))
              (mv-nth 4 (fn-cop-evaluate installation kind family address peer depth)))
        (fn-cop-evaluate installation kind family address peer depth))
 :hints (("Goal" :in-theory (disable fn-cop-input-left fn-cop-body-demand fn-cop-times-roomp)))))
(defthm fn-copsc-prepare-observes-complete-actual-result
 (equal (let ((seen (fn-copsc-prepare kind family address peer slot slots mio pool state)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen)
                (mv-nth 4 seen) (mv-nth 5 seen) (mv-nth 6 seen)))
        (fn-owner-index-connection-prepare kind family address peer slot slots mio pool state))
 :hints (("Goal" :in-theory
  (disable fn-atsc-enter fn-ats-enter-internal fn-copc-evaluate fn-cop-evaluate
           fn-copsc-body fn-ats-prepay-body-internal fn-copsc-refuse
           fn-owner-index-connection-refuse-internal fn-omk-at fn-omk-widthp
           fn-owner-connection-operation-ticket fn-owner-connection-operation-installation
           fn-owner-core fn-copsc-evaluator-width5 fn-atsc-value fn-atsc-ops fn-atsc-cells
           fn-atsc-sites fn-copsc-join fn-mio$c-provider fn-ibp-slot-depth)))
 :rule-classes nil)

(local
 (defthm fn-copsc-actual-pool-body-state
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
 (defthm fn-copsc-actual-ats-body-state
  (implies (fn-aec-pool-statep fn-page-read-pool)
   (fn-aec-pool-statep (mv-nth 2 (fn-ats-prepay-body-internal slot nonce body fn-allocation-turn-slots fn-page-read-pool))))
  :hints (("Goal" :in-theory (disable fn-aec-pool-statep fn-aec-pool-body-internal)))))


(verify-guards fn-copsc-prepare
 :hints (("Goal" :in-theory
  (disable fn-atsc-enter fn-ats-enter-internal fn-copsc-body fn-ats-prepay-body-internal
           fn-copsc-refuse fn-owner-index-connection-refuse-internal fn-cop-evaluate
           fn-copc-evaluate fn-aec-pool-statep fn-atsc-value fn-atsc-ops fn-atsc-cells fn-atsc-sites)
  :use ((:instance fn-atsh-entry-preserves-carried-pool-state (role :connection-start))))))
