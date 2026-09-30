; Source side of the actual ATS Qgate/finish contract. Observation scaffolding
; is never executed by the served path and its constructors are not charged.
; Source CONS cells are distinct from selected compiler allocation requests.
(in-package "ACL2")
(include-book "allocation-turn-slots")
(include-book "page-read-issue-source-cost")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-atsc-at (n x)
 (declare (xargs :guard (natp n)))
 (if (consp x) (if (zp n) (car x) (fn-atsc-at (- n 1) (cdr x))) nil))
(defun fn-atsc-value (x) (declare (xargs :guard t)) (fn-atsc-at 0 x))
(defun fn-atsc-cells (x) (declare (xargs :guard t)) (nfix (fn-atsc-at 1 x)))
(defun fn-atsc-ops (x) (declare (xargs :guard t)) (fn-atsc-at 2 x))
(defun fn-atsc-sites (x) (declare (xargs :guard t)) (fn-atsc-at 3 x))
(local
 (defthm fn-atsc-at-is-nth
  (implies (natp n) (equal (fn-atsc-at n x) (nth n x)))
  :hints (("Goal" :induct (fn-atsc-at n x)))))
(local
 (defthm fn-atsc-at-is-mv-nth
  (implies (natp n) (equal (fn-atsc-at n x) (mv-nth n x)))
  :hints (("Goal" :induct (fn-atsc-at n x)))))
(local
 (defthm fn-atsc-prsc-at-is-mv-nth
  (implies (natp n) (equal (fn-prsc-at n x) (mv-nth n x)))
  :hints (("Goal" :induct (fn-prsc-at n x)))))
(defun fn-atsc-append (a b)
 (declare (xargs :guard t))
 (if (consp a) (cons (car a) (fn-atsc-append (cdr a) b)) b))
(local
 (defthm fn-atsc-observation-fields
  (and (equal (fn-atsc-value (list value cells ops sites)) value)
       (equal (fn-atsc-cells (list value cells ops sites)) (nfix cells))
       (equal (fn-atsc-ops (list value cells ops sites)) ops)
       (equal (fn-atsc-sites (list value cells ops sites)) sites))))

; Each numeric event names the actual source operator and ordered operands.
; Prefix conditions matter: refused arithmetic never fabricates the later sum.
(defun fn-atsc-add-room (used debit domain)
 (declare (xargs :guard t))
 (if (and (natp used) (natp debit) (natp domain) (<= debit domain))
  (list (<= used (- domain debit)) 0
        (list (list :subtract (list domain debit)))
        '(fn-aed-add-roomp))
  (list nil 0 nil '(fn-aed-add-roomp))))
(defthm fn-atsc-add-room-observes-result
 (equal (fn-atsc-value (fn-atsc-add-room used debit domain))
        (fn-aed-add-roomp used debit domain)))

(defun fn-atsc-ordinary-room (occupied prepaid reserve budget domain)
 (declare (xargs :guard t))
 (if (not (and (natp occupied) (natp prepaid) (natp reserve)
               (natp budget) (natp domain) (<= budget domain)
               (<= reserve budget)))
  (list nil 0 nil '(fn-aed-ordinary-roomp))
  (let ((remaining (- budget reserve)))
   (if (not (<= prepaid remaining))
    (list nil 0 (list (list :subtract (list budget reserve)))
          '(fn-aed-ordinary-roomp))
    (list (<= occupied (- (- budget reserve) prepaid)) 0
          (list (list :subtract (list budget reserve))
                (list :subtract (list budget reserve))
                (list :subtract (list remaining prepaid)))
          '(fn-aed-ordinary-roomp))))))
(defthm fn-atsc-ordinary-room-observes-result
 (equal (fn-atsc-value (fn-atsc-ordinary-room occupied prepaid reserve budget domain))
        (fn-aed-ordinary-roomp occupied prepaid reserve budget domain)))

(defun fn-atsc-prepay (occupied prepaid debit reserve budget domain)
 (declare (xargs :guard t))
 (let ((room (fn-atsc-add-room prepaid debit domain)))
  (if (not (fn-atsc-value room))
   (list (list :unavailable prepaid) 0 (fn-atsc-ops room)
         (cons 'fn-aed-ordinary-prepay (fn-atsc-sites room)))
   (let* ((proposed (+ prepaid debit))
          (ordinary (fn-atsc-ordinary-room occupied proposed reserve budget domain))
          (prefix (fn-atsc-append (fn-atsc-ops room)
                    (cons (list :add (list prepaid debit)) (fn-atsc-ops ordinary))))
          (sites (cons 'fn-aed-ordinary-prepay
                    (fn-atsc-append (fn-atsc-sites room) (fn-atsc-sites ordinary)))))
    (if (fn-atsc-value ordinary)
     (list (list :prepaid (+ prepaid debit)) 0
           (fn-atsc-append prefix (list (list :add (list prepaid debit)))) sites)
     (list (list :unavailable prepaid) 0 prefix sites))))))
(defthm fn-atsc-prepay-observes-complete-result
 (equal (fn-atsc-value (fn-atsc-prepay occupied prepaid debit reserve budget domain))
        (fn-aed-ordinary-prepay occupied prepaid debit reserve budget domain))
 :hints (("Goal" :in-theory (disable fn-atsc-add-room fn-aed-add-roomp
                                   fn-atsc-ordinary-room fn-aed-ordinary-roomp
                                   fn-atsc-value fn-atsc-ops fn-atsc-sites))))

(defun fn-atsc-ceiling (installation)
 (declare (xargs :guard (fn-aec-installationp installation)))
 (let* ((budget (fn-aec-at 3 installation)) (slack (fn-aec-at 5 installation))
        (collector (fn-aec-at 6 installation)) (external (fn-aec-at 7 installation))
        (factor (fn-aec-at 4 installation))
        (first (- budget slack)) (second (- first collector))
        (third (- second external)))
  (list (floor third factor) 0
        (list (list :subtract (list budget slack))
              (list :subtract (list first collector))
              (list :subtract (list second external))
              (list :floor (list third factor)))
        '(fn-aec-ceiling fn-aec-at))))
(defthm fn-atsc-ceiling-observes-result
 (equal (fn-atsc-value (fn-atsc-ceiling installation)) (fn-aec-ceiling installation)))

; The guard-verified caller carries installation validity; it is not an
; allocating served revalidation. Epoch/nonce remain actual ignored inputs.
(defun fn-atsc-gate (installation mode epoch occupied allocated turns nonce)
 (declare (ignore epoch nonce)
  (xargs :guard (fn-aec-statep installation mode epoch occupied allocated turns nonce)))
 (cond
  ((not (eq mode :active))
   (list (list (if (eq mode :recovery) :recovery-required :yield) mode allocated turns)
         0 nil '(fn-aec-enter)))
  (t
   (let ((room (fn-atsc-add-room turns 1 (fn-aec-at 2 installation))))
    (if (not (fn-atsc-value room))
     (list (list :recovery-required :recovery allocated turns) 0
           (fn-atsc-ops room) (cons 'fn-aec-enter (fn-atsc-sites room)))
     (let* ((ceiling (fn-atsc-ceiling installation))
            (prepay (fn-atsc-prepay occupied allocated (fn-aec-at 9 installation)
                       (fn-aec-at 8 installation) (fn-atsc-value ceiling)
                       (fn-aec-at 2 installation)))
            (ops (fn-atsc-append (fn-atsc-ops room)
                    (fn-atsc-append (fn-atsc-ops ceiling) (fn-atsc-ops prepay))))
            (sites (cons 'fn-aec-enter
                    (fn-atsc-append (fn-atsc-sites room)
                     (fn-atsc-append (fn-atsc-sites ceiling) (fn-atsc-sites prepay))))))
      (if (eq (fn-atsc-at 0 (fn-atsc-value prepay)) :prepaid)
       (list (list :prepaid :active (fn-atsc-at 1 (fn-atsc-value prepay)) (+ 1 turns))
             0 (fn-atsc-append ops (list (list :add (list 1 turns)))) sites)
       (list (list :yield :draining allocated turns) 0 ops sites))))))))
(defthm fn-atsc-gate-observes-complete-result
 (equal (fn-atsc-value (fn-atsc-gate installation mode epoch occupied allocated turns nonce))
        (fn-aec-enter installation mode epoch occupied allocated turns nonce nil))
 :hints (("Goal" :in-theory
  (disable fn-atsc-add-room fn-aed-add-roomp fn-atsc-prepay fn-aed-ordinary-prepay
           fn-atsc-ceiling fn-aec-ceiling fn-atsc-value fn-atsc-ops fn-atsc-sites))))

(defun fn-atsc-leave (mode allocated turns)
 (declare (xargs :guard (and (natp allocated) (natp turns))))
 (if (and (member-eq mode '(:active :draining :recovery)) (posp turns))
  (list (list :left mode allocated (- turns 1)) 0
        (list (list :subtract (list turns 1))) '(fn-aec-leave-owned))
  (list (list :recovery-required :recovery allocated turns) 0 nil '(fn-aec-leave-owned))))
(defthm fn-atsc-leave-observes-complete-result
 (equal (fn-atsc-value (fn-atsc-leave mode allocated turns))
        (fn-aec-leave-owned mode allocated turns)))

; Reuse the existing PRS observer, not a new issuer. DOMAIN preflight's source
; subtractions are represented separately from its five-vector validation.
(defun fn-atsc-issuer-domain-ops (budget used charged next domain)
 (declare (xargs :guard t) (ignore next))
 (if (not (and (fn-prs-vectorp budget) (fn-prs-vectorp used) (fn-prs-vectorp charged)
               (natp domain))) nil
  ; Executed domain arithmetic is obtained below by its short-circuit prefix.
  (let* ((r0 (fn-atsc-add-room (fn-prl-nth 0 used) (fn-prl-nth 0 charged) domain))
         (r1 (and (fn-atsc-value r0)
                   (fn-atsc-add-room (fn-prl-nth 1 used) (fn-prl-nth 1 charged) domain)))
         (r2 (and r1 (fn-atsc-value r1)
                   (fn-atsc-add-room (fn-prl-nth 2 used) (fn-prl-nth 2 charged) domain)))
         (r3 (and r2 (fn-atsc-value r2)
                   (fn-atsc-add-room (fn-prl-nth 3 used) (fn-prl-nth 3 charged) domain)))
         (r4 (and r3 (fn-atsc-value r3)
                   (fn-atsc-ordinary-room (fn-prl-nth 4 used) (fn-prl-nth 4 charged)
                                          1 domain domain))))
   (fn-atsc-append (fn-atsc-ops r0)
    (fn-atsc-append (fn-atsc-ops r1)
     (fn-atsc-append (fn-atsc-ops r2)
      (fn-atsc-append (fn-atsc-ops r3) (fn-atsc-ops r4))))))))

(defun fn-atsc-issue (ledger domain)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((budget (fn-prl-nth 0 ledger)) (used (fn-prl-baseline ledger))
        (charged (fn-prl-nth 1 ledger)) (next (fn-prl-nth 2 ledger))
        (domain-ops
         (if (and (fn-prs-vectorp budget) (fn-prs-vectorp used) (fn-prs-vectorp charged)
                  (natp domain) (natp next) (< next domain)
                  (fn-aec-nats-below budget domain))
             (fn-atsc-issuer-domain-ops budget used charged next domain) nil)))
  (if (not (fn-aec-collection-issuer-domainp budget used charged next domain))
   (list (list :invalid-resource-state nil ledger) 0 domain-ops
         '(fn-aec-collection-issue fn-aec-collection-issuer-domainp
           fn-prl-nth fn-prl-baseline fn-prs-vectorp fn-aec-nats-below))
   (let* ((issue (fn-prsc-issue budget used '(0 0 0 0 0) charged next
                                  (fn-prl-nth 4 budget) '(0 0 0 0 1)))
          (result (fn-prsc-value issue))
          (ops (fn-atsc-append domain-ops (fn-prsc-trace issue)))
          (sites '(fn-aec-collection-issue fn-aec-collection-issuer-domainp
                   fn-prl-nth fn-prl-baseline fn-prs-vectorp fn-aec-nats-below
                   fn-prs-issue fn-prs-fundedp fn-prs-plus fn-prs-below)))
    (if (eq (fn-prsc-at 0 result) :admitted)
     (list (list :issued next
                 (fn-prl-build budget (fn-prsc-at 2 result) (fn-prsc-at 1 result)
                               (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)))
           (+ (fn-prsc-cells issue) (if (fn-prl-nth 4 ledger) 5 4)) ops
           (fn-atsc-append sites '(fn-prl-build)))
     (list (list (fn-prsc-at 0 result) nil ledger) (fn-prsc-cells issue) ops sites))))))
(defthm fn-atsc-issue-observes-complete-result
 (equal (fn-atsc-value (fn-atsc-issue ledger domain))
        (fn-aec-collection-issue ledger domain))
 :hints (("Goal" :in-theory
  (e/d (fn-atsc-issue fn-aec-collection-issue)
       (fn-prsc-issue fn-prs-issue fn-prl-build fn-prl-baseline
        fn-aec-collection-issuer-domainp fn-atsc-issuer-domain-ops
        fn-atsc-value fn-atsc-ops fn-atsc-sites fn-prsc-value fn-prsc-trace fn-prsc-cells
        fn-prs-vectorp fn-prsc-at))
  :use ((:instance fn-prsc-issue-observes-complete-actual-result
          (budget (fn-prl-nth 0 ledger)) (used (fn-prl-baseline ledger))
          (rescue '(0 0 0 0 0)) (charged (fn-prl-nth 1 ledger))
          (next (fn-prl-nth 2 ledger)) (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger)))
          (demand '(0 0 0 0 1)))))))

; Compiler closure obligations: fixed-index readers / recognizers / comparisons
; allocate no explicit source cells. This roster names their live inputs; it
; does not assert their selected compiler lowering is already allocation-free.
; Concrete stores and MV returns likewise have distinct native obligations.
(defun fn-atsc-enter (slot role fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool)
                 :guard (fn-aec-pool-statep fn-page-read-pool) :verify-guards nil))
 (cond
  ((not (and (fn-ats-slotp slot fn-allocation-turn-slots)
             (fn-ats-associatedp fn-allocation-turn-slots fn-page-read-pool)
             role (symbolp role) (symbolp (fn-ats-kindsi slot fn-allocation-turn-slots))
             (eq role (fn-ats-kindsi slot fn-allocation-turn-slots))))
   (mv :unsupported-slots 0 fn-allocation-turn-slots fn-page-read-pool 0 nil
       (list (list :dispatch-check slot role))))
  ((not (eql (fn-ats-phasesi slot fn-allocation-turn-slots) 0))
   (mv (if (fn-ats-owned-phasep (fn-ats-phasesi slot fn-allocation-turn-slots))
           :busy :recovery-required) 0 fn-allocation-turn-slots fn-page-read-pool 0 nil
       (list (list :dispatch-check slot role) (list :phase-check slot))))
  (t
   (let* ((gate (fn-atsc-gate (fn-prp-alloc-installation fn-page-read-pool)
                 (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool)
                 (fn-prp-alloc-occupied fn-page-read-pool) (fn-prp-alloc-allocated fn-page-read-pool)
                 (fn-prp-alloc-active-turns fn-page-read-pool) (fn-prp-alloc-gc-nonce fn-page-read-pool)))
          (gr (fn-atsc-value gate))
          (fn-allocation-turn-slots (update-fn-ats-phasesi slot 1 fn-allocation-turn-slots))
          (fn-page-read-pool (update-fn-prp-alloc-mode (fn-atsc-at 1 gr) fn-page-read-pool))
          (fn-page-read-pool (update-fn-prp-alloc-allocated (fn-atsc-at 2 gr) fn-page-read-pool))
          (fn-page-read-pool (update-fn-prp-alloc-active-turns (fn-atsc-at 3 gr) fn-page-read-pool))
          (sites (list (list :dispatch-check slot role) (list :phase-check slot)
                       (list :slot-store slot :entry-intent)
                       (list :scalar-gate (fn-atsc-sites gate))
                       '(:pool-stores :mode :allocated :active-turns))))
    (if (not (eq (fn-atsc-at 0 gr) :prepaid))
     (let ((fn-allocation-turn-slots (update-fn-ats-phasesi slot 0 fn-allocation-turn-slots)))
      (mv (fn-atsc-at 0 gr) 0 fn-allocation-turn-slots fn-page-read-pool 0 (fn-atsc-ops gate)
          (fn-atsc-append sites (list (list :slot-store slot :idle)))))
     (let* ((issue (fn-atsc-issue (fn-owner-page-read-ledger fn-page-read-pool)
                     (fn-aec-at 2 (fn-prp-alloc-installation fn-page-read-pool))))
            (ir (fn-atsc-value issue))
            (ops (fn-atsc-append (fn-atsc-ops gate) (fn-atsc-ops issue)))
            (sites (fn-atsc-append sites (list (list :shared-prs (fn-atsc-sites issue))))))
      (if (not (eq (fn-atsc-at 0 ir) :issued))
       (let* ((leave (fn-atsc-leave (fn-prp-alloc-mode fn-page-read-pool)
                      (fn-prp-alloc-allocated fn-page-read-pool)
                      (fn-prp-alloc-active-turns fn-page-read-pool)))
              (lr (fn-atsc-value leave))
              (fn-page-read-pool (update-fn-prp-alloc-mode (fn-atsc-at 1 lr) fn-page-read-pool))
              (fn-page-read-pool (update-fn-prp-alloc-allocated (fn-atsc-at 2 lr) fn-page-read-pool))
              (fn-page-read-pool (update-fn-prp-alloc-active-turns (fn-atsc-at 3 lr) fn-page-read-pool))
              (fn-allocation-turn-slots (update-fn-ats-phasesi slot 0 fn-allocation-turn-slots)))
        (mv (fn-atsc-at 0 ir) 0 fn-allocation-turn-slots fn-page-read-pool (fn-atsc-cells issue)
            (fn-atsc-append ops (fn-atsc-ops leave))
            (fn-atsc-append sites (list '(:failed-entry-disposition fn-aec-leave-owned)
                 '(:pool-stores :mode :allocated :active-turns) (list :slot-store slot :idle)))))
       (let* ((fn-page-read-pool (fn-owner-page-read-keep-ledger (fn-atsc-at 2 ir) fn-page-read-pool))
              (fn-allocation-turn-slots (update-fn-ats-noncesi slot (fn-atsc-at 1 ir) fn-allocation-turn-slots))
              (fn-allocation-turn-slots (update-fn-ats-phasesi slot 2 fn-allocation-turn-slots)))
        (mv :gate-owned (fn-atsc-at 1 ir) fn-allocation-turn-slots fn-page-read-pool
            (+ 5 (fn-atsc-cells issue)) ops
            (fn-atsc-append sites (list '(:pool-data-rebuild 5)
               (list :slot-store slot :nonce) (list :slot-store slot :gate-owned))))))))))))

(defun fn-atsc-finish (slot nonce fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool)
                 :guard (fn-aec-pool-statep fn-page-read-pool) :verify-guards nil))
 (cond ((not (fn-ats-matchingp slot nonce fn-allocation-turn-slots fn-page-read-pool))
        (mv :stale fn-allocation-turn-slots fn-page-read-pool 0 nil
            (list (list :receipt-check slot nonce))))
       ((not (and (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining))
                  (posp (fn-prp-alloc-active-turns fn-page-read-pool))))
        (mv :recovery-required fn-allocation-turn-slots fn-page-read-pool 0 nil
            (list (list :receipt-check slot nonce) '(:finish-mode-count-check))))
       (t
        (let* ((leave (fn-atsc-leave (fn-prp-alloc-mode fn-page-read-pool)
                        (fn-prp-alloc-allocated fn-page-read-pool)
                        (fn-prp-alloc-active-turns fn-page-read-pool)))
               (lr (fn-atsc-value leave))
               (fn-allocation-turn-slots (update-fn-ats-phasesi slot 5 fn-allocation-turn-slots))
               (fn-page-read-pool (update-fn-prp-alloc-mode (fn-atsc-at 1 lr) fn-page-read-pool))
               (fn-page-read-pool (update-fn-prp-alloc-allocated (fn-atsc-at 2 lr) fn-page-read-pool))
               (fn-page-read-pool (update-fn-prp-alloc-active-turns (fn-atsc-at 3 lr) fn-page-read-pool))
               (fn-allocation-turn-slots (update-fn-ats-phasesi slot 0 fn-allocation-turn-slots)))
         (mv (fn-atsc-at 0 lr) fn-allocation-turn-slots fn-page-read-pool 0 (fn-atsc-ops leave)
             (list (list :receipt-check slot nonce) '(:finish-mode-count-check)
                   (list :slot-store slot :leave-intent) '(:scalar-leave fn-aec-leave-owned)
                   '(:pool-stores :mode :allocated :active-turns) (list :slot-store slot :idle)))))))

; Complete results: status/nonce and both concrete representations, not only
; a status or count projection. Observation fields have no served authority.
(defthm fn-atsc-enter-observes-complete-actual-result
 (equal (list (mv-nth 0 (fn-atsc-enter slot role slots pool))
              (mv-nth 1 (fn-atsc-enter slot role slots pool))
              (mv-nth 2 (fn-atsc-enter slot role slots pool))
              (mv-nth 3 (fn-atsc-enter slot role slots pool)))
        (fn-ats-enter-internal slot role slots pool))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-atsc-enter fn-ats-enter-internal fn-aec-pool-enter-internal
         fn-aec-pool-consumed-turn-internal)
       (fn-ats-slotp fn-ats-associatedp fn-ats-owned-phasep fn-atsc-gate fn-aec-enter
        fn-atsc-issue fn-aec-collection-issue fn-atsc-leave fn-aec-leave-owned
        fn-owner-page-read-keep-ledger fn-aec-statep fn-aec-installationp
        fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-atsc-at)))))
(defthm fn-atsc-finish-observes-complete-actual-result
 (equal (list (mv-nth 0 (fn-atsc-finish slot nonce slots pool))
              (mv-nth 1 (fn-atsc-finish slot nonce slots pool))
              (mv-nth 2 (fn-atsc-finish slot nonce slots pool)))
        (fn-ats-finish-owned slot nonce slots pool))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-atsc-finish fn-ats-finish-owned fn-aec-pool-consumed-turn-internal)
       (fn-ats-matchingp fn-atsc-leave fn-aec-leave-owned fn-aec-statep fn-aec-installationp
        fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-atsc-at)))))

(verify-guards fn-atsc-issue)

(local
 (defthm fn-atsc-actual-gate-allocated-natural
  (implies (fn-aec-statep i m e l a n g)
           (natp (mv-nth 2 (fn-aec-enter i m e l a n g nil))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory
   (disable fn-aec-enter fn-aec-installationp fn-aec-ceiling fn-aec-at)
   :use ((:instance fn-aec-enter-preserves-allocation-state (cleanup nil)))))))
(local
 (defthm fn-atsc-actual-gate-turns-natural
  (implies (fn-aec-statep i m e l a n g)
           (natp (mv-nth 3 (fn-aec-enter i m e l a n g nil))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory
   (disable fn-aec-enter fn-aec-installationp fn-aec-ceiling fn-aec-at)
   :use ((:instance fn-aec-enter-preserves-allocation-state (cleanup nil)))))))
(local
 (defthm fn-atsc-actual-funded-gate
  (implies (and (natp n) (eq (mv-nth 0 (fn-aec-enter i m e l a n g nil)) :prepaid))
   (and (eq (mv-nth 1 (fn-aec-enter i m e l a n g nil)) :active)
        (posp (mv-nth 3 (fn-aec-enter i m e l a n g nil)))))
  :hints (("Goal" :in-theory (disable fn-aed-ordinary-prepay fn-aed-add-roomp
                                    fn-aec-ceiling fn-aec-at)))))
(local
 (defthm fn-atsc-funded-turn-positive
  (implies (and (natp n) (eq (mv-nth 0 (fn-aec-enter i m e l a n g nil)) :prepaid))
           (< 0 (mv-nth 3 (fn-aec-enter i m e l a n g nil))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-aed-ordinary-prepay fn-aed-add-roomp
                                    fn-aec-ceiling fn-aec-at)))))

(local
 (defthm fn-atsc-observed-issue-nonce-natural
  (implies (eq (fn-atsc-at 0 (fn-atsc-value (fn-atsc-issue ledger domain))) :issued)
           (natp (fn-atsc-at 1 (fn-atsc-value (fn-atsc-issue ledger domain)))))
  :hints (("Goal" :in-theory
   (e/d (fn-aec-collection-issue fn-prs-issue)
        (fn-atsc-issue fn-prs-fundedp fn-prs-plus fn-prs-vectorp
         fn-aec-nats-below fn-aed-add-roomp fn-aed-ordinary-roomp
         fn-atsc-value fn-atsc-at))))))
(local
 (defthm fn-atsc-actual-issued-nonce-natural
  (implies (eq (mv-nth 0 (fn-aec-collection-issue ledger domain)) :issued)
           (natp (mv-nth 1 (fn-aec-collection-issue ledger domain))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory
   (e/d (fn-aec-collection-issue fn-prs-issue)
        (fn-prs-fundedp fn-prs-plus fn-prs-vectorp fn-aec-nats-below
         fn-aed-add-roomp fn-aed-ordinary-roomp))))))

(verify-guards fn-atsc-enter
 :hints (("Goal" :in-theory
  (disable fn-atsc-gate fn-aec-enter fn-atsc-issue fn-aec-collection-issue
           fn-atsc-leave fn-atsc-value fn-atsc-at
           fn-aec-statep fn-aec-installationp fn-aec-at
           fn-aec-ceiling fn-owner-page-read-keep-ledger)
  :use ((:instance fn-aec-pool-entry-preserves-allocation-state
          (cleanup nil) (pool fn-page-read-pool))
        (:instance fn-atsc-actual-issued-nonce-natural
          (ledger (fn-owner-page-read-ledger fn-page-read-pool))
          (domain (fn-aec-at 2 (fn-prp-alloc-installation fn-page-read-pool))))))))
(verify-guards fn-atsc-finish
 :hints (("Goal" :in-theory
  (disable fn-atsc-leave fn-atsc-value fn-atsc-at
           fn-aec-statep fn-aec-installationp))))

(local
 (defthm fn-atsc-append-length
  (equal (len (fn-atsc-append a b)) (+ (len a) (len b)))
  :hints (("Goal" :induct (fn-atsc-append a b)))))
(local
 (defthm fn-atsc-funded-add-room-one-operation
  (implies (fn-aed-add-roomp used debit domain)
           (equal (len (fn-atsc-ops (fn-atsc-add-room used debit domain))) 1))))
(local
 (defthm fn-atsc-funded-ordinary-room-three-operations
  (implies (fn-aed-ordinary-roomp occupied prepaid reserve budget domain)
    (equal (len (fn-atsc-ops
                 (fn-atsc-ordinary-room occupied prepaid reserve budget domain))) 3))))
(local
 (defthm fn-atsc-issued-domain-seven-operations
  (implies (fn-aec-collection-issuer-domainp budget used charged next domain)
   (equal (len (fn-atsc-issuer-domain-ops budget used charged next domain)) 7))
  :hints (("Goal" :in-theory
   (e/d (fn-atsc-issuer-domain-ops fn-aec-collection-issuer-domainp)
        (fn-atsc-add-room fn-aed-add-roomp fn-atsc-ordinary-room fn-aed-ordinary-roomp
         fn-atsc-ops fn-atsc-value fn-prs-vectorp fn-aec-nats-below fn-prl-nth))))))

; Literal source census, not an installed tariff: the single PRS observer
; contributes its actual admitted 30 CONS / 31 ADD, the actual ledger rebuild
; contributes its 4/5 source cells, and the complete domain prefix has 7 SUB.
(local
 (defthm fn-atsc-prs-does-not-return-issued
  (not (eq (mv-nth 0 (fn-prs-issue budget used rescue charged next limit demand)) :issued))
  :hints (("Goal" :in-theory (e/d (fn-prs-issue) (fn-prs-fundedp fn-prs-plus fn-prs-vectorp))))))
(defthm fn-atsc-issued-shared-prs-source-census
 (implies (eq (mv-nth 0 (fn-aec-collection-issue ledger domain)) :issued)
  (and (equal (fn-atsc-cells (fn-atsc-issue ledger domain))
              (+ 30 (if (fn-prl-nth 4 ledger) 5 4)))
       (equal (len (fn-atsc-ops (fn-atsc-issue ledger domain))) 38)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-atsc-issue fn-aec-collection-issue)
       (fn-prsc-issue fn-prs-issue fn-prl-build fn-prl-baseline
        fn-atsc-issuer-domain-ops
        fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-prsc-value
        fn-prsc-trace fn-prsc-cells fn-prs-vectorp fn-prsc-at
        fn-atsc-prs-does-not-return-issued))
  :use ((:instance fn-prsc-issue-observes-complete-actual-result
          (budget (fn-prl-nth 0 ledger)) (used (fn-prl-baseline ledger))
          (rescue '(0 0 0 0 0)) (charged (fn-prl-nth 1 ledger))
          (next (fn-prl-nth 2 ledger)) (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger)))
          (demand '(0 0 0 0 1)))
        (:instance fn-atsc-prs-does-not-return-issued
          (budget (fn-prl-nth 0 ledger)) (used (fn-prl-baseline ledger))
          (rescue '(0 0 0 0 0)) (charged (fn-prl-nth 1 ledger))
          (next (fn-prl-nth 2 ledger)) (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger)))
          (demand '(0 0 0 0 1)))
        (:instance fn-prsc-admitted-issue-source-roster
          (budget (fn-prl-nth 0 ledger)) (used (fn-prl-baseline ledger))
          (rescue '(0 0 0 0 0)) (charged (fn-prl-nth 1 ledger))
          (next (fn-prl-nth 2 ledger)) (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger)))
          (demand '(0 0 0 0 1)))))))

(defthm fn-atsc-finish-source-census-by-definition
 (and (equal (mv-nth 3 (fn-atsc-finish slot nonce slots pool)) 0)
      (equal (mv-nth 4 (fn-atsc-finish slot nonce slots pool))
       (if (and (fn-ats-matchingp slot nonce slots pool)
                (member-eq (fn-prp-alloc-mode pool) '(:active :draining))
                (posp (fn-prp-alloc-active-turns pool)))
           (list (list :subtract (list (fn-prp-alloc-active-turns pool) 1))) nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-atsc-finish fn-atsc-leave)
       (fn-ats-matchingp fn-aec-statep fn-aec-installationp)))))

(local
 (defthm fn-atsc-prepaid-six-operations
  (implies (eq (mv-nth 0 (fn-aed-ordinary-prepay occupied prepaid debit reserve budget domain))
                :prepaid)
   (equal (len (fn-atsc-ops
                 (fn-atsc-prepay occupied prepaid debit reserve budget domain))) 6))
  :hints (("Goal" :in-theory
   (e/d (fn-atsc-prepay fn-aed-ordinary-prepay)
        (fn-atsc-add-room fn-aed-add-roomp fn-atsc-ordinary-room fn-aed-ordinary-roomp
         fn-atsc-value fn-atsc-ops fn-atsc-sites))))))
(local
 (defthm fn-atsc-ceiling-four-operations
  (equal (len (fn-atsc-ops (fn-atsc-ceiling installation))) 4)))
(local
 (defthm fn-atsc-prepaid-gate-twelve-operations
  (implies (eq (mv-nth 0 (fn-aec-enter i m e l a n g nil)) :prepaid)
   (equal (len (fn-atsc-ops (fn-atsc-gate i m e l a n g))) 12))
  :hints (("Goal" :in-theory
   (e/d (fn-atsc-gate fn-aec-enter)
        (fn-atsc-add-room fn-aed-add-roomp fn-atsc-prepay fn-aed-ordinary-prepay
         fn-atsc-ceiling fn-aec-ceiling fn-atsc-value fn-atsc-ops fn-atsc-sites))))))
(local
 (defthm fn-atsc-gate-return-words
  (member-eq (mv-nth 0 (fn-aec-enter i m e l a n g nil))
             '(:prepaid :yield :recovery-required))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-aed-ordinary-prepay fn-aed-add-roomp
                                     fn-aec-ceiling fn-aec-at)))))
(local
 (defthm fn-atsc-issue-return-words
  (member-eq (mv-nth 0 (fn-aec-collection-issue ledger domain))
             '(:issued :invalid-resource-state :read-identities-exhausted :read-resources-unavailable))
  :rule-classes nil
  :hints (("Goal" :in-theory
   (e/d (fn-aec-collection-issue fn-prs-issue)
        (fn-aec-collection-issuer-domainp fn-prs-fundedp fn-prs-vectorp fn-prs-plus))))))

; PRF-1164: count the ACTUAL entry's PRS+ledger+pool reconstruction, and all
; material integer operands on its successful source path. The fixed reader,
; recognizer, comparison, concrete-store and result-MV native closure is a
; separate named ingredient; 39/40 cells alone cannot install Qgate.
(defthm fn-atsc-enter-owned-source-census
 (implies (eq (mv-nth 0 (fn-ats-enter-internal slot role slots pool)) :gate-owned)
  (and (equal (mv-nth 4 (fn-atsc-enter slot role slots pool))
              (+ 35 (if (fn-prl-nth 4 (fn-owner-page-read-ledger pool)) 5 4)))
       (equal (len (mv-nth 5 (fn-atsc-enter slot role slots pool))) 50)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-atsc-enter fn-ats-enter-internal fn-aec-pool-enter-internal)
       (fn-ats-slotp fn-ats-associatedp fn-ats-owned-phasep fn-atsc-gate fn-aec-enter
        fn-atsc-issue fn-aec-collection-issue fn-atsc-leave fn-aec-leave-owned
        fn-owner-page-read-keep-ledger fn-aec-statep fn-aec-installationp
        fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-atsc-at))
  :use ((:instance fn-atsc-issued-shared-prs-source-census
          (ledger (fn-owner-page-read-ledger pool))
          (domain (fn-aec-at 2 (fn-prp-alloc-installation pool))))
        (:instance fn-atsc-issue-return-words
          (ledger (fn-owner-page-read-ledger pool))
          (domain (fn-aec-at 2 (fn-prp-alloc-installation pool))))
        (:instance fn-atsc-gate-return-words
          (i (fn-prp-alloc-installation pool)) (m (fn-prp-alloc-mode pool))
          (e (fn-prp-alloc-epoch pool)) (l (fn-prp-alloc-occupied pool))
          (a (fn-prp-alloc-allocated pool)) (n (fn-prp-alloc-active-turns pool))
          (g (fn-prp-alloc-gc-nonce pool)))))))

(local
 (defthm fn-atsc-prsc-fields
  (and (equal (fn-prsc-value (list value cells trace)) value)
       (equal (fn-prsc-cells (list value cells trace)) (nfix cells))
       (equal (fn-prsc-trace (list value cells trace)) trace))))
(local
 (defthm fn-atsc-len-append
  (equal (len (append a b)) (+ (len a) (len b)))
  :hints (("Goal" :induct (append a b)))))
(local
 (defthm fn-atsc-prsc-funded-bounds
  (and (<= (fn-prsc-cells (fn-prsc-funded budget used rescue charged)) 10)
       (<= (len (fn-prsc-trace (fn-prsc-funded budget used rescue charged))) 10))
  :rule-classes nil
  :hints (("Goal" :in-theory
   (e/d (fn-prsc-funded fn-prs-vectorp)
        (fn-prsc-plus fn-prs-plus fn-prsc-cells fn-prsc-trace fn-prsc-value))))))
(local
 (defthm fn-atsc-prsc-issue-bounds
  (let ((o (fn-prsc-issue budget used rescue charged next limit demand)))
   (and (<= (fn-prsc-cells o) 30) (<= (len (fn-prsc-trace o)) 31)
        (implies (not (eq (fn-prsc-at 0 (fn-prsc-value o)) :admitted))
          (and (<= (fn-prsc-cells o) 25) (<= (len (fn-prsc-trace o)) 25)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
   (e/d (fn-prsc-issue fn-prs-fundedp fn-prs-vectorp)
        (fn-prsc-plus fn-prs-plus fn-prsc-funded fn-prsc-cells fn-prsc-trace
         fn-prsc-value fn-prs-below))
   :use ((:instance fn-atsc-prsc-funded-bounds)
         (:instance fn-atsc-prsc-funded-bounds
            (charged (fn-prsc-value (fn-prsc-plus charged demand)))))))))
(local
 (defthm fn-atsc-add-room-operation-bound
  (<= (len (fn-atsc-ops (fn-atsc-add-room used debit domain))) 1)
  :rule-classes :linear))
(local
 (defthm fn-atsc-ordinary-room-operation-bound
  (<= (len (fn-atsc-ops (fn-atsc-ordinary-room occupied prepaid reserve budget domain))) 3)
  :rule-classes :linear))
(local
 (defthm fn-atsc-prepay-operation-bound
  (<= (len (fn-atsc-ops (fn-atsc-prepay occupied prepaid debit reserve budget domain))) 6)
  :rule-classes :linear
  :hints (("Goal" :in-theory
   (e/d (fn-atsc-prepay)
        (fn-atsc-add-room fn-atsc-ordinary-room fn-atsc-value fn-atsc-ops fn-atsc-sites))))))
(local
 (defthm fn-atsc-gate-operation-bound
  (<= (len (fn-atsc-ops (fn-atsc-gate i m e l a n g))) 12)
  :rule-classes :linear
  :hints (("Goal" :in-theory
   (e/d (fn-atsc-gate)
        (fn-atsc-add-room fn-atsc-prepay fn-atsc-ceiling fn-atsc-value fn-atsc-ops fn-atsc-sites))))))
(local
 (defthm fn-atsc-leave-operation-bound
  (<= (len (fn-atsc-ops (fn-atsc-leave m a n))) 1)
  :rule-classes :linear))
(local
 (defthm fn-atsc-domain-operation-bound
  (<= (len (fn-atsc-issuer-domain-ops budget used charged next domain)) 7)
  :rule-classes :linear
  :hints (("Goal" :in-theory
   (e/d (fn-atsc-issuer-domain-ops)
        (fn-atsc-add-room fn-atsc-ordinary-room fn-atsc-ops fn-atsc-value fn-prs-vectorp))))))
(local
 (defthm fn-atsc-issue-source-bounds
  (let ((o (fn-atsc-issue ledger domain)))
   (and (<= (fn-atsc-cells o) 35) (<= (len (fn-atsc-ops o)) 38)
        (implies (not (eq (mv-nth 0 (fn-aec-collection-issue ledger domain)) :issued))
          (and (<= (fn-atsc-cells o) 25) (<= (len (fn-atsc-ops o)) 32)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
   (e/d (fn-atsc-issue fn-aec-collection-issue)
        (fn-prsc-issue fn-prs-issue fn-aec-collection-issuer-domainp fn-atsc-issuer-domain-ops
         fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-prsc-value
         fn-prsc-trace fn-prsc-cells fn-prs-vectorp fn-prsc-at))
   :use ((:instance fn-atsc-prsc-issue-bounds
          (budget (fn-prl-nth 0 ledger)) (used (fn-prl-baseline ledger))
          (rescue '(0 0 0 0 0)) (charged (fn-prl-nth 1 ledger))
          (next (fn-prl-nth 2 ledger)) (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger)))
          (demand '(0 0 0 0 1)))
         (:instance fn-prsc-issue-observes-complete-actual-result
          (budget (fn-prl-nth 0 ledger)) (used (fn-prl-baseline ledger))
          (rescue '(0 0 0 0 0)) (charged (fn-prl-nth 1 ledger))
          (next (fn-prl-nth 2 ledger)) (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger)))
          (demand '(0 0 0 0 1))))))))

; The full all-branch SOURCE bound is consumable by the matched native
; lowering. It includes failed-entry disposition, not just the admitted PRS.
; Native readers/recognizers/stores/MV/frames still need their own exact closure.
(defthm fn-atsc-all-entry-paths-source-census-bound
 (and (<= (mv-nth 4 (fn-atsc-enter slot role slots pool)) 40)
      (<= (len (mv-nth 5 (fn-atsc-enter slot role slots pool))) 50))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-atsc-enter)
       (fn-ats-slotp fn-ats-associatedp fn-ats-owned-phasep fn-atsc-gate fn-aec-enter
        fn-atsc-issue fn-aec-collection-issue fn-atsc-leave fn-aec-leave-owned
        fn-owner-page-read-keep-ledger fn-aec-statep fn-aec-installationp
        fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-atsc-at))
  :use ((:instance fn-atsc-issue-source-bounds
          (ledger (fn-owner-page-read-ledger pool))
          (domain (fn-aec-at 2 (fn-prp-alloc-installation pool))))))))
