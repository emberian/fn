; Complete changed-state views for the actual PREPARE/ticket subjects.
; These are source fixtures with a synthetic installation, never authority.
(in-package "ACL2")
(include-book "connection-operation-start-tests")
(include-book "../../books/connection-reserve-source-cost")
(local (include-book "arithmetic-5/top" :dir :system))
(defun copsct-view (fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool) :verify-guards nil))
 (list
  (list (fn-ats-association fn-allocation-turn-slots) (fn-ats-count fn-allocation-turn-slots)
        (list (fn-ats-kindsi 0 fn-allocation-turn-slots))
        (list (fn-ats-noncesi 0 fn-allocation-turn-slots))
        (list (fn-ats-phasesi 0 fn-allocation-turn-slots)))
  (list (fn-prp-data fn-page-read-pool) (fn-prp-mode fn-page-read-pool)
        (fn-prp-incoming-slot fn-page-read-pool) (fn-prp-alloc-installation fn-page-read-pool)
        (fn-prp-alloc-mode fn-page-read-pool) (fn-prp-alloc-epoch fn-page-read-pool)
        (fn-prp-alloc-occupied fn-page-read-pool) (fn-prp-alloc-allocated fn-page-read-pool)
        (fn-prp-alloc-active-turns fn-page-read-pool) (fn-prp-alloc-gc-nonce fn-page-read-pool))))
(defun copsct-prefix (n x)
 (declare (xargs :guard (natp n)))
 (if (zp n) nil (cons (if (consp x) (car x) nil)
                     (copsct-prefix (- n 1) (if (consp x) (cdr x) nil)))))
(local (defthm copsct-prefix-reconstruct
 (implies (and (true-listp x) (natp n) (equal (len x) n))
  (equal (copsct-prefix n x) x))
 :hints (("Goal" :induct (copsct-prefix n x)))))
(local (defthm copsct-list1
 (implies (and (true-listp x) (equal (len x) 1)) (equal (list (nth 0 x)) x))
 :hints (("Goal" :use ((:instance copsct-prefix-reconstruct (n 1)))))))
(local (defthm copsct-consp-positive
 (implies (consp x) (< 0 (len x)))
 :rule-classes :linear :hints (("Goal" :expand ((len x))))))
(local (defthm copsct-list5
 (implies (and (true-listp x) (equal (len x) 5))
  (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)) x))
 :hints (("Goal" :cases ((and (consp x) (consp (cdr x)) (consp (cdr (cdr x))) (consp (cdr (cdr (cdr x)))) (consp (cdr (cdr (cdr (cdr x))))) (not (consp (cdr (cdr (cdr (cdr (cdr x)))))))))))))
(local
 (defthm copsct-pool-view
  (implies (and (true-listp x) (equal (len x) 10))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)
                        (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x) (nth 9 x)) x))
  :hints (("Goal" :cases ((and (consp x) (consp (cdr x)) (consp (cdr (cdr x))) (consp (cdr (cdr (cdr x)))) (consp (cdr (cdr (cdr (cdr x))))) (consp (cdr (cdr (cdr (cdr (cdr x)))))) (consp (cdr (cdr (cdr (cdr (cdr (cdr x))))))) (consp (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))) (consp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))) (consp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))) (not (consp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))))))))))
(defthm copsct-one-slot-view-is-complete-state
 (implies (and (true-listp slots) (equal (len slots) 5)
               (true-listp pool) (equal (len pool) 10)
               (true-listp (nth 2 slots)) (equal (len (nth 2 slots)) 1)
               (true-listp (nth 3 slots)) (equal (len (nth 3 slots)) 1)
               (true-listp (nth 4 slots)) (equal (len (nth 4 slots)) 1))
  (equal (copsct-view slots pool) (list slots pool)))
 :hints (("Goal" :in-theory (disable copsct-list5 copsct-list1 copsct-pool-view)
 :use ((:instance copsct-list5 (x slots))
       (:instance copsct-list1 (x (nth 2 slots)))
       (:instance copsct-list1 (x (nth 3 slots)))
       (:instance copsct-list1 (x (nth 4 slots)))
       (:instance copsct-pool-view (x pool))))))
; PREPARE never mutates the MIO argument. These frame helpers plus the full
; ticket view and universal other-global frame account for the complete STATE result.
(defthm copsct-prepare-mio-frame-by-definition
 (equal (mv-nth 4 (fn-copsc-prepare kind family address peer slot slots mio pool st)) mio)
 :hints (("Goal" :in-theory (disable fn-atsc-enter fn-ats-enter-internal fn-copc-evaluate fn-cop-evaluate
                     fn-copsc-body fn-ats-prepay-body-internal fn-copsc-refuse
                     fn-owner-index-connection-refuse-internal fn-mio$c-provider fn-ibp-slot-depth
                     fn-omk-at fn-omk-widthp
                     fn-owner-core fn-owner-connection-operation-ticket fn-atsc-value
                     fn-atsc-at fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-copsc-join)))
 :rule-classes nil)
(local (defthm copsct-state-identity
 (implies (and (true-listp st) (<= 3 (len st)))
  (equal (update-nth 2 (nth 2 st) st) st))
 :hints (("Goal" :cases ((consp st) (consp (cdr st)) (consp (cddr st)))
           :in-theory (enable update-nth nth)
           :expand ((update-nth 2 (nth 2 st) st)
                    (update-nth 1 (nth 1 (cdr st)) (cdr st))
                    (update-nth 0 (nth 0 (cddr st)) (cddr st)))))))
(local (defthm copsct-update-twice
 (equal (update-nth 2 a (update-nth 2 b st)) (update-nth 2 a st))
 :hints (("Goal" :in-theory (enable update-nth)
  :expand ((update-nth 2 a (update-nth 2 b st)) (update-nth 2 b st) (update-nth 2 a st)
           (update-nth 1 a (update-nth 1 b (cdr st))) (update-nth 1 b (cdr st))
           (update-nth 1 a (cdr st)) (update-nth 0 a (update-nth 0 b (cddr st)))
           (update-nth 0 b (cddr st)) (update-nth 0 a (cddr st))))))
)
(local (defthm copsct-put-frame
 (implies (equal (update-nth 2 (nth 2 st) original) st)
  (equal (update-nth 2 (nth 2 (f-put-global key value st)) original)
         (f-put-global key value st)))
 :hints (("Goal" :in-theory (enable f-put-global)))))
(local (defthm copsct-refuse-state
 (equal (mv-nth 5 (fn-copsc-refuse slot nonce reason slots pool st)) st)
 :hints (("Goal" :in-theory (disable fn-atsc-finish fn-ats-finish-owned)))))
(defthm copsct-prepare-state-frame-by-definition
 (implies (and (true-listp st) (<= 3 (len st)))
  (let ((out (mv-nth 6 (fn-copsc-prepare kind family address peer slot slots mio pool st))))
   (equal out (update-nth 2 (nth 2 out) st))))
 :hints (("Goal" :in-theory (disable fn-atsc-enter fn-ats-enter-internal fn-copc-evaluate fn-cop-evaluate
                   fn-copsc-body fn-ats-prepay-body-internal fn-atsc-finish fn-ats-finish-owned
                   fn-copsc-refuse fn-owner-index-connection-refuse-internal f-put-global
                   fn-owner-connection-operation-installation fn-owner-ocfg
                   fn-mio$c-provider fn-ibp-slot-depth fn-omk-at fn-omk-widthp
                   fn-owner-core fn-owner-connection-operation-ticket fn-atsc-value
                   fn-atsc-at fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-copsc-join)))
 :rule-classes nil)
(local (defthm copsct-put-other-global
 (implies (not (equal key 'fn-owner-connection-operation-ticket))
  (equal (f-get-global key (f-put-global 'fn-owner-connection-operation-ticket value st))
         (f-get-global key st)))
 :hints (("Goal" :in-theory (enable f-put-global f-get-global)))))
(defthm copsct-prepare-other-global-frame-by-definition
 (implies (not (equal key 'fn-owner-connection-operation-ticket))
  (equal (f-get-global key (mv-nth 6 (fn-copsc-prepare kind family address peer slot slots mio pool st)))
         (f-get-global key st)))
 :hints (("Goal" :in-theory (disable fn-atsc-enter fn-ats-enter-internal fn-copc-evaluate fn-cop-evaluate
                   fn-copsc-body fn-ats-prepay-body-internal fn-atsc-finish fn-ats-finish-owned
                   fn-copsc-refuse fn-owner-index-connection-refuse-internal f-put-global f-get-global
                   fn-owner-connection-operation-installation fn-owner-ocfg
                   fn-mio$c-provider fn-ibp-slot-depth fn-omk-at fn-omk-widthp
                   fn-owner-core fn-owner-connection-operation-ticket fn-atsc-value
                   fn-atsc-at fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-copsc-join)))
 :rule-classes nil)
(defthm copsct-finish-state-frame-by-definition
 (implies (and (true-listp st) (<= 3 (len st)))
  (let ((out (mv-nth 4 (fn-coptc-finish slot nonce slots pool st))))
   (equal out (update-nth 2 (nth 2 out) st))))
 :hints (("Goal" :in-theory (disable fn-atsc-finish fn-ats-finish-owned
   fn-owner-connection-operation-ticket fn-omk-at fn-omk-widthp
   f-put-global update-nth))) :rule-classes nil)
(defthm copsct-finish-other-global-frame-by-definition
 (implies (not (equal key 'fn-owner-connection-operation-ticket))
  (equal (f-get-global key (mv-nth 4 (fn-coptc-finish slot nonce slots pool st)))
         (f-get-global key st)))
 :hints (("Goal" :in-theory (disable fn-atsc-finish fn-ats-finish-owned
   fn-owner-connection-operation-ticket fn-omk-at fn-omk-widthp
   f-put-global f-get-global update-nth))) :rule-classes nil)
(defthm copsct-fault-state-frame-by-definition
 (equal (mv-nth 4 (fn-coptc-fault slots pool st)) st)
 :hints (("Goal" :in-theory (disable fn-ats-uncertain-internal))) :rule-classes nil)
(defun copsct-sample (observedp case fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-mio$c fn-page-read-pool state) :verify-guards nil))
 (mv-let (setup fn-allocation-turn-slots fn-mio$c fn-page-read-pool)
  (fn-cost-setup t fn-allocation-turn-slots fn-mio$c fn-page-read-pool)
  (let* ((state (f-put-global 'fn-owner '((nil nil nil 42)) state))
         (state (f-put-global 'fn-owner-connection-operation-ticket nil state))
         (state (f-put-global 'fn-owner-connection-operation-installation
                  (and (not (eq case :unavailable))
                   (list :connection-operation-installation 9
                    '(:allocation-epoch-association :runtime :profile :pool 10 1000)
                    :synthetic-source 1000 '(40 0 0 0 1)
                    (if (eq case :body-yield) 700 40) 0 0 20)) state))
         (antecedent (and (eq setup :constructed) (boundp-global 'fn-owner state)
                          (fn-aec-pool-statep fn-page-read-pool)
                          (fn-allocation-turn-slotsp fn-allocation-turn-slots)
                          (fn-page-read-poolp fn-page-read-pool)
                          (equal (fn-ats-kinds-length fn-allocation-turn-slots) 1)
                          (equal (fn-ats-nonces-length fn-allocation-turn-slots) 1)
                          (equal (fn-ats-phases-length fn-allocation-turn-slots) 1))))
   (mv-let (erp word nonce fn-allocation-turn-slots fn-mio$c fn-page-read-pool state seen)
    (if observedp
        (fn-copsc-prepare (if (eq case :bad-input) :invalid :reader) nil nil nil 0
                         fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
      (mv-let (erp word nonce fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
       (fn-owner-index-connection-prepare (if (eq case :bad-input) :invalid :reader) nil nil nil 0
                         fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
       (mv erp word nonce fn-allocation-turn-slots fn-mio$c fn-page-read-pool state nil)))
    (if (member-eq case '(:finish :fault :double-fault :duplicate-finish))
        (mv-let (erp word fn-allocation-turn-slots fn-page-read-pool state)
         (if (member-eq case '(:double-fault :duplicate-finish))
             (if (eq case :double-fault)
                 (fn-owner-index-connection-fault fn-allocation-turn-slots fn-page-read-pool state)
               (fn-owner-index-connection-finish 0 nonce fn-allocation-turn-slots fn-page-read-pool state))
           (mv erp word fn-allocation-turn-slots fn-page-read-pool state))
         (declare (ignore erp word))
         (mv-let (erp word fn-allocation-turn-slots fn-page-read-pool state cells ops sites)
          (if (member-eq case '(:fault :double-fault))
              (if observedp (fn-coptc-fault fn-allocation-turn-slots fn-page-read-pool state)
                (mv-let (erp word fn-allocation-turn-slots fn-page-read-pool state)
                 (fn-owner-index-connection-fault fn-allocation-turn-slots fn-page-read-pool state)
                 (mv erp word fn-allocation-turn-slots fn-page-read-pool state 0 nil nil)))
            (if observedp (fn-coptc-finish 0 nonce fn-allocation-turn-slots fn-page-read-pool state)
              (mv-let (erp word fn-allocation-turn-slots fn-page-read-pool state)
               (fn-owner-index-connection-finish 0 nonce fn-allocation-turn-slots fn-page-read-pool state)
               (mv erp word fn-allocation-turn-slots fn-page-read-pool state 0 nil nil))))
          (declare (ignore sites))
          (mv (list antecedent erp word nonce (copsct-view fn-allocation-turn-slots fn-page-read-pool)
                    (fn-owner-connection-operation-ticket state)) cells (len ops)
              fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)))
      (mv (list antecedent erp word nonce (copsct-view fn-allocation-turn-slots fn-page-read-pool)
                (fn-owner-connection-operation-ticket state)) (fn-atsc-cells seen) (len (fn-atsc-ops seen))
          fn-allocation-turn-slots fn-mio$c fn-page-read-pool state))))))
(defun copsct-local (observedp case state)
 (declare (xargs :stobjs state :verify-guards nil))
 (with-local-stobj fn-page-read-pool
  (mv-let (value cells operations fn-page-read-pool state)
   (with-local-stobj fn-allocation-turn-slots
    (mv-let (value cells operations fn-allocation-turn-slots fn-page-read-pool state)
     (with-local-stobj fn-mio$c
      (mv-let (value cells operations fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
       (copsct-sample observedp case fn-allocation-turn-slots fn-mio$c fn-page-read-pool state)
       (mv value cells operations fn-allocation-turn-slots fn-page-read-pool state)))
     (mv value cells operations fn-page-read-pool state)))
   (mv value cells operations state))))
(defun copsct-pair (case word nonce allocated active phase cells operations state)
 (declare (xargs :stobjs state :verify-guards nil))
 (mv-let (actual ignored1 ignored2 state) (copsct-local nil case state)
  (declare (ignore ignored1 ignored2))
  (mv-let (seen actual-cells actual-operations state) (copsct-local t case state)
   (let* ((view (nth 4 seen)) (slots (nth 0 view)) (pool (nth 1 view)))
    (mv (and (equal actual seen) (car seen) (not (nth 1 seen)) (equal (nth 2 seen) word)
             (equal (nth 3 seen) nonce) (equal (nth 7 pool) allocated) (equal (nth 8 pool) active)
             (equal (nth 0 (nth 4 slots)) phase)
             (equal actual-cells cells) (equal actual-operations operations)) state)))))
(make-event (mv-let (ok state) (copsct-pair :prepared :prepared 0 70 1 3 56 73 state)
 (if ok (value '(value-triple :source-prepare-complete)) (er soft 'source "prepare mismatch"))))
(make-event (mv-let (ok state) (copsct-pair :unavailable :unsupported-runtime nil 30 0 0 40 52 state)
 (if ok (value '(value-triple :source-unavailable-complete)) (er soft 'source "unavailable mismatch"))))
(make-event (mv-let (ok state) (copsct-pair :bad-input :refused nil 30 0 0 40 52 state)
 (if ok (value '(value-triple :source-refused-complete)) (er soft 'source "refused mismatch"))))
(make-event (mv-let (ok state) (copsct-pair :body-yield :yield nil 30 0 0 40 71 state)
 (if ok (value '(value-triple :source-yield-complete)) (er soft 'source "yield mismatch"))))
(make-event (mv-let (ok state) (copsct-pair :finish :left 0 70 0 0 4 3 state)
 (if ok (value '(value-triple :source-finish-complete)) (er soft 'source "finish mismatch"))))
(make-event (mv-let (ok state) (copsct-pair :duplicate-finish :recovery-required 0 70 0 0 0 0 state)
 (if ok (value '(value-triple :source-duplicate-finish-complete)) (er soft 'source "duplicate mismatch"))))
(make-event (mv-let (ok state) (copsct-pair :fault :recovery-required 0 70 1 3 0 0 state)
 (if ok (value '(value-triple :source-fault-complete)) (er soft 'source "fault mismatch"))))
(make-event (mv-let (ok state) (copsct-pair :double-fault :recovery-required 0 70 1 3 0 0 state)
 (if ok (value '(value-triple :source-double-fault-complete)) (er soft 'source "double fault mismatch"))))
