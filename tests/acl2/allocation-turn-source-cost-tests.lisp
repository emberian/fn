(in-package "ACL2")
(include-book "../../books/allocation-turn-source-cost")
(include-book "allocation-turn-slots-tests")
(local (include-book "arithmetic-5/top" :dir :system))

; The real-stobj witness reads every field through its guarded accessors.
; This bounded reconstruction theorem makes its complete view a literal
; full-state witness, rather than silently replacing the keystone conclusion
; with a projection. These helpers never run on the served path.
(defun atsct-prefix (n x)
 (declare (xargs :guard (natp n)))
 (if (zp n) nil
  (cons (if (consp x) (car x) nil)
        (atsct-prefix (- n 1) (if (consp x) (cdr x) nil)))))
(local
 (defthm atsct-prefix-restores-list
  (implies (and (true-listp x) (natp n) (equal (len x) n))
           (equal (atsct-prefix n x) x))
  :hints (("Goal" :induct (atsct-prefix n x)))))
(local
 (defthm atsct-consp-length-positive
  (implies (consp x) (< 0 (len x)))
  :rule-classes :linear
  :hints (("Goal" :expand ((len x))))))
(local
 (defthm atsct-list2-reconstruction
  (implies (and (true-listp x) (equal (len x) 2))
           (equal (list (nth 0 x) (nth 1 x)) x))
  :hints (("Goal" :use ((:instance atsct-prefix-restores-list (n 2)))))))
(local
 (defthm atsct-list5-reconstruction
  (implies (and (true-listp x) (equal (len x) 5))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)) x))
  :hints (("Goal" :use ((:instance atsct-prefix-restores-list (n 5)))))))
(local
 (defthm atsct-list10-reconstruction
  (implies (and (true-listp x) (equal (len x) 10))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)
                        (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x) (nth 9 x)) x))
  :hints (("Goal" :cases ((and (consp x) (consp (cdr x)) (consp (cdr (cdr x))) (consp (cdr (cdr (cdr x)))) (consp (cdr (cdr (cdr (cdr x))))) (consp (cdr (cdr (cdr (cdr (cdr x)))))) (consp (cdr (cdr (cdr (cdr (cdr (cdr x))))))) (consp (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))) (consp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))) (consp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))) (not (consp (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))))))))))
(defun atsct-decode-view (view)
 (declare (xargs :guard t))
 (list (list (fn-prsc-at 0 view) (fn-prsc-at 1 view)
             (list (fn-prsc-at 2 view) (fn-prsc-at 3 view))
             (list (fn-prsc-at 4 view) (fn-prsc-at 5 view))
             (list (fn-prsc-at 6 view) (fn-prsc-at 7 view)))
       (list (fn-prsc-at 8 view) (fn-prsc-at 9 view) (fn-prsc-at 10 view)
             (fn-prsc-at 11 view) (fn-prsc-at 12 view) (fn-prsc-at 13 view)
             (fn-prsc-at 14 view) (fn-prsc-at 15 view) (fn-prsc-at 16 view) (fn-prsc-at 17 view))))
(defthm atsct-two-slot-view-is-complete-state
 (implies
  (and (true-listp slots) (equal (len slots) 5)
       (true-listp pool) (equal (len pool) 10)
       (true-listp (nth 2 slots)) (equal (len (nth 2 slots)) 2)
       (true-listp (nth 3 slots)) (equal (len (nth 3 slots)) 2)
       (true-listp (nth 4 slots)) (equal (len (nth 4 slots)) 2))
  (equal (atsct-decode-view (atst-view slots pool)) (list slots pool)))
 :hints (("Goal" :in-theory
  (e/d (atst-view atsct-decode-view)
       (atsct-list2-reconstruction atsct-list5-reconstruction atsct-list10-reconstruction))
  :use ((:instance atsct-list5-reconstruction (x slots))
        (:instance atsct-list10-reconstruction (x pool))
        (:instance atsct-list2-reconstruction (x (nth 2 slots)))
        (:instance atsct-list2-reconstruction (x (nth 3 slots)))
        (:instance atsct-list2-reconstruction (x (nth 4 slots)))))))

(defun atsct-init (case finishp fn-allocation-turn-slots fn-page-read-pool)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool) :verify-guards nil))
 (let* ((fn-allocation-turn-slots (update-fn-ats-association nil fn-allocation-turn-slots))
        (fn-allocation-turn-slots (update-fn-ats-count 0 fn-allocation-turn-slots))
        (fn-page-read-pool (update-fn-prp-alloc-active-turns 0 fn-page-read-pool))
        (ledger
         (cond ((eq case :legacy) (list (car *ats-ledger*) (cadr *ats-ledger*) 7 '(:lifetime-holder)))
               ((eq case :identities) '((1000 1000 1000 1000 7) (0 0 0 0 7) 7 (:lifetime-holder) (0 0 0 0 0)))
               ((eq case :resources) '((1000 1000 1000 1000 8) (0 0 0 0 7) 7 (:lifetime-holder) (0 0 0 0 1)))
               ((eq case :domain-next) '((1000 1000 1000 1000 1000) (0 0 0 0 1000) 1000 (:lifetime-holder) (0 0 0 0 0)))
               ((eq case :invalid-funded) '((1000 1000 1000 1000 6) (0 0 0 0 7) 7 (:lifetime-holder) (0 0 0 0 0)))
               (t *ats-ledger*))))
  (mv-let (constructed fn-allocation-turn-slots fn-page-read-pool)
   (atst-init ledger (if (eq case :gate-room) 250 20) fn-allocation-turn-slots fn-page-read-pool)
   (declare (ignore constructed))
   (mv-let (entered nonce fn-allocation-turn-slots fn-page-read-pool)
    (if (or (eq case :busy) (and finishp (not (member-eq case '(:idle :wrong-slot)))))
        (fn-ats-enter-internal 0 :connection-start fn-allocation-turn-slots fn-page-read-pool)
      (mv :unused 7 fn-allocation-turn-slots fn-page-read-pool))
    (declare (ignore entered))
    (mv-let (body fn-allocation-turn-slots fn-page-read-pool)
     (if (eq case :body)
         (fn-ats-prepay-body-internal 0 nonce 40 fn-allocation-turn-slots fn-page-read-pool)
       (mv :unused fn-allocation-turn-slots fn-page-read-pool))
     (declare (ignore body))
     (mv-let (finished fn-allocation-turn-slots fn-page-read-pool)
      (if (member-eq case '(:duplicate :reuse))
          (fn-ats-finish-owned 0 nonce fn-allocation-turn-slots fn-page-read-pool)
        (mv :unused fn-allocation-turn-slots fn-page-read-pool))
      (declare (ignore finished))
      (mv-let (reentered next fn-allocation-turn-slots fn-page-read-pool)
       (if (eq case :reuse)
           (fn-ats-enter-internal 0 :connection-start fn-allocation-turn-slots fn-page-read-pool)
         (mv :unused nonce fn-allocation-turn-slots fn-page-read-pool))
       (declare (ignore reentered next))
       (let* ((fn-allocation-turn-slots
               (cond ((eq case :intent) (update-fn-ats-phasesi 0 (if finishp 5 1) fn-allocation-turn-slots))
                     ((eq case :finishing) (update-fn-ats-phasesi 0 4 fn-allocation-turn-slots))
                     (t fn-allocation-turn-slots)))
              (fn-page-read-pool
               (cond ((eq case :draining) (fn-aec-pool-drain-internal fn-page-read-pool))
                     ((eq case :recovery) (fn-aec-pool-uncertain-internal fn-page-read-pool))
                     ((eq case :zero-count) (update-fn-prp-alloc-active-turns 0 fn-page-read-pool))
                     ((eq case :count-domain) (update-fn-prp-alloc-active-turns 1000 fn-page-read-pool))
                     (t fn-page-read-pool))))
        (mv (if (eq case :wrong-nonce) (+ 1 nonce) nonce) fn-allocation-turn-slots fn-page-read-pool)))))))))

; Calls both actual subject and source observer from identically reconstructed
; concrete inputs. The full 18-field view includes all scalar pool fields and
; every element of both arrays; literal correspondence includes word and nonce.
(defun atsct-entry (case expected cells operations)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-page-read-pool
  (mv-let (ok fn-page-read-pool)
   (with-local-stobj fn-allocation-turn-slots
    (mv-let (ok fn-allocation-turn-slots fn-page-read-pool)
     (mv-let (ignored fn-allocation-turn-slots fn-page-read-pool)
      (atsct-init case nil fn-allocation-turn-slots fn-page-read-pool)
      (declare (ignore ignored))
      (let ((valid (fn-aec-pool-statep fn-page-read-pool))
            (slot (if (eq case :wrong-slot) 2 0))
            (role (if (eq case :wrong-role) :wrong-role :connection-start)))
       (mv-let (word nonce fn-allocation-turn-slots fn-page-read-pool)
        (fn-ats-enter-internal slot role fn-allocation-turn-slots fn-page-read-pool)
        (let ((actual (list word nonce (atsct-decode-view (atst-view fn-allocation-turn-slots fn-page-read-pool)))))
         (mv-let (ignored fn-allocation-turn-slots fn-page-read-pool)
          (atsct-init case nil fn-allocation-turn-slots fn-page-read-pool)
          (declare (ignore ignored))
          (mv-let (ow on fn-allocation-turn-slots fn-page-read-pool oc ops sites)
           (fn-atsc-enter slot role fn-allocation-turn-slots fn-page-read-pool)
           (mv (and valid (eq word expected)
                    (equal (list ow on (atsct-decode-view (atst-view fn-allocation-turn-slots fn-page-read-pool))) actual)
                    (equal oc cells) (equal (len ops) operations) (consp sites)
                    (<= oc 40) (<= (len ops) 51)
                    (if (eq expected :gate-owned)
                        (and (eq word :gate-owned)
                             (equal oc (+ 35 (if (fn-prl-nth 4
                               (fn-owner-page-read-ledger fn-page-read-pool)) 5 4)))
                             (equal (len ops) 51))
                      (and (not (eq word :gate-owned))
                           (not (and (equal oc (+ 35 (if (fn-prl-nth 4
                             (fn-owner-page-read-ledger fn-page-read-pool)) 5 4)))
                                     (equal (len ops) 51))))))
               fn-allocation-turn-slots fn-page-read-pool)))))))
     (mv ok fn-page-read-pool)))
   ok)))

(assert-event (atsct-entry :success :gate-owned 40 51))
(assert-event (atsct-entry :legacy :gate-owned 39 51))
(assert-event (atsct-entry :identities :read-identities-exhausted 10 31))
(assert-event (atsct-entry :resources :read-resources-unavailable 25 46))
(assert-event (atsct-entry :domain-next :invalid-resource-state 0 14))
(assert-event (atsct-entry :gate-room :yield 0 11))
(assert-event (atsct-entry :draining :yield 0 0))
(assert-event (atsct-entry :recovery :recovery-required 0 0))
(assert-event (atsct-entry :busy :busy 0 0))
(assert-event (atsct-entry :wrong-role :unsupported-slots 0 0))
(assert-event (atsct-entry :wrong-slot :unsupported-slots 0 0))
; Model raw retained entry intent, outside ordinary returned correspondence.
(assert-event (atsct-entry :intent :recovery-required 0 0))
; CORRUPTED logical funding, though the separate physical pool invariant holds.
(assert-event (atsct-entry :invalid-funded :invalid-resource-state 10 31))
; CORRUPTED ATS correspondence: an idle slot cannot coexist with domain active
; turns in this two-slot maintained fixture. Scalar overflow branch is tested,
; not asserted reachable in the composed maintained machine.
(assert-event (atsct-entry :count-domain :recovery-required 0 1))

(defun atsct-finish (case expected operations)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-page-read-pool
  (mv-let (ok fn-page-read-pool)
   (with-local-stobj fn-allocation-turn-slots
    (mv-let (ok fn-allocation-turn-slots fn-page-read-pool)
     (mv-let (nonce fn-allocation-turn-slots fn-page-read-pool)
      (atsct-init case t fn-allocation-turn-slots fn-page-read-pool)
      (let ((valid (fn-aec-pool-statep fn-page-read-pool))
            (slot (if (eq case :wrong-slot) 2 0)))
       (mv-let (word fn-allocation-turn-slots fn-page-read-pool)
        (fn-ats-finish-owned slot nonce fn-allocation-turn-slots fn-page-read-pool)
        (let ((actual (list word (atsct-decode-view (atst-view fn-allocation-turn-slots fn-page-read-pool)))))
         (mv-let (nonce fn-allocation-turn-slots fn-page-read-pool)
          (atsct-init case t fn-allocation-turn-slots fn-page-read-pool)
          (mv-let (ow fn-allocation-turn-slots fn-page-read-pool oc ops sites)
           (fn-atsc-finish slot nonce fn-allocation-turn-slots fn-page-read-pool)
           (mv (and valid (eq word expected)
                    (equal (list ow (atsct-decode-view (atst-view fn-allocation-turn-slots fn-page-read-pool))) actual)
                    (equal oc 0) (equal (len ops) operations) (consp sites))
               fn-allocation-turn-slots fn-page-read-pool)))))))
     (mv ok fn-page-read-pool)))
   ok)))

(assert-event (atsct-finish :owned :left 1))
(assert-event (atsct-finish :body :left 1))
(assert-event (atsct-finish :draining :left 1))
(assert-event (atsct-finish :idle :stale 0))
(assert-event (atsct-finish :duplicate :stale 0))
(assert-event (atsct-finish :reuse :stale 0))
(assert-event (atsct-finish :wrong-nonce :stale 0))
(assert-event (atsct-finish :wrong-slot :stale 0))
(assert-event (atsct-finish :recovery :recovery-required 0))
; Model raw retained leave intent before decrement; no ordinary finish allowed.
(assert-event (atsct-finish :intent :stale 0))
; CORRUPTED maintained slot/count correspondence, physical pool remains valid.
(assert-event (atsct-finish :zero-count :recovery-required 0))
; MUTATION: phase4 is reserved, not published by a normal returned ATS edge.
(assert-event (atsct-finish :finishing :left 1))

; Literal successful-issuer census witness and premise removal. Every retained
; hypothesis (there are none besides :issued) is vacuous in the removal case;
; actual :issued is false, and the complete 34/35 cells +38 operations fails.
(assert-event
 (let* ((ledger *ats-ledger*) (obs (fn-atsc-issue ledger 1000)))
  (mv-let (word nonce next-ledger) (fn-aec-collection-issue ledger 1000)
   (and (eq word :issued)
        (equal (fn-atsc-value obs) (list word nonce next-ledger))
        (equal (fn-atsc-cells obs) (+ 30 (if (fn-prl-nth 4 ledger) 5 4)))
        (equal (len (fn-atsc-ops obs)) 38)))))
(assert-event
 (let* ((ledger '((1000 1000 1000 1000 7) (0 0 0 0 7) 7 (:lifetime-holder) (0 0 0 0 0)))
        (obs (fn-atsc-issue ledger 1000)))
  (mv-let (word nonce next-ledger) (fn-aec-collection-issue ledger 1000)
   (and (not (eq word :issued))
        (equal (fn-atsc-value obs) (list word nonce next-ledger))
        (not (and (equal (fn-atsc-cells obs) (+ 30 (if (fn-prl-nth 4 ledger) 5 4)))
                  (equal (len (fn-atsc-ops obs)) 38)))))))
