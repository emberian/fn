; K3 and K6 over the fault-free consumer reference model: a retried append
; answers its recorded outcome, and an accepted ack settles.
(in-package "ACL2")
(include-book "owed-consumer")
(include-book "owed-discharge")

(local (in-theory (current-theory 'fn2-cns-class)))

(local (defthm cns-rs-alist-put
         (implies (alistp st) (alistp (put-assoc-equal k v st)))))
(local (defthm cns-rs-assoc-put
         (equal (assoc-equal key (put-assoc-equal k v st))
                (if (equal key k) (cons k v) (assoc-equal key st)))))
(local (defthm cns-rs-alist-model-put
         (implies (alistp st) (alistp (fn2-cns-model-put k v st)))
         :hints (("Goal" :in-theory (enable fn2-cns-model-put)))))
(local (defthm cns-rs-get-put
         (implies (alistp st)
                  (equal (fn2-cns-get key (fn2-cns-model-put k v st))
                         (if (equal key k) v (fn2-cns-get key st))))
         :hints (("Goal" :in-theory (enable fn2-cns-model-put fn2-cns-get)))))
(local (defthm cns-rs-get-non-alist
         (implies (not (alistp st)) (equal (fn2-cns-get k st) nil))
         :hints (("Goal" :in-theory (enable fn2-cns-get)))))
(local (defthm cns-rs-mv-nth-cons
         (equal (mv-nth n (cons x xs))
                (if (zp n) x (mv-nth (1- n) xs)))))
(local (defthm cns-rs-at-nil (equal (fn2-cns-at k nil) nil)
         :hints (("Goal" :in-theory (enable fn2-cns-at)))))

;; K3. A recorded outcome is answered before admission and the step only
;; touches the wait table after it, so the log is unchanged.
(local (defthm cns-rs-step-replay
         (let ((prior (fn2-cns-at (cons (nth 1 op) (nth 4 op)) (fn2-cns-get :outcomes st))))
           (implies (and (equal (fn2-cns-class op) 'append) (nth 4 op) prior
                         (equal (car prior) (list (nth 2 op) (nth 3 op))))
                    (and (equal (mv-nth 0 (fn2-cns-step op st nil)) (cadr prior))
                         (equal (fn2-cns-get :log (mv-nth 2 (fn2-cns-step op st nil)))
                                (fn2-cns-get :log st)))))
         :hints (("Goal" :cases ((alistp st))
                  :in-theory (enable fn2-cns-step fn2-cns-verb-step fn2-cns-append fn2-cns-wake)))))
(local (defthm cns-rs-run-replay
         (fn2-cns-k3 (mv-nth 0 (fn2-cns-model-run ops st nil)))
         :hints (("Goal" :induct (fn2-cns-model-run ops st nil)
                  :in-theory (e/d (fn2-cns-model-run fn2-cns-k3) (mv-nth fn2-cns-step))))))
(defthm fn2-cns-append-retry-proved
  (fn2-cns-append-retry$owed ops)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-cns-append-retry$owed fn2-cns-trace))))
(fn2-owed-discharge fn2-cns-append-retry fn2-cns-append-retry-proved)

;; K6. An accepted ack leaves the grants, registrations, authority and log
;; as they were and records TO; a repeat needs no reservation, and the
;; meter that admitted the first ack admits the repeat and POSITION.
(local (defun cns-rs-frame-key-p (key) (member-eq key '(:waits :acks :charged))))
(local (defthm cns-rs-frame-reads
         (implies (and (alistp st) (cns-rs-frame-key-p key))
                  (and (equal (fn2-cns-may-consume (fn2-cns-model-put key v st) p) (fn2-cns-may-consume st p))
                       (equal (fn2-cns-scope-problem (fn2-cns-model-put key v st) p k view)
                              (fn2-cns-scope-problem st p k view))
                       (equal (fn2-cns-auth (fn2-cns-model-put key v st) p) (fn2-cns-auth st p))
                       (equal (fn2-cns-frontier (fn2-cns-model-put key v st)) (fn2-cns-frontier st))
                       (equal (fn2-cns-reg (fn2-cns-model-put key v st) p c) (fn2-cns-reg st p c))
                       (equal (fn2-cns-limit (fn2-cns-model-put key v st) p) (fn2-cns-limit st p))
                       (equal (fn2-cns-model-cursor (fn2-cns-model-put key v st) p c r pos)
                              (fn2-cns-model-cursor st p c r pos))))
         :hints (("Goal" :in-theory (enable fn2-cns-may-consume fn2-cns-scope-problem fn2-cns-auth
                                            fn2-cns-frontier fn2-cns-reg fn2-cns-limit fn2-cns-model-cursor)))))
(local (defthm cns-rs-frame-acked
         (implies (and (alistp st) (not (equal key :acks)))
                  (equal (fn2-cns-acked (fn2-cns-model-put key v st) p c e) (fn2-cns-acked st p c e)))
         :hints (("Goal" :in-theory (enable fn2-cns-acked)))))
(local (defthm cns-rs-frame-charged
         (implies (and (alistp st) (not (equal key :charged)))
                  (equal (fn2-cns-charged (fn2-cns-model-put key v st) p) (fn2-cns-charged st p)))
         :hints (("Goal" :in-theory (enable fn2-cns-charged)))))
(local (defthm cns-rs-at-set
         (equal (fn2-cns-at k (fn2-cns-set key v rows))
                (if (equal k key) v (fn2-cns-at k rows)))
         :hints (("Goal" :in-theory (enable fn2-cns-at fn2-cns-set)))))
(local (defthm cns-rs-charge-frame
         (implies (alistp st)
                  (and (alistp (fn2-cns-model-charge st p a))
                       (equal (fn2-cns-charged (fn2-cns-model-charge st p a) p) (+ (fn2-cns-charged st p) (nfix a)))
                       (equal (fn2-cns-acked (fn2-cns-model-charge st p a) q c e) (fn2-cns-acked st q c e))
                       (equal (fn2-cns-model-charge st p a)
                              (fn2-cns-model-put :charged (fn2-cns-set p (+ (fn2-cns-charged st p) (nfix a))
                                                                     (fn2-cns-get :charged st)) st))))
         :hints (("Goal" :in-theory (enable fn2-cns-model-charge fn2-cns-charged fn2-cns-acked)))))
(local (defthm cns-rs-position-natural
         (natp (fn2-cns-cursor-position k))
         :rule-classes :type-prescription
         :hints (("Goal" :in-theory (enable fn2-cns-cursor-position)))))
(local (defthm cns-rs-acked-natural
         (natp (fn2-cns-acked st p c e))
         :rule-classes :type-prescription
         :hints (("Goal" :in-theory (enable fn2-cns-acked)))))
(local (defthm cns-rs-cursor-position-of-cursor
         (equal (fn2-cns-cursor-position (fn2-cns-model-cursor st p c r pos)) (nfix pos))
         :hints (("Goal" :in-theory (enable fn2-cns-cursor-position fn2-cns-model-cursor)))))
(local (defthm cns-rs-consume-needs-alist
         (implies (not (alistp st)) (not (fn2-cns-may-consume st p)))
         :hints (("Goal" :in-theory (enable fn2-cns-may-consume fn2-cns-allows)))))
(local (defthm cns-rs-scope-needs-registration
         (implies (not (fn2-cns-reg st p (fn2-cns-cursor-consumer k)))
                  (fn2-cns-scope-problem st p k view))
         :hints (("Goal" :in-theory (enable fn2-cns-scope-problem)))))
(local (defthm cns-rs-charged-set
         (implies (alistp st)
                  (equal (fn2-cns-charged (fn2-cns-model-put :charged (fn2-cns-set p x rows) st) p)
                         (nfix x)))
         :hints (("Goal" :in-theory (enable fn2-cns-charged)))))
(local (defthm cns-rs-acked-set
         (implies (alistp st)
                  (equal (fn2-cns-acked (fn2-cns-model-put :acks (fn2-cns-set (list p c e) to rows) st) p c e)
                         (nfix to)))
         :hints (("Goal" :in-theory (enable fn2-cns-acked)))))
(local (defthm cns-rs-ack-settles
         (let* ((st2 (fn2-cns-model-put :waits w (mv-nth 1 (fn2-cns-ack st p k nil))))
                (c (fn2-cns-cursor-consumer k)) (to (fn2-cns-cursor-position k)))
           (implies (equal (fn2-cns-class (mv-nth 0 (fn2-cns-ack st p k nil))) :accepted)
                    (and (equal (mv-nth 0 (fn2-cns-ack st2 p k nil)) (list :accepted (list to)))
                         (equal (fn2-cns-cursor-position (car (cadr (mv-nth 0 (fn2-cns-position st2 p c nil))))) to)
                         (<= (fn2-cns-cursor-position (car (cadr (mv-nth 0 (fn2-cns-position st p c nil))))) to))))
         :hints (("Goal" :cases ((alistp st))
                  :in-theory (enable fn2-cns-ack fn2-cns-position fn2-cns-admit fn2-cns-meter
                                     fn2-consumer-admit)))))
(local (defthm cns-rs-step-ack
         (implies (equal (fn2-cns-class op) 'ack)
                  (let ((st1 (mv-nth 1 (fn2-cns-ack st (nth 1 op) (nth 2 op) nil))))
                    (and (equal (mv-nth 0 (fn2-cns-step op st nil))
                                (mv-nth 0 (fn2-cns-ack st (nth 1 op) (nth 2 op) nil)))
                         (equal (mv-nth 2 (fn2-cns-step op st nil))
                                (fn2-cns-model-put :waits (mv-nth 1 (fn2-cns-wake-list (fn2-cns-get :waits st1) st1 nil))
                                                   st1)))))
         :hints (("Goal" :in-theory (e/d (fn2-cns-step fn2-cns-verb-step fn2-cns-wake) (fn2-cns-ack))))))
(local (defthm cns-rs-run-settles
         (fn2-cns-k6 (mv-nth 0 (fn2-cns-model-run ops st nil)) nil)
         :hints (("Goal" :induct (fn2-cns-model-run ops st nil)
                  :in-theory (e/d (fn2-cns-model-run fn2-cns-k6)
                                  (mv-nth fn2-cns-step fn2-cns-ack fn2-cns-position))))))
(defthm fn2-cns-uncertain-settles-proved
  (fn2-cns-uncertain-settles$owed ops)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-cns-uncertain-settles$owed fn2-cns-trace))))
(fn2-owed-discharge fn2-cns-uncertain-settles fn2-cns-uncertain-settles-proved)
