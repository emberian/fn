; Discharges fn2-account-ops-conserve (books/accounts.lisp): every ledger
; operation preserves fn2-accounts-conservedp. Acquire and release are one
; "holding step" (a hold cell and its dimension's committed cell move
; together); charge touches neither; the bundles and attribution compose them.
(in-package "ACL2")
(include-book "accounts")
(include-book "owed-discharge")
(local (include-book "arithmetic/top" :dir :system))

;; Index arithmetic of the dimension-major arrays.
(local
 (defthm fn2-acp-mult-mono
   (implies (and (natp a) (natp b) (natp r) (<= a b))
            (<= (* a r) (* b r)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))
(local
 (defthm fn2-acp-ix-injective
   (implies (and (natp i) (natp p) (natp d) (natp d2) (natp r) (< i r) (< p r))
            (equal (equal (+ i (* d2 r)) (+ p (* d r)))
                   (and (equal i p) (equal d2 d))))
   :hints (("Goal" :use ((:instance fn2-acp-mult-mono (a (+ 1 d2)) (b d))
                         (:instance fn2-acp-mult-mono (a (+ 1 d)) (b d2)))))))
(local
 (defthm fn2-acp-ix-in-range
   (implies (and (natp d) (natp p) (natp r) (< d 5) (< p r))
            (< (+ p (* d r)) (* 5 r)))
   :hints (("Goal" :use ((:instance fn2-account-ix-bound (n 5)))))))

;; The readers under each array update.
(local
 (defthm fn2-acp-readers-of-update-hold
   (implies (and (natp (nth *fn2-accounts-rows* fn2-accounts))
                 (natp p) (< p (nth *fn2-accounts-rows* fn2-accounts)) (natp d) (< d 5))
            (let ((new (update-fn2-accounts-holdi (+ p (* d (nth *fn2-accounts-rows* fn2-accounts))) v fn2-accounts)))
              (and (equal (fn2-account-hold i d2 new)
                          (if (and (equal i p) (equal d2 d)) (nfix v) (fn2-account-hold i d2 fn2-accounts)))
                   (equal (fn2-account-reserve i d2 new) (fn2-account-reserve i d2 fn2-accounts))
                   (equal (fn2-account-limit i d2 new) (fn2-account-limit i d2 fn2-accounts))
                   (equal (fn2-account-committed d2 new) (fn2-account-committed d2 fn2-accounts))
                   (equal (fn2-account-capacity d2 new) (fn2-account-capacity d2 fn2-accounts))
                   (equal (nth *fn2-accounts-rows* new) (nth *fn2-accounts-rows* fn2-accounts)))))
   :hints (("Goal" :in-theory (enable fn2-account-holdv fn2-account-reservev fn2-account-limitv
                                      fn2-account-committedv fn2-account-capacityv)))))
(local
 (defthm fn2-acp-readers-of-update-committed
   (let ((new (update-fn2-accounts-committedi d v fn2-accounts)))
     (and (equal (fn2-account-hold i d2 new) (fn2-account-hold i d2 fn2-accounts))
          (equal (fn2-account-reserve i d2 new) (fn2-account-reserve i d2 fn2-accounts))
          (equal (fn2-account-limit i d2 new) (fn2-account-limit i d2 fn2-accounts))
          (implies (and (natp d) (< d 5))
                   (equal (fn2-account-committed d2 new)
                          (if (equal d2 d) (nfix v) (fn2-account-committed d2 fn2-accounts))))
          (equal (fn2-account-capacity d2 new) (fn2-account-capacity d2 fn2-accounts))
          (equal (nth *fn2-accounts-rows* new) (nth *fn2-accounts-rows* fn2-accounts))))
   :hints (("Goal" :in-theory (enable fn2-account-holdv fn2-account-reservev fn2-account-limitv
                                      fn2-account-committedv fn2-account-capacityv)))))
(local
 (defthm fn2-acp-readers-of-update-charge
   (let ((new (update-fn2-accounts-chargei k v fn2-accounts)))
     (and (equal (fn2-account-hold i d2 new) (fn2-account-hold i d2 fn2-accounts))
          (equal (fn2-account-reserve i d2 new) (fn2-account-reserve i d2 fn2-accounts))
          (equal (fn2-account-limit i d2 new) (fn2-account-limit i d2 fn2-accounts))
          (equal (fn2-account-committed d2 new) (fn2-account-committed d2 fn2-accounts))
          (equal (fn2-account-capacity d2 new) (fn2-account-capacity d2 fn2-accounts))
          (equal (nth *fn2-accounts-rows* new) (nth *fn2-accounts-rows* fn2-accounts))))
   :hints (("Goal" :in-theory (enable fn2-account-holdv fn2-account-reservev fn2-account-limitv
                                      fn2-account-committedv fn2-account-capacityv)))))
(local (in-theory (disable fn2-account-hold fn2-account-reserve fn2-account-limit
                           fn2-account-committed fn2-account-capacity
                           update-fn2-accounts-holdi update-fn2-accounts-committedi
                           update-fn2-accounts-chargei fn2-accounts-rows)))
(local
 (defthm fn2-acp-rows-is-nth
   (equal (fn2-accounts-rows fn2-accounts) (nth *fn2-accounts-rows* fn2-accounts))
   :hints (("Goal" :in-theory (enable fn2-accounts-rows)))))

;; The per-dimension sum and limit check under each update.
(local
 (defthm fn2-acp-sum-of-update-hold
   (implies (and (natp (nth *fn2-accounts-rows* fn2-accounts))
                 (natp p) (< p (nth *fn2-accounts-rows* fn2-accounts)) (natp d) (< d 5) (natp v))
            (equal (fn2-account-sum d2 i (update-fn2-accounts-holdi
                                          (+ p (* d (nth *fn2-accounts-rows* fn2-accounts))) v fn2-accounts))
                   (if (and (equal d2 d) (natp i) (<= i p))
                       (+ (fn2-account-sum d i fn2-accounts)
                          (max v (fn2-account-reserve p d fn2-accounts))
                          (- (max (fn2-account-hold p d fn2-accounts) (fn2-account-reserve p d fn2-accounts))))
                     (fn2-account-sum d2 i fn2-accounts))))
   :hints (("Goal" :induct (fn2-account-sum d2 i fn2-accounts)))))
(local
 (defthm fn2-acp-sum-of-update-committed
   (equal (fn2-account-sum d2 i (update-fn2-accounts-committedi d v fn2-accounts))
          (fn2-account-sum d2 i fn2-accounts))
   :hints (("Goal" :induct (fn2-account-sum d2 i fn2-accounts)))))
(local
 (defthm fn2-acp-sum-of-update-charge
   (equal (fn2-account-sum d2 i (update-fn2-accounts-chargei k v fn2-accounts))
          (fn2-account-sum d2 i fn2-accounts))
   :hints (("Goal" :induct (fn2-account-sum d2 i fn2-accounts)))))
(local
 (defthm fn2-acp-limits-of-update-hold
   (implies (and (natp (nth *fn2-accounts-rows* fn2-accounts))
                 (natp p) (< p (nth *fn2-accounts-rows* fn2-accounts)) (natp d) (< d 5) (natp v)
                 (<= v (fn2-account-limit p d fn2-accounts))
                 (fn2-account-limits-ok d2 i fn2-accounts))
            (fn2-account-limits-ok d2 i (update-fn2-accounts-holdi
                                         (+ p (* d (nth *fn2-accounts-rows* fn2-accounts))) v fn2-accounts)))
   :hints (("Goal" :induct (fn2-account-limits-ok d2 i fn2-accounts)))))
(local
 (defthm fn2-acp-limits-of-update-committed
   (equal (fn2-account-limits-ok d2 i (update-fn2-accounts-committedi d v fn2-accounts))
          (fn2-account-limits-ok d2 i fn2-accounts))
   :hints (("Goal" :induct (fn2-account-limits-ok d2 i fn2-accounts)))))
(local
 (defthm fn2-acp-limits-of-update-charge
   (equal (fn2-account-limits-ok d2 i (update-fn2-accounts-chargei k v fn2-accounts))
          (fn2-account-limits-ok d2 i fn2-accounts))
   :hints (("Goal" :induct (fn2-account-limits-ok d2 i fn2-accounts)))))

;; One holding step: row P's hold in dimension D becomes H2 and the
;; dimension's committed moves by the change of max(hold, reserve).
(local
 (defthm fn2-acp-dims-ok-of-hold-step
   (implies (and (natp (nth *fn2-accounts-rows* fn2-accounts))
                 (natp p) (< p (nth *fn2-accounts-rows* fn2-accounts)) (natp d) (< d 5)
                 (natp h2) (natp c2)
                 (<= h2 (fn2-account-limit p d fn2-accounts))
                 (equal c2 (+ (fn2-account-committed d fn2-accounts)
                              (max h2 (fn2-account-reserve p d fn2-accounts))
                              (- (max (fn2-account-hold p d fn2-accounts)
                                      (fn2-account-reserve p d fn2-accounts)))))
                 (<= c2 (fn2-account-capacity d fn2-accounts))
                 (fn2-account-dims-ok d0 fn2-accounts))
            (fn2-account-dims-ok
             d0 (update-fn2-accounts-committedi
                 d c2 (update-fn2-accounts-holdi
                       (+ p (* d (nth *fn2-accounts-rows* fn2-accounts))) h2 fn2-accounts))))
   :hints (("Goal" :induct (fn2-account-dims-ok d0 fn2-accounts)))))
(local
 (defthm fn2-acp-dims-ok-of-update-charge
   (equal (fn2-account-dims-ok d0 (update-fn2-accounts-chargei k v fn2-accounts))
          (fn2-account-dims-ok d0 fn2-accounts))
   :hints (("Goal" :induct (fn2-account-dims-ok d0 fn2-accounts)))))

;; What the invariant says of one row and one dimension.
(local
 (defthm fn2-acp-limits-ok-at
   (implies (and (fn2-account-limits-ok d i fn2-accounts)
                 (natp i) (natp p) (<= i p) (< p (nfix (nth *fn2-accounts-rows* fn2-accounts))))
            (<= (fn2-account-hold p d fn2-accounts) (fn2-account-limit p d fn2-accounts)))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-account-limits-ok d i fn2-accounts)))))
(local
 (defthm fn2-acp-dims-ok-at
   (implies (and (fn2-account-dims-ok d0 fn2-accounts) (natp d0) (natp d) (<= d0 d) (< d 5))
            (and (<= (fn2-account-committed d fn2-accounts) (fn2-account-capacity d fn2-accounts))
                 (fn2-account-limits-ok d 0 fn2-accounts)))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-account-dims-ok d0 fn2-accounts)))))

(local (in-theory (disable fn2-account-dims-ok)))

;; The operations read the arrays by index; the invariant reads them by
;; row and dimension. In range the two agree.
(local
 (defthm fn2-acp-index-readers
   (implies (and (natp (nth *fn2-accounts-rows* fn2-accounts))
                 (natp p) (< p (nth *fn2-accounts-rows* fn2-accounts)) (natp d) (< d 5))
            (let ((ix (+ p (* d (nth *fn2-accounts-rows* fn2-accounts)))))
              (and (equal (fn2-account-holdv ix fn2-accounts) (fn2-account-hold p d fn2-accounts))
                   (equal (fn2-account-reservev ix fn2-accounts) (fn2-account-reserve p d fn2-accounts))
                   (equal (fn2-account-limitv ix fn2-accounts) (fn2-account-limit p d fn2-accounts))
                   (equal (fn2-account-committedv d fn2-accounts) (fn2-account-committed d fn2-accounts))
                   (equal (fn2-account-capacityv d fn2-accounts) (fn2-account-capacity d fn2-accounts)))))
   :hints (("Goal" :in-theory (enable fn2-account-hold fn2-account-reserve fn2-account-limit
                                      fn2-account-committed fn2-account-capacity)))))

;; The three single operations.
(local
 (defthm fn2-acp-acquire-dims-ok
   (implies (and (fn2-account-guard) (fn2-account-dims-ok 0 fn2-accounts))
            (fn2-account-dims-ok 0 (mv-nth 1 (fn2-account-acquire p d a fn2-accounts))))
   :hints (("Goal"
            :in-theory (e/d (fn2-account-acquire)
                            (fn2-acp-dims-ok-of-hold-step))
            :use ((:instance fn2-acp-dims-ok-of-hold-step
                   (d0 0)
                   (h2 (+ a (fn2-account-hold p d fn2-accounts)))
                   (c2 (let ((h (fn2-account-hold p d fn2-accounts))
                             (r (fn2-account-reserve p d fn2-accounts)))
                         (+ (fn2-account-committed d fn2-accounts)
                            (- (max (+ h a) r) (max h r)))))))))))
(local
 (defthm fn2-acp-release-dims-ok
   (implies (and (fn2-account-guard) (fn2-account-dims-ok 0 fn2-accounts))
            (fn2-account-dims-ok 0 (mv-nth 1 (fn2-account-release p d a fn2-accounts))))
   :hints (("Goal"
            :in-theory (e/d (fn2-account-release)
                            (fn2-acp-dims-ok-of-hold-step))
            :use ((:instance fn2-acp-dims-ok-at (d0 0))
                  (:instance fn2-acp-limits-ok-at (i 0))
                  (:instance fn2-acp-dims-ok-of-hold-step
                   (d0 0)
                   (h2 (- (fn2-account-hold p d fn2-accounts) a))
                   (c2 (let ((h (fn2-account-hold p d fn2-accounts))
                             (r (fn2-account-reserve p d fn2-accounts)))
                         (- (fn2-account-committed d fn2-accounts)
                            (- (max h r) (max (- h a) r)))))))))))
(local
 (defthm fn2-acp-charge-dims-ok
   (implies (fn2-account-dims-ok 0 fn2-accounts)
            (fn2-account-dims-ok 0 (mv-nth 1 (fn2-account-charge p k a fn2-accounts))))
   :hints (("Goal" :in-theory (enable fn2-account-charge)))))

(local
 (defthm fn2-acp-acquire-conserves
   (implies (fn2-accounts-conservedp fn2-accounts)
            (fn2-accounts-conservedp (mv-nth 1 (fn2-account-acquire p d a fn2-accounts))))))
(local
 (defthm fn2-acp-release-conserves
   (implies (fn2-accounts-conservedp fn2-accounts)
            (fn2-accounts-conservedp (mv-nth 1 (fn2-account-release p d a fn2-accounts))))))
(local
 (defthm fn2-acp-charge-conserves
   (implies (fn2-accounts-conservedp fn2-accounts)
            (fn2-accounts-conservedp (mv-nth 1 (fn2-account-charge p k a fn2-accounts))))))
(local (in-theory (disable fn2-accounts-conservedp)))

;; The bundles are compositions of the single operations.
(local
 (defthm fn2-acp-acquire2-conserves
   (implies (fn2-accounts-conservedp fn2-accounts)
            (fn2-accounts-conservedp (mv-nth 1 (fn2-account-acquire2 p d1 a1 d2 a2 fn2-accounts))))
   :hints (("Goal" :in-theory (enable fn2-account-acquire2)))))
(local
 (defthm fn2-acp-release2-conserves
   (implies (fn2-accounts-conservedp fn2-accounts)
            (fn2-accounts-conservedp (mv-nth 1 (fn2-account-release2 p d1 a1 d2 a2 fn2-accounts))))
   :hints (("Goal" :in-theory (enable fn2-account-release2)))))
(local
 (defthm fn2-acp-attribute-conserves
   (implies (fn2-accounts-conservedp fn2-accounts)
            (fn2-accounts-conservedp (mv-nth 1 (fn2-account-attribute p q d1 a1 d2 a2 fn2-accounts))))
   :hints (("Goal" :in-theory (enable fn2-account-attribute)))))

(defthm fn2-account-ops-conserve-proved
  (fn2-account-ops-conserve$owed op p q d1 a1 d2 a2 fn2-accounts)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-account-ops-conserve$owed))))

(fn2-owed-discharge fn2-account-ops-conserve fn2-account-ops-conserve-proved)
