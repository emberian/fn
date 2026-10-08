; Custody: every bound row is covered in all five resource coordinates.
; This predicate is proof state, never a served-path whole-ledger scan.
(in-package "ACL2")
(include-book "page-read-ledger")
(include-book "page-read-budget-growth")

(defun fn-prl-row-wfp (entry)
  (declare (xargs :guard t))
  (and (consp entry)
       (fn-prs-vectorp (fn-prl-nth 0 (cdr entry)))
       (implies (equal (fn-prl-nth 1 (cdr entry)) :issued)
                (and (fn-prs-vectorp (fn-prl-nth 2 (cdr entry)))
                     (fn-prs-below (fn-prl-nth 2 (cdr entry))
                                   (fn-prl-nth 0 (cdr entry)))))))

(defun fn-prl-rows-wfp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-prl-row-wfp (car rows)) (fn-prl-rows-wfp (cdr rows)))
    (equal rows nil)))

(defun fn-prl-row-sum (n rows)
  (declare (xargs :guard (natp n)))
  (if (consp rows)
      (+ (nfix (fn-prl-nth n (fn-prl-nth 0
                        (if (consp (car rows)) (cdar rows) nil))))
         (fn-prl-row-sum n (cdr rows)))
    0))

(local
 (defthm fn-prl-rs-nats-nth
   (implies (and (fn-prs-nats-p x) (natp n) (< n (len x)))
            (natp (fn-prl-nth n x)))
   :hints (("Goal" :in-theory (enable fn-prs-nats-p fn-prl-nth)
            :induct (fn-prl-nth n x)))))
(local
 (defthm fn-prl-rs-vector-nth
   (implies (and (fn-prs-vectorp x) (natp n) (< n 5))
            (natp (fn-prl-nth n x)))
   :hints (("Goal" :in-theory (enable fn-prs-vectorp)))))

(defun fn-prl-row-sum-invp (ledger)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-prl-nth)))))
  (let ((rows (fn-prl-nth 3 ledger)) (charged (fn-prl-nth 1 ledger)))
    (and (fn-prs-vectorp charged)
         (fn-prl-rows-wfp rows)
         (<= (fn-prl-row-sum 0 rows) (fn-prl-nth 0 charged))
         (<= (fn-prl-row-sum 1 rows) (fn-prl-nth 1 charged))
         (<= (fn-prl-row-sum 2 rows) (fn-prl-nth 2 charged))
         (<= (fn-prl-row-sum 3 rows) (fn-prl-nth 3 charged))
         (<= (fn-prl-row-sum 4 rows) (fn-prl-nth 4 charged)))))

(local
 (defthm fn-prl-rs-nth-build
   (and (equal (fn-prl-nth 0 (fn-prl-build b c n r u)) b)
        (equal (fn-prl-nth 1 (fn-prl-build b c n r u)) c)
        (equal (fn-prl-nth 2 (fn-prl-build b c n r u)) n)
        (equal (fn-prl-nth 3 (fn-prl-build b c n r u)) r))
   :hints (("Goal" :in-theory (enable fn-prl-nth fn-prl-build)))))

(local
 (defthm fn-prl-rs-vector-components
   (implies (fn-prs-vectorp x)
            (and (true-listp x)
                 (natp (fn-prl-nth 0 x)) (natp (fn-prl-nth 1 x))
                 (natp (fn-prl-nth 2 x)) (natp (fn-prl-nth 3 x))
                 (natp (fn-prl-nth 4 x))))
   :hints (("Goal" :in-theory (enable fn-prs-vectorp fn-prs-nats-p fn-prl-nth)))))

(local
 (defthm fn-prl-rs-wfp-binding
   (implies (and (fn-prl-rows-wfp rows) (fn-prl-binding token rows))
            (fn-prl-row-wfp (fn-prl-binding token rows)))
   :hints (("Goal" :in-theory (enable fn-prl-binding)
            :induct (fn-prl-binding token rows)))))

(local
 (defthm fn-prl-rs-wfp-revappend
   (implies (and (fn-prl-rows-wfp a) (fn-prl-rows-wfp b))
            (fn-prl-rows-wfp (revappend a b)))
   :hints (("Goal" :induct (revappend a b)))))

(local
 (defthm fn-prl-rs-wfp-remove-aux
   (implies (and (fn-prl-rows-wfp rows) (fn-prl-rows-wfp rev))
            (fn-prl-rows-wfp (fn-prl-remove-aux token rows rev)))
   :hints (("Goal" :in-theory (enable fn-prl-remove-aux)
            :induct (fn-prl-remove-aux token rows rev)))))

(local
 (defthm fn-prl-rs-wfp-remove
   (implies (fn-prl-rows-wfp rows)
            (fn-prl-rows-wfp (fn-prl-remove token rows)))
   :hints (("Goal" :in-theory (enable fn-prl-remove)))))

(local
 (defthm fn-prl-rs-sum-revappend
   (equal (fn-prl-row-sum n (revappend a b))
          (+ (fn-prl-row-sum n a) (fn-prl-row-sum n b)))
   :hints (("Goal" :induct (revappend a b)))))

(local
 (defthm fn-prl-rs-sum-remove-aux-upper
   (<= (fn-prl-row-sum n (fn-prl-remove-aux token rows rev))
       (+ (fn-prl-row-sum n rows) (fn-prl-row-sum n rev)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-prl-remove-aux)
            :induct (fn-prl-remove-aux token rows rev)))))

(local
 (defthm fn-prl-rs-sum-remove-aux-bound
   (implies (fn-prl-binding token rows)
            (<= (+ (nfix (fn-prl-nth n (fn-prl-nth 0
                              (cdr (fn-prl-binding token rows)))))
                   (fn-prl-row-sum n (fn-prl-remove-aux token rows rev)))
                (+ (fn-prl-row-sum n rows) (fn-prl-row-sum n rev))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-prl-binding fn-prl-remove-aux)
            :induct (fn-prl-remove-aux token rows rev)))))

(local
 (defthm fn-prl-rs-sum-remove-bound
   (implies (fn-prl-binding token rows)
            (<= (+ (nfix (fn-prl-nth n (fn-prl-nth 0
                              (cdr (fn-prl-binding token rows)))))
                   (fn-prl-row-sum n (fn-prl-remove token rows)))
                (fn-prl-row-sum n rows)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-prl-remove)
            :use ((:instance fn-prl-rs-sum-remove-aux-bound (rev nil)))))))

(local
 (defthm fn-prl-rs-binding-below-sum
   (<= (nfix (fn-prl-nth n (fn-prl-nth 0
                           (cdr (fn-prl-binding token rows)))))
       (fn-prl-row-sum n rows))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-prl-binding fn-prl-nth)
            :induct (fn-prl-binding token rows)))))

(local
 (defthm fn-prl-rs-vector-shape
   (implies (fn-prs-vectorp x)
            (equal x (list (fn-prl-nth 0 x) (fn-prl-nth 1 x)
                           (fn-prl-nth 2 x) (fn-prl-nth 3 x) (fn-prl-nth 4 x))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-prs-vectorp fn-prl-nth)
            :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
                     (len (cddddr x)) (len (cdr (cddddr x)))
                     (fn-prs-nats-p x) (fn-prs-nats-p (cdr x))
                     (fn-prs-nats-p (cddr x)) (fn-prs-nats-p (cdddr x))
                     (fn-prs-nats-p (cddddr x)) (fn-prs-nats-p (cdr (cddddr x))))))))

(local
 (defthm fn-prl-rs-nth-is-nth
   (implies (natp n) (equal (fn-prl-nth n x) (nth n x)))
   :hints (("Goal" :in-theory (enable fn-prl-nth)))))
(local
 (defun fn-prl-rs-pair-induct (n a b)
   (if (and (consp a) (not (zp n)))
       (fn-prl-rs-pair-induct (- n 1) (cdr a) (if (consp b) (cdr b) nil))
     (list n a b))))
(local
 (defthm fn-prl-rs-plus-nth-general
   (implies (and (natp n) (< n (len a)))
            (equal (nth n (fn-prs-plus a b))
                   (+ (nfix (nth n a)) (nfix (nth n b)))))
   :hints (("Goal" :in-theory (enable fn-prs-plus)
            :induct (fn-prl-rs-pair-induct n a b)))))
(local
 (defthm fn-prl-rs-below-nth-general
   (implies (and (fn-prs-below a b) (natp n))
            (<= (nfix (nth n a)) (nfix (nth n b))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-prs-below)
            :induct (fn-prl-rs-pair-induct n a b)))))

(local
 (defthm fn-prl-rs-nats-nth-standard
   (implies (and (fn-prs-nats-p x) (natp n) (< n (len x)))
            (natp (nth n x)))
   :hints (("Goal" :use fn-prl-rs-nats-nth))))
(local
 (defthm fn-prl-rs-vector-nth-standard
   (implies (and (fn-prs-vectorp x) (natp n) (< n 5))
            (natp (nth n x)))
   :hints (("Goal" :in-theory (enable fn-prs-vectorp)))))

(local
 (defthm fn-prl-rs-plus-nth
   (implies (and (fn-prs-vectorp a) (fn-prs-vectorp b) (natp n) (< n 5))
            (equal (fn-prl-nth n (fn-prs-plus a b))
                   (+ (fn-prl-nth n a) (fn-prl-nth n b))))
   :hints (("Goal" :in-theory (enable fn-prs-vectorp)))))

(local
 (defthm fn-prl-rs-below-nth
   (implies (and (fn-prs-vectorp a) (fn-prs-vectorp b)
                 (fn-prs-below a b) (natp n) (< n 5))
            (<= (fn-prl-nth n a) (fn-prl-nth n b)))
   :rule-classes nil
   :hints (("Goal" :use fn-prl-rs-below-nth-general))))

(local
 (defthm fn-prl-rs-release-nth
   (implies (and (fn-prs-vectorp a) (fn-prs-vectorp b) (natp n) (< n 5))
            (equal (fn-prl-nth n (fn-prs-release-reusable a b))
                   (if (equal n 4) (fn-prl-nth n a)
                     (nfix (- (fn-prl-nth n a) (fn-prl-nth n b))))))
   :hints (("Goal" :in-theory (e/d (fn-prs-release-reusable) (nth))
            :cases ((equal n 0) (equal n 1) (equal n 2) (equal n 3))))))

(local
 (defthm fn-prl-rs-release-vector
   (fn-prs-vectorp (fn-prs-release-reusable a b))
   :hints (("Goal" :in-theory (enable fn-prs-release-reusable fn-prs-vectorp fn-prs-nats-p)))))

(local
 (defthm fn-prl-rs-sum-cons
   (equal (fn-prl-row-sum n (cons (cons key (list demand tag native)) rows))
          (+ (nfix (fn-prl-nth n demand)) (fn-prl-row-sum n rows)))
   :hints (("Goal" :in-theory (enable fn-prl-nth)))))

(local
 (defthm fn-prl-rs-rows-cons
   (equal (fn-prl-rows-wfp (cons entry rows))
          (and (fn-prl-row-wfp entry) (fn-prl-rows-wfp rows)))))

(local (in-theory (disable fn-prl-row-sum fn-prl-rows-wfp)))

(local
 (defthm fn-prl-rs-release-nth-standard
   (implies (and (fn-prs-vectorp a) (fn-prs-vectorp b) (natp n) (< n 5))
            (equal (nth n (fn-prs-release-reusable a b))
                   (if (equal n 4) (nth n a)
                     (nfix (- (nth n a) (nth n b))))))
   :hints (("Goal" :in-theory (disable nth fn-prl-rs-release-nth)
            :use fn-prl-rs-release-nth))))

(local
 (defthm fn-prl-rs-vector-nth-type
   (implies (and (fn-prs-vectorp x) (natp n) (< n 5))
            (natp (nth n x)))
   :rule-classes :type-prescription))

(local
 (defthm fn-prl-rs-refund-covers-rest
   (implies (and (fn-prs-vectorp charged) (fn-prs-vectorp demand)
                 (natp n) (< n 5) (natp rest)
                 (<= (+ (nth n demand) rest) (nth n charged)))
            (<= rest (nth n (fn-prs-release-reusable charged demand))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable nth)))))

(local
 (defthm fn-prl-rs-refund-covers-cached
   (implies (and (fn-prs-vectorp charged) (fn-prs-vectorp demand)
                 (fn-prs-vectorp native) (fn-prs-below native demand)
                 (natp n) (< n 5) (natp rest)
                 (<= (+ (nth n demand) rest) (nth n charged)))
            (<= (+ (nth n (fn-prs-release-reusable demand native)) rest)
                (nth n (fn-prs-release-reusable charged native))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable nth)
            :use ((:instance fn-prl-rs-below-nth (a native) (b demand)))))))

; Statements committed before proof development. No budget premise is
; necessary: make establishes custody for every budget, and refusals retain it.
(defthm fn-prl-make-row-sum-invp
  (fn-prl-row-sum-invp (fn-prl-make budget))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prl-make fn-prl-nth))))

(defthm fn-prl-register-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 1 (fn-prl-register ledger file demand))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prl-register fn-prl-build fn-prl-nth) (nth)))))

(defthm fn-prl-admit-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 2 (fn-prl-admit ledger cid file eoff elen trailer demand native-demand))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prl-admit fn-prs-issue fn-prl-build fn-prl-nth) (nth)))))

(defthm fn-prl-settle-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 1 (fn-prl-settle ledger token cachedp))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prl-settle fn-prl-build fn-prl-nth) (nth)) :use ((:instance fn-prl-rs-wfp-binding (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-sum-remove-bound (n 0) (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-sum-remove-bound (n 1) (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-sum-remove-bound (n 2) (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-sum-remove-bound (n 3) (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-sum-remove-bound (n 4) (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-below-nth (n 0) (a (fn-prl-nth 2 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))) (b (fn-prl-nth 0 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))))
(:instance fn-prl-rs-below-nth (n 1) (a (fn-prl-nth 2 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))) (b (fn-prl-nth 0 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))))
(:instance fn-prl-rs-below-nth (n 2) (a (fn-prl-nth 2 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))) (b (fn-prl-nth 0 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))))
(:instance fn-prl-rs-below-nth (n 3) (a (fn-prl-nth 2 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))) (b (fn-prl-nth 0 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))))))))

(defthm fn-prl-evict-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 1 (fn-prl-evict ledger token))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prl-evict fn-prl-build fn-prl-nth) (nth)) :use ((:instance fn-prl-rs-wfp-binding (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-sum-remove-bound (n 0) (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-sum-remove-bound (n 1) (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-sum-remove-bound (n 2) (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-sum-remove-bound (n 3) (rows (fn-prl-nth 3 ledger)) (token token))
(:instance fn-prl-rs-sum-remove-bound (n 4) (rows (fn-prl-nth 3 ledger)) (token token))))))

(defthm fn-prl-close-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 1 (fn-prl-close ledger file))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prl-close fn-prl-build fn-prl-nth) (nth)) :use ((:instance fn-prl-rs-wfp-binding (rows (fn-prl-nth 3 ledger)) (token (list :incarnation file)))
(:instance fn-prl-rs-sum-remove-bound (n 0) (rows (fn-prl-nth 3 ledger)) (token (list :incarnation file)))
(:instance fn-prl-rs-sum-remove-bound (n 1) (rows (fn-prl-nth 3 ledger)) (token (list :incarnation file)))
(:instance fn-prl-rs-sum-remove-bound (n 2) (rows (fn-prl-nth 3 ledger)) (token (list :incarnation file)))
(:instance fn-prl-rs-sum-remove-bound (n 3) (rows (fn-prl-nth 3 ledger)) (token (list :incarnation file)))
(:instance fn-prl-rs-sum-remove-bound (n 4) (rows (fn-prl-nth 3 ledger)) (token (list :incarnation file)))))))

(defthm fn-prl-reserve-growth-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 2 (fn-prl-reserve-growth ledger amount))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prl-reserve-growth fn-prs-issue fn-prl-build fn-prl-nth fn-prs-vectorp fn-prs-nats-p) (nth)))))

(local
 (defthm fn-prl-rs-shrink-invp
   (implies (fn-prl-row-sum-invp ledger)
            (fn-prl-row-sum-invp
             (mv-nth 1 (fn-prl-resident-shrink amount ledger))))
   :hints (("Goal" :in-theory (disable nth fn-prl-resident-shrink
                     fn-prl-resident-shrink-preserves-custody)
            :use fn-prl-resident-shrink-preserves-custody))))

; In particular G2's NATP premise follows; it is not silently dropped.
(defthm fn-prl-row-sum-bound-reserve-natural
  (implies (and (fn-prl-row-sum-invp ledger)
                (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                       (cons token (list (list amount 0 0 0 0) :cached nil))))
           (natp amount))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prl-nth fn-prs-vectorp fn-prs-nats-p) (nth))
           :use ((:instance fn-prl-rs-wfp-binding (rows (fn-prl-nth 3 ledger)))))))

(defthm fn-prl-convert-growth-preserves-row-sum-invp
  (implies (fn-prl-row-sum-invp ledger)
           (fn-prl-row-sum-invp
            (mv-nth 1 (fn-prl-convert-growth ledger token amount))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prl-convert-growth)
                (fn-prl-row-sum-invp fn-prl-resident-shrink nth))
 :use fn-prl-evict-preserves-row-sum-invp)))

; Discharge G2's charged-covers premise from custody and the exact binding.
; NATP AMOUNT is unnecessary here: row well-formedness supplies it.
(defthm fn-prl-row-sum-covers-bound-reserve
  (implies (and (fn-prl-row-sum-invp ledger)
                (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                       (cons token (list (list amount 0 0 0 0) :cached nil))))
           (<= amount (fn-prl-nth 0 (fn-prl-nth 1 ledger))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-prl-nth) (nth))
 :use ((:instance fn-prl-rs-binding-below-sum (n 0) (rows (fn-prl-nth 3 ledger)))
       fn-prl-row-sum-bound-reserve-natural))))

; G2 with the charged-covers hypothesis discharged (and NATP derived).
(defthm fn-prl-convert-growth-under-row-sum-invp
  (implies (and (fn-prl-row-sum-invp ledger)
                (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                       (cons token (list (list amount 0 0 0 0) :cached nil)))
                (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                                '(0 0 0 0 0) (fn-prl-nth 1 ledger)))
           (and (equal (mv-nth 0 (fn-prl-convert-growth ledger token amount))
                       :protected-growth-admitted)
                (let ((next (mv-nth 1 (fn-prl-convert-growth ledger token amount))))
                  (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next)
                                  '(0 0 0 0 0) (fn-prl-nth 1 next)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-prl-row-sum-invp fn-prl-convert-growth fn-prl-resident-shrink)
 :use (fn-prl-row-sum-covers-bound-reserve fn-prl-row-sum-bound-reserve-natural
       fn-prl-convert-growth-when-charged-covers-the-reserve))))
