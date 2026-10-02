; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Proof-only actual stored-hash comparison after semantic digest completion.
(in-package "ACL2")
(include-book "post-identity-captured-refinement")

(defun fn-pic-hash-productp (c incoming held)
 (let* ((msg (fn-pic-span-value (fn-pic-get digest-desc c) incoming))
        (base (fn-pic-get digest-base c)) (pos (fn-pic-get pos c))
        (stored (take 32 (nthcdr base held))))
  (and (equal (fn-pic-get phase c) :digest-compare)
       (true-listp held) (equal (fn-pic-get incoming-n c) (len incoming))
       (equal (fn-pic-get held-n c) (len held)) (member-equal base '(9 41))
       (<= (+ base 32) (len held))
       (equal (fn-pic-get digest c) (fn-blake3 msg))
       (natp pos) (<= pos 32)
       (equal (take pos (fn-pic-get digest c)) (take pos stored)))))
(defun fn-pic-hash-outcomep (c incoming held)
 (or (fn-pic-hash-productp c incoming held)
     (let ((same (equal (fn-blake3 (fn-pic-span-value (fn-pic-get digest-desc c) incoming))
                        (take 32 (nthcdr (fn-pic-get digest-base c) held)))))
      (or (and (equal (fn-pic-get phase c) :groups) same)
          (and (equal (fn-pic-get phase c) :done)
               (equal (fn-pic-get result c) :conflict) (not same))))))
(defun fn-pic-hash-observationp (c observation held)
 (let ((d (fn-pic-demand c)))
  (and (fn-pic-observation-okp c d observation)
       (or (equal d :control)
           (equal (fn-pic-observed-byte d observation)
                  (nth (+ (fn-pic-get digest-base c) (fn-pic-get pos c)) held))))))
(local (defthm fn-pic-hc-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-hc-nth-of-tail
 (implies (and (natp i) (natp j)) (equal (nth i (nthcdr j x)) (nth (+ i j) x)))
 :hints (("Goal" :induct (nthcdr j x) :in-theory (enable nthcdr nth)))))
(local (defthm fn-pic-hc-consp-of-take
 (implies (posp n) (consp (take n x)))
 :hints (("Goal" :expand ((take n x))))))
(local (defthm fn-pic-hc-car-of-take
 (implies (posp n) (equal (car (take n x)) (car x)))
 :hints (("Goal" :expand ((take n x))))))
(local (defthm fn-pic-hc-cdr-of-take
 (implies (posp n) (equal (cdr (take n x)) (take (1- n) (cdr x))))
 :hints (("Goal" :expand ((take n x))))))
(local (defun fn-pic-hc-nth-take-induct (i n x)
 (declare (xargs :measure (nfix i) :guard (and (natp i) (natp n))))
 (if (or (zp i) (zp n)) x
  (fn-pic-hc-nth-take-induct (1- i) (1- n) (if (consp x) (cdr x) nil)))))
(local (defthm fn-pic-hc-nth-of-take
 (implies (and (natp i) (natp n) (< i n)) (equal (nth i (take n x)) (nth i x)))
 :hints (("Goal" :induct (fn-pic-hc-nth-take-induct i n x) :in-theory (enable nth take)))))
(local (defthm fn-pic-hc-len-take
 (implies (natp n) (equal (len (take n x)) n))))
(local (defthm fn-pic-hc-take-at-length
 (implies (true-listp x) (equal (take (len x) x) x))
 :hints (("Goal" :induct (len x) :in-theory (enable take len)))))
(local (defthm fn-pic-hc-take-next
 (implies (natp n)
   (equal (take (+ 1 n) x) (append (take n x) (list (nth n x)))))
 :hints (("Goal" :induct (take n x) :in-theory (enable take nth binary-append)))))
(local (defthm fn-pic-hc-equal-prefix-advance
 (implies (and (natp n) (equal (take n x) (take n y)) (equal (nth n x) (nth n y)))
   (equal (take (+ 1 n) x) (take (+ 1 n) y)))
 :hints (("Goal" :in-theory (disable take nth)))))
(local (defthm fn-pic-hc-completed-prefix-is-equality
 (implies (and (true-listp x) (true-listp y) (equal n (len x)) (equal n (len y))
               (equal (take n x) (take n y))) (equal x y))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pic-hc-take-at-length) (:instance fn-pic-hc-take-at-length (x y)))
 :in-theory (disable fn-pic-hc-take-at-length take)))))
(local (defthm fn-pic-hc-different-cell-implies-different
 (implies (not (equal (nth n x) (nth n y))) (not (equal x y)))
 :rule-classes nil))
(defthm fn-pic-feed-funded-preserves-exact-stored-hash-outcome
 (implies (and (fn-pic-hash-productp c incoming held)
               (fn-pic-hash-observationp c observation held))
   (fn-pic-hash-outcomep (mv-nth 1 (fn-pic-feed-funded c observation fuel)) incoming held))
 :rule-classes nil
 :hints (("Goal" :use
 ((:instance fn-pic-hc-completed-prefix-is-equality
   (x (fn-pic-get digest c)) (y (take 32 (nthcdr (fn-pic-get digest-base c) held)))
   (n (fn-pic-get pos c)))
  (:instance fn-pic-hc-different-cell-implies-different
   (x (fn-pic-get digest c)) (y (take 32 (nthcdr (fn-pic-get digest-base c) held)))
   (n (fn-pic-get pos c)))
  (:instance fn-pic-hc-equal-prefix-advance
   (x (fn-pic-get digest c)) (y (take 32 (nthcdr (fn-pic-get digest-base c) held)))
   (n (fn-pic-get pos c))))
 :in-theory (e/d (fn-pic-hash-productp fn-pic-hash-outcomep fn-pic-hash-observationp
                 fn-pic-feed-funded fn-pic-feed fn-pic-finish fn-pic-demand fn-pic-groups-start)
 (fn-pic-at fn-pic-observation-okp fn-pic-observed-byte fn-pic-groups-begin
  fn-pic-span-value fn-blake3 fn-pic-hc-equal-prefix-advance fn-pic-hc-take-next take nth nthcdr update-nth)))))
(local (defthm fn-pic-hc-control-observation-is-exact
 (implies (and (fn-pic-hash-productp c incoming held) (<= 32 (fn-pic-get pos c)))
  (fn-pic-hash-observationp c :control held))
 :hints (("Goal" :in-theory (e/d (fn-pic-hash-productp fn-pic-hash-observationp
      fn-pic-demand fn-pic-observation-okp) (fn-pic-at fn-blake3 fn-pic-span-value nth take nthcdr))))))
(local (defthm fn-pic-hc-product-outcome-unfolds
 (implies (fn-pic-hash-productp c incoming held) (fn-pic-hash-outcomep c incoming held))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-hash-outcomep) (fn-pic-hash-productp))))))
(defthm fn-pic-next-preserves-exact-stored-hash-outcome
 (implies (fn-pic-hash-productp c fn-octets held)
   (fn-pic-hash-outcomep (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets held))
 :rule-classes nil
 :hints (("Goal" :use
 ((:instance fn-pic-feed-funded-preserves-exact-stored-hash-outcome
   (incoming fn-octets) (observation :control))
  (:instance fn-pic-hc-control-observation-is-exact (incoming fn-octets))
  (:instance fn-pic-hc-product-outcome-unfolds (incoming fn-octets)))
 :in-theory (e/d (fn-pic-next fn-pic-demand fn-pic-hash-productp)
 (fn-pic-at fn-pic-feed-funded fn-pic-hash-outcomep fn-pic-hash-observationp
  fn-pic-hc-control-observation-is-exact fn-pic-observation-okp fn-blake3 fn-pic-span-value
  nth take nthcdr update-nth)))))
(defun fn-pic-hash-entry-layoutp (c held)
 (let ((base (fn-pic-get digest-base c)))
  (and (true-listp held) (equal (fn-pic-get held-n c) (len held))
       (member-equal base '(9 41)) (<= (+ base 32) (len held)))))
(local (defthm fn-pic-hc-digest-feedback-starts-comparison
 (implies (equal (fn-pic-get phase c) :digest-next)
  (let ((next (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state))))
   (and (equal (fn-pic-hash-entry-layoutp next held) (fn-pic-hash-entry-layoutp c held))
        (implies (equal (fn-pic-get phase next) :digest-compare)
                 (equal (fn-pic-get pos next) 0)))))
 :hints (("Goal" :in-theory
  (e/d (fn-pic-digest-next fn-pic-feed-funded fn-pic-feed fn-pic-finish fn-pic-hash-entry-layoutp)
   (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-digest-effect
    fn-pic-parser fn-psc-step fn-psc-result fn-pic-span-value fn-blake3 nth update-nth))))))
(local (defthm fn-pic-hc-take-zero (equal (take 0 x) nil)
 :hints (("Goal" :in-theory (enable take)))))
(local (defthm fn-pic-hc-trajectory-implies-completed-hash
 (implies (and (fn-pic-digest-trajectoryp limit c incoming pgs-digest-state)
               (equal (fn-pic-get phase c) :digest-compare))
  (and (equal (fn-pic-get incoming-n c) (len incoming))
       (equal (fn-pic-get digest c)
              (fn-blake3 (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-digest-trajectoryp)
  (fn-pic-at pgs-dcs-invariantp fn-pic-span-value fn-pic-span-length fn-pic-spanp
   fn-b3-octet-listp fn-blake3 take nth nthcdr update-nth))))))
(defthm fn-pic-digest-next-establishes-exact-stored-hash-product
 (implies (and (fn-pic-digest-trajectoryp limit c incoming pgs-digest-state)
               (fn-pic-hash-entry-layoutp c held)
               (equal (fn-pic-get phase c) :digest-next))
  (let ((next (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state))))
   (implies (equal (fn-pic-get phase next) :digest-compare)
            (fn-pic-hash-productp next incoming held))))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-pic-hc-digest-feedback-starts-comparison fn-pic-digest-next-preserves-full-virtual-trajectory
   (:instance fn-pic-hc-trajectory-implies-completed-hash
    (c (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state)))
    (pgs-digest-state (mv-nth 3 (fn-pic-digest-next c fuel pgs-digest-state)))))
 :in-theory (e/d (fn-pic-hash-entry-layoutp fn-pic-hash-productp)
  (fn-pic-at fn-pic-digest-next fn-pic-digest-trajectoryp pgs-dcs-invariantp fn-pic-span-value fn-pic-span-length
   fn-pic-spanp fn-b3-octet-listp fn-blake3
   fn-pic-hc-digest-feedback-starts-comparison take nth nthcdr update-nth)))))
