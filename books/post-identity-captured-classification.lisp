; Proof-only invariant for the actual bounded current-RCL2 recognizer.
(in-package "ACL2")
(include-book "post-identity-captured")
(defun fn-pic-classification-productp (c incoming held)
 (let ((pos (fn-pic-get pos c)))
  (and (equal (fn-pic-get phase c) :magic)
       (true-listp incoming) (true-listp held)
       (equal (fn-pic-get incoming-n c) (len incoming))
       (equal (fn-pic-get held-n c) (len held))
       (<= *fn-rcl-tombstone-fixed* (len held))
       (natp pos) (<= pos 8)
       (equal (take pos held) (take pos *fn-rcl-magic*)))))
(defun fn-pic-classification-outcomep (c incoming held)
 (or (fn-pic-classification-productp c incoming held)
     (and (equal (fn-pic-get phase c) :tomb-flag) (fn-rcl-tombstonep held))
     (and (equal (fn-pic-get phase c) :source-held) (not (fn-rcl-tombstonep held)))))
(defun fn-pic-classification-observationp (c observation held)
 (let ((d (fn-pic-demand c)))
  (and (fn-pic-observation-okp c d observation)
       (or (equal d :control)
           (equal (fn-pic-observed-byte d observation) (nth (fn-pic-get pos c) held))))))
(local (defthm fn-pic-cl-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-cl-at-least-is-length
 (implies (natp n) (equal (fn-rcl-at-leastp n x) (<= n (len x))))
 :hints (("Goal" :induct (fn-rcl-at-leastp n x)
  :in-theory (enable fn-rcl-at-leastp len)))))
(local (defthm fn-pic-cl-take-next
 (implies (natp n)
  (equal (take (+ 1 n) x) (append (take n x) (list (nth n x)))))
 :hints (("Goal" :induct (take n x) :in-theory (enable take nth binary-append)))))
(local (defthm fn-pic-cl-take-zero (equal (take 0 x) nil)
 :hints (("Goal" :in-theory (enable take)))))
(defthm fn-pic-feed-funded-preserves-exact-tombstone-classification
 (implies (and (fn-pic-classification-productp c incoming held)
               (fn-pic-classification-observationp c observation held))
   (fn-pic-classification-outcomep
    (mv-nth 1 (fn-pic-feed-funded c observation fuel)) incoming held))
 :rule-classes nil
 :hints (("Goal" :cases
  ((equal (fn-pic-get pos c) 0) (equal (fn-pic-get pos c) 1)
   (equal (fn-pic-get pos c) 2) (equal (fn-pic-get pos c) 3)
   (equal (fn-pic-get pos c) 4) (equal (fn-pic-get pos c) 5)
   (equal (fn-pic-get pos c) 6) (equal (fn-pic-get pos c) 7))
 :in-theory (e/d (fn-pic-classification-productp fn-pic-classification-outcomep
    fn-pic-classification-observationp fn-pic-feed-funded fn-pic-feed fn-pic-demand
    fn-pic-start-parser fn-pic-finish fn-rcl-tombstonep fn-rcl-prefixp binary-append take nth)
  (fn-pic-at fn-pic-observation-okp fn-pic-observed-byte fn-rcl-at-leastp
   fn-pic-parser fn-psc-begin fn-pic-spanp fn-pic-span-length fn-pic-span-offset update-nth)))))
(local (defthm fn-pic-cl-control-is-exact
 (implies (and (fn-pic-classification-productp c incoming held)
               (<= 8 (fn-pic-get pos c)))
  (fn-pic-classification-observationp c :control held))
 :hints (("Goal" :in-theory (e/d (fn-pic-classification-productp
    fn-pic-classification-observationp fn-pic-demand fn-pic-observation-okp)
  (fn-pic-at nth take update-nth))))))
(local (defthm fn-pic-cl-product-outcome-unfolds
 (implies (fn-pic-classification-productp c incoming held)
          (fn-pic-classification-outcomep c incoming held))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-classification-outcomep) (fn-pic-classification-productp))))))
(defthm fn-pic-next-preserves-exact-tombstone-classification
 (implies (fn-pic-classification-productp c fn-octets held)
  (fn-pic-classification-outcomep (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets held))
 :rule-classes nil
 :hints (("Goal" :use
 ((:instance fn-pic-feed-funded-preserves-exact-tombstone-classification
    (incoming fn-octets) (observation :control))
  (:instance fn-pic-cl-control-is-exact (incoming fn-octets))
  (:instance fn-pic-cl-product-outcome-unfolds (incoming fn-octets)))
 :in-theory (e/d (fn-pic-next fn-pic-demand fn-pic-classification-productp)
  (fn-pic-at fn-pic-feed-funded fn-pic-classification-outcomep fn-pic-classification-observationp
   fn-pic-cl-control-is-exact fn-pic-observation-okp nth take update-nth)))))
(defun fn-pic-classification-entryp (c incoming held)
 (and (true-listp incoming) (true-listp held)
      (equal (fn-pic-get incoming-n c) (len incoming))
      (equal (fn-pic-get held-n c) (len held))))
(defthm fn-pic-feed-funded-establishes-exact-tombstone-classification
 (implies (and (fn-pic-classification-entryp c incoming held)
               (equal (fn-pic-get phase c) :source-incoming))
  (let ((next (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
   (implies (member-eq (fn-pic-get phase next) '(:magic :source-held))
    (fn-pic-classification-outcomep next incoming held))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-pic-classification-entryp fn-pic-classification-productp fn-pic-classification-outcomep
    fn-pic-feed-funded fn-pic-feed fn-pic-start-parser fn-pic-finish fn-rcl-tombstonep)
   (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-parser
    fn-psc-step fn-psc-result fn-psc-begin fn-pic-source-result fn-pic-spanp
    fn-rcl-at-leastp fn-rcl-prefixp nth take update-nth)))))
(defthm fn-pic-next-establishes-exact-tombstone-classification
 (implies (and (fn-pic-classification-entryp c fn-octets held)
               (equal (fn-pic-get phase c) :source-incoming))
  (let ((next (mv-nth 1 (fn-pic-next c fuel fn-octets))))
   (implies (member-eq (fn-pic-get phase next) '(:magic :source-held))
    (fn-pic-classification-outcomep next fn-octets held))))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-pic-feed-funded-establishes-exact-tombstone-classification
    (incoming fn-octets) (observation :control))
   (:instance fn-pic-feed-funded-establishes-exact-tombstone-classification
    (incoming fn-octets) (fuel (- fuel 1))
    (observation (list :incoming-byte (fn-pic-get incoming-token c)
      (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next fn-pic-classification-entryp fn-pic-finish)
  (fn-pic-at fn-pic-feed-funded fn-pic-demand fn-pic-classification-outcomep
   fn-octets-get nth update-nth)))))
