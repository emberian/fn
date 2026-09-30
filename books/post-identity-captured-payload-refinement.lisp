; Proof-only immutable virtual payload product for actual byte continuations.
(in-package "ACL2")
(include-book "post-identity-captured")

(defun fn-pic-payload-productp (c incoming held)
 (let* ((id (fn-pic-get incoming-desc c)) (hd (fn-pic-get held-desc c))
        (left (fn-pic-span-value id incoming)) (right (fn-pic-span-value hd held))
        (pos (fn-pic-get pos c)) (phase (fn-pic-get phase c)))
  (and (member-eq phase '(:compare-incoming :compare-held))
       (true-listp incoming) (true-listp held)
       (equal (fn-pic-get incoming-n c) (len incoming))
       (equal (fn-pic-get held-n c) (len held))
       (fn-pic-spanp id (len incoming)) (fn-pic-spanp hd (len held))
       (equal (len left) (len right)) (natp pos) (<= pos (len left))
       (equal (take pos left) (take pos right))
       (implies (equal phase :compare-held)
         (and (< pos (len left)) (equal (fn-pic-get cached c) (nth pos left)))))))
(defun fn-pic-payload-outcomep (c incoming held)
 (or (fn-pic-payload-productp c incoming held)
     (let ((same (equal (fn-pic-span-value (fn-pic-get incoming-desc c) incoming)
                       (fn-pic-span-value (fn-pic-get held-desc c) held))))
      (or (and (equal (fn-pic-get phase c) :groups) same)
          (and (equal (fn-pic-get phase c) :done)
               (equal (fn-pic-get result c) :conflict) (not same))))))
(defun fn-pic-payload-observationp (c observation incoming held)
 (let* ((d (fn-pic-demand c)) (phase (fn-pic-get phase c))
        (source (if (equal phase :compare-held) held incoming))
        (span (if (equal phase :compare-held) (fn-pic-get held-desc c) (fn-pic-get incoming-desc c))))
  (and (fn-pic-observation-okp c d observation)
       (or (equal d :control)
           (equal (fn-pic-observed-byte d observation)
                  (nth (fn-pic-get pos c) (fn-pic-span-value span source)))))))
(local (defthm fn-pic-py-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-py-len-take
 (implies (natp n) (equal (len (take n x)) n))))
(local (defthm fn-pic-py-len-tail
 (implies (natp n) (equal (len (nthcdr n x)) (nfix (- (len x) n))))
 :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr len nfix)))))
(local (defthm fn-pic-py-len-append
 (equal (len (append x y)) (+ (len x) (len y)))
 :hints (("Goal" :induct (append x y) :in-theory (enable binary-append len)))))
(local (defthm fn-pic-py-span-length
 (implies (fn-pic-spanp d (len x))
  (equal (len (fn-pic-span-value d x)) (fn-pic-span-length d (len x))))
 :hints (("Goal" :in-theory (e/d (fn-pic-spanp fn-pic-span-value fn-pic-span-length)
                                (take nthcdr fn-pic-at nth binary-append))))))
(local (defthm fn-pic-py-take-at-length
 (implies (true-listp x) (equal (take (len x) x) x))
 :hints (("Goal" :induct (len x) :in-theory (enable take len)))))
(local (defthm fn-pic-py-take-next
 (implies (natp n)
   (equal (take (+ 1 n) x) (append (take n x) (list (nth n x)))))
 :hints (("Goal" :induct (take n x) :in-theory (enable take nth binary-append)))))
(local (defthm fn-pic-py-equal-prefix-advance
 (implies (and (natp n) (equal (take n x) (take n y)) (equal (nth n x) (nth n y)))
   (equal (take (+ 1 n) x) (take (+ 1 n) y)))
 :hints (("Goal" :in-theory (disable take nth)))))
(local (defthm fn-pic-py-span-is-proper
 (implies (true-listp x) (true-listp (fn-pic-span-value d x)))
 :hints (("Goal" :in-theory (enable fn-pic-span-value)))))
(local (defthm fn-pic-py-completed-prefix-is-equality
 (implies (and (true-listp x) (true-listp y) (equal n (len x)) (equal n (len y))
               (equal (take n x) (take n y)))
   (equal x y))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pic-py-take-at-length) (:instance fn-pic-py-take-at-length (x y)))
 :in-theory (disable fn-pic-py-take-at-length take)))))
(local (defthm fn-pic-py-different-cell-implies-different
 (implies (not (equal (nth n x) (nth n y))) (not (equal x y)))
 :rule-classes nil))
(defthm fn-pic-feed-funded-preserves-exact-payload-outcome
 (implies (and (fn-pic-payload-productp c incoming held)
               (fn-pic-payload-observationp c observation incoming held))
   (fn-pic-payload-outcomep (mv-nth 1 (fn-pic-feed-funded c observation fuel)) incoming held))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pic-py-completed-prefix-is-equality
  (x (fn-pic-span-value (fn-pic-get incoming-desc c) incoming))
  (y (fn-pic-span-value (fn-pic-get held-desc c) held)) (n (fn-pic-get pos c)))
 (:instance fn-pic-py-different-cell-implies-different
  (x (fn-pic-span-value (fn-pic-get incoming-desc c) incoming))
  (y (fn-pic-span-value (fn-pic-get held-desc c) held)) (n (fn-pic-get pos c)))
 (:instance fn-pic-py-equal-prefix-advance
  (x (fn-pic-span-value (fn-pic-get incoming-desc c) incoming))
  (y (fn-pic-span-value (fn-pic-get held-desc c) held)) (n (fn-pic-get pos c))))
 :in-theory (e/d (fn-pic-payload-productp fn-pic-payload-outcomep
                     fn-pic-payload-observationp fn-pic-feed-funded fn-pic-feed fn-pic-finish
                     fn-pic-demand fn-pic-groups-start)
  (fn-pic-at fn-pic-observation-okp fn-pic-observed-byte fn-pic-groups-begin
   fn-pic-span-value fn-pic-spanp fn-pic-span-length fn-pic-span-offset
   fn-pic-py-equal-prefix-advance fn-pic-span-byte-is-denoted-byte take nth nthcdr update-nth)))))
(local (defthm fn-pic-py-nth-is-octet
 (implies (and (fn-cbor-octet-listp x) (natp i) (< i (len x)))
   (unsigned-byte-p 8 (nth i x)))
 :hints (("Goal" :induct (nth i x)
  :in-theory (enable nth fn-cbor-octet-listp fn-cbor-octetp unsigned-byte-p)))))
(local (defthm fn-pic-py-incoming-observation-is-exact
 (implies (and (fn-pic-payload-productp c fn-octets held)
               (fn-cbor-octet-listp fn-octets)
               (equal (fn-pic-get phase c) :compare-incoming)
               (< (fn-pic-get pos c)
                  (fn-pic-span-length (fn-pic-get incoming-desc c) (fn-pic-get incoming-n c))))
   (fn-pic-payload-observationp c
    (list :incoming-byte (fn-pic-get incoming-token c)
      (fn-pic-span-offset (fn-pic-get incoming-desc c) (fn-pic-get pos c))
      (fn-octets-get (fn-pic-span-offset (fn-pic-get incoming-desc c) (fn-pic-get pos c)) fn-octets))
    fn-octets held))
 :hints (("Goal" :use
  ((:instance fn-pic-span-offset-is-within-source
     (d (fn-pic-get incoming-desc c)) (i (fn-pic-get pos c)) (n (len fn-octets)))
   (:instance fn-pic-py-nth-is-octet
     (x fn-octets) (i (fn-pic-span-offset (fn-pic-get incoming-desc c) (fn-pic-get pos c))))
   (:instance fn-pic-span-byte-is-denoted-byte
     (d (fn-pic-get incoming-desc c)) (i (fn-pic-get pos c)) (xs fn-octets)))
 :in-theory (e/d (fn-pic-payload-productp fn-pic-payload-observationp fn-pic-demand
                    fn-pic-observation-okp fn-pic-observed-byte fn-octets-get)
  (fn-pic-at fn-pic-span-value fn-pic-spanp fn-pic-span-length fn-pic-span-offset
   fn-pic-span-offset-is-within-source fn-pic-py-nth-is-octet
   fn-pic-span-byte-is-denoted-byte nth take nthcdr unsigned-byte-p))))))
(local (defthm fn-pic-py-completed-observation-is-control
 (implies (and (fn-pic-payload-productp c incoming held)
               (equal (fn-pic-get phase c) :compare-incoming)
               (<= (fn-pic-span-length (fn-pic-get incoming-desc c) (fn-pic-get incoming-n c))
                   (fn-pic-get pos c)))
   (fn-pic-payload-observationp c :control incoming held))
 :hints (("Goal" :in-theory (e/d (fn-pic-payload-productp fn-pic-payload-observationp
                   fn-pic-demand fn-pic-observation-okp)
   (fn-pic-at fn-pic-span-length fn-pic-spanp fn-pic-span-value fn-pic-span-offset nth take nthcdr))))))
(local (defthm fn-pic-py-product-outcome-unfolds
 (implies (fn-pic-payload-productp c incoming held) (fn-pic-payload-outcomep c incoming held))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-payload-outcomep) (fn-pic-payload-productp))))))
(defthm fn-pic-next-preserves-exact-payload-outcome
 (implies (and (fn-pic-payload-productp c fn-octets held)
               (fn-cbor-octet-listp fn-octets))
   (fn-pic-payload-outcomep (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets held))
 :rule-classes nil
 :hints (("Goal" :use
 ((:instance fn-pic-feed-funded-preserves-exact-payload-outcome
   (incoming fn-octets) (observation :control))
  (:instance fn-pic-feed-funded-preserves-exact-payload-outcome
   (incoming fn-octets) (fuel (- fuel 1))
   (observation (list :incoming-byte (fn-pic-get incoming-token c)
      (fn-pic-span-offset (fn-pic-get incoming-desc c) (fn-pic-get pos c))
      (fn-octets-get (fn-pic-span-offset (fn-pic-get incoming-desc c) (fn-pic-get pos c)) fn-octets))))
  fn-pic-py-incoming-observation-is-exact
  (:instance fn-pic-py-product-outcome-unfolds (incoming fn-octets))
  (:instance fn-pic-py-completed-observation-is-control (incoming fn-octets))
  (:instance fn-pic-span-offset-is-within-source
     (d (fn-pic-get incoming-desc c)) (i (fn-pic-get pos c)) (n (len fn-octets))))
 :in-theory (e/d (fn-pic-next fn-pic-demand fn-pic-payload-productp)
  (fn-pic-at fn-pic-feed-funded fn-pic-payload-outcomep fn-pic-payload-observationp
   fn-pic-observation-okp fn-pic-span-value fn-pic-spanp fn-pic-span-length
   fn-pic-span-offset fn-pic-observed-byte fn-octets-get fn-cbor-octet-listp
   fn-pic-py-incoming-observation-is-exact fn-pic-py-completed-observation-is-control
   fn-pic-span-offset-is-within-source fn-pic-span-byte-is-denoted-byte nth take nthcdr update-nth)))))
(defun fn-pic-payload-entryp (c incoming held)
 (and (true-listp incoming) (true-listp held)
      (equal (fn-pic-get incoming-n c) (len incoming))
      (equal (fn-pic-get held-n c) (len held))
      (or (not (fn-pic-get incoming-desc c))
          (fn-pic-spanp (fn-pic-get incoming-desc c) (len incoming)))))
(local (defthm fn-pic-py-whole-value
 (equal (fn-pic-span-value '(0 0 0) x) x)
 :hints (("Goal" :in-theory (enable fn-pic-span-value fn-pic-at take nthcdr)))))
(local (defthm fn-pic-py-whole-span-is-valid
 (implies (natp n) (fn-pic-spanp '(0 0 0) n))
 :hints (("Goal" :in-theory (enable fn-pic-spanp fn-pic-at)))))
(local (defthm fn-pic-py-whole-span-length
 (implies (natp n) (equal (fn-pic-span-length '(0 0 0) n) n))
 :hints (("Goal" :in-theory (enable fn-pic-span-length fn-pic-at)))))
(local (defthm fn-pic-py-take-zero
 (equal (take 0 x) nil)
 :hints (("Goal" :in-theory (enable take)))))
(local (defthm fn-pic-py-source-result-is-valid
 (implies (fn-pic-source-result r n) (fn-pic-spanp (fn-pic-source-result r n) n))
 :hints (("Goal" :in-theory (e/d (fn-pic-source-result) (fn-pic-spanp fn-pic-at))))))
(local (defthm fn-pic-py-different-length-implies-different
 (implies (not (equal (len x) (len y))) (not (equal x y)))
 :rule-classes nil))
(local (defthm fn-pic-py-start-establishes-product-or-conflict
 (implies (and (fn-pic-payload-entryp c incoming held)
               (or (not (fn-pic-get held-desc c)) (fn-pic-spanp (fn-pic-get held-desc c) (len held))))
   (fn-pic-payload-outcomep (fn-pic-compare-start c) incoming held))
 :hints (("Goal" :use
 ((:instance fn-pic-py-different-length-implies-different
  (x (fn-pic-span-value (fn-pic-get incoming-desc c) incoming))
  (y (fn-pic-span-value (fn-pic-get held-desc c) held))))
 :in-theory (e/d (fn-pic-payload-entryp fn-pic-payload-productp
                    fn-pic-payload-outcomep fn-pic-compare-start fn-pic-finish)
  (fn-pic-at fn-pic-spanp fn-pic-span-value fn-pic-span-length nth take nthcdr update-nth))))))
(defthm fn-pic-feed-funded-establishes-exact-payload-product
 (implies (and (fn-pic-payload-entryp c incoming held)
               (equal (fn-pic-get phase c) :source-held))
   (let ((next (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
    (implies (or (equal (fn-pic-get phase next) :compare-incoming)
                 (and (equal (fn-pic-get phase next) :done) (equal (fn-pic-get result next) :conflict)))
      (fn-pic-payload-outcomep next incoming held))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-feed-funded fn-pic-feed fn-pic-finish fn-pic-payload-entryp)
  (fn-pic-at fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-pic-parser
   fn-psc-step fn-psc-result fn-pic-source-result fn-pic-compare-start
   fn-pic-payload-outcomep fn-pic-payload-productp fn-pic-spanp nth update-nth)))))
(defthm fn-pic-next-establishes-exact-payload-product
 (implies (and (fn-pic-payload-entryp c fn-octets held)
               (equal (fn-pic-get phase c) :source-held))
   (let ((next (mv-nth 1 (fn-pic-next c fuel fn-octets))))
    (implies (or (equal (fn-pic-get phase next) :compare-incoming)
                 (and (equal (fn-pic-get phase next) :done) (equal (fn-pic-get result next) :conflict)))
      (fn-pic-payload-outcomep next fn-octets held))))
 :rule-classes nil
 :hints (("Goal" :use
 ((:instance fn-pic-feed-funded-establishes-exact-payload-product
   (incoming fn-octets) (observation :control))
  (:instance fn-pic-feed-funded-establishes-exact-payload-product
   (incoming fn-octets) (fuel (- fuel 1))
   (observation (list :incoming-byte (fn-pic-get incoming-token c)
      (fn-pic-at 1 (fn-pic-demand c))
      (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets)))))
 :in-theory (e/d (fn-pic-next fn-pic-payload-entryp fn-pic-finish)
  (fn-pic-at fn-pic-feed-funded fn-pic-demand fn-pic-payload-outcomep
   fn-pic-payload-productp fn-pic-spanp fn-octets-get nth update-nth)))))
