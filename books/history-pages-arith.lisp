; fn: floor and ceiling facts for the history's writer (lane arena-store-3,
; 2026-09-28).  Prefix fn-hp-.  Kept apart so arithmetic-5 does not meet
; the writer's arithmetic/top.
(in-package "ACL2")
(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-hp-floor-2048-mono
  (implies (and (natp a) (natp b) (<= a b)) (<= (floor a 2048) (floor b 2048)))
  :rule-classes :linear)

(defthm fn-hp-floor-2048-nat
  (implies (natp a) (natp (floor a 2048)))
  :rule-classes :type-prescription)

(defthm fn-hp-floor-block-lo
  (implies (and (natp base) (natp l))
           (equal (floor (+ (* 2048 base) (floor l 8)) 2048) (+ base (floor l 16384)))))

(local
 (defthm fn-hp-floor-le-quot
   (implies (and (rationalp x) (posp y)) (<= (* y (floor x y)) x))
   :rule-classes :linear))

(local
 (defthm fn-hp-ceiling-ge-quot
   (implies (and (rationalp x) (posp y)) (<= x (* y (ceiling x y))))
   :rule-classes :linear))

(defthm fn-hp-floor-block-hi
  (implies (and (natp base) (natp l) (natp d))
           (< (floor (+ (* 2048 base) (floor l 8) (floor d 8) -1) 2048)
              (+ base (ceiling (+ l d) 16384))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-floor-le-quot (x l) (y 8))
                 (:instance fn-hp-floor-le-quot (x d) (y 8))
                 (:instance fn-hp-floor-le-quot (x (+ (* 2048 base) (floor l 8) (floor d 8) -1)) (y 2048))
                 (:instance fn-hp-ceiling-ge-quot (x (+ l d)) (y 16384)))
           :in-theory (union-theories '(natp posp (:executable-counterpart posp) (:type-prescription floor) (:type-prescription ceiling)) (theory 'minimal-theory))))
  :rule-classes :linear)

(defthm fn-hp-ceiling-16384-upper
  (implies (natp l) (< (* 16384 (ceiling l 16384)) (+ l 16384)))
  :rule-classes :linear)

(defthm fn-hp-floor-16384-lower
  (implies (natp l) (< l (+ 16384 (* 16384 (floor l 16384)))))
  :rule-classes :linear)

(defthm fn-hp-floor-le-ceiling-16384
  (implies (and (natp l1) (natp l2) (<= l1 l2))
           (<= (floor l1 16384) (ceiling l2 16384)))
  :rule-classes :linear)
