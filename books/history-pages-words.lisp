; fn: octets and little-endian u64 words for the history's image (lane
; arena-store-2, 2026-09-28).  Prefix fn-hp-.
;
; The page store keeps a page as 2048 little-endian u64 words
; (`pgs-word-le-octets', books/pagestore-words-sha); the FNADTSN1 image is
; octets with little-endian cells (`adt-le', books/proto/adt-bytes-lib).
; This book is the bridge: a word's page-store octets are its `adt-le'
; octets, and packing octets into words (`fn-hp-pack8') is the inverse of
; `pgs-words-le-octets'.  Kept apart so its arithmetic (arithmetic-5) does
; not meet the other books' (arithmetic/top).
(in-package "ACL2")
(include-book "pagestore-words-sha")
(include-book "proto/adt-bytes-lib")
(local (include-book "arithmetic-5/top" :dir :system))

; A word's page-store octets are its adt-le octets.
(defthm fn-hp-word-le-octets-is-le
  (implies (natp x)
           (equal (pgs-word-le-octets x) (adt-le 8 x)))
  :hints (("Goal" :in-theory (enable fn-sha256-byte)
           :expand ((:free (y) (adt-le 8 y)) (:free (y) (adt-le 7 y)) (:free (y) (adt-le 6 y))
                    (:free (y) (adt-le 5 y)) (:free (y) (adt-le 4 y)) (:free (y) (adt-le 3 y))
                    (:free (y) (adt-le 2 y)) (:free (y) (adt-le 1 y)) (:free (y) (adt-le 0 y))))))

(defun fn-hp-pack8 (n b)
  ; the first 8N octets of B as N little-endian words
  (declare (xargs :guard (and (natp n) (true-listp b))))
  (if (zp n) nil (cons (adt-unle 8 b) (fn-hp-pack8 (1- n) (nthcdr 8 b)))))

(defthm fn-hp-len-pack8 (equal (len (fn-hp-pack8 n b)) (nfix n)))

(local
 (defun fn-hp-le-ind (w b)
   (if (zp w) (list w b) (fn-hp-le-ind (1- w) (cdr b)))))

(defthm fn-hp-le-unle
  (implies (and (natp w) (<= w (len b)) (adt-octetsp b))
           (equal (adt-le w (adt-unle w b)) (take w b)))
  :hints (("Goal" :induct (fn-hp-le-ind w b) :in-theory (enable take))))

(local
 (defthm fn-hp-octetsp-nthcdr
   (implies (adt-octetsp b) (adt-octetsp (nthcdr n b)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defun fn-hp-tk-ind (m b)
   (if (zp m) (list m b) (fn-hp-tk-ind (1- m) (cdr b)))))

(defthmd fn-hp-take-plus
  (implies (and (natp m) (natp k))
           (equal (take (+ m k) b) (append (take m b) (take k (nthcdr m b)))))
  :hints (("Goal" :induct (fn-hp-tk-ind m b) :in-theory (enable take nthcdr))))

(local
 (defthm fn-hp-len-nthcdr
   (implies (and (natp m) (<= m (len b))) (equal (len (nthcdr m b)) (- (len b) m)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local (defthm fn-hp-take-0 (equal (take 0 b) nil) :hints (("Goal" :in-theory (enable take)))))

(defthm fn-hp-words-le-octets-of-pack8
  (implies (and (natp n) (<= (* 8 n) (len b)) (adt-octetsp b))
           (equal (pgs-words-le-octets (fn-hp-pack8 n b)) (take (* 8 n) b)))
  :hints (("Goal" :induct (fn-hp-pack8 n b) :in-theory (disable pgs-word-le-octets take))
          ("Subgoal *1/2" :use ((:instance fn-hp-take-plus (m 8) (k (* 8 (+ -1 n))))))))

(local
 (defun fn-hp-pk-ind (j n b)
   (if (or (zp j) (zp n)) (list j n b) (fn-hp-pk-ind (1- j) (1- n) (nthcdr 8 b)))))

(defthm fn-hp-nthcdr-nthcdr
  (implies (and (natp m) (natp n))
           (equal (nthcdr m (nthcdr n b)) (nthcdr (+ m n) b)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm fn-hp-nth-pack8
  (implies (and (natp j) (< j (nfix n)))
           (equal (nth j (fn-hp-pack8 n b)) (adt-unle 8 (nthcdr (* 8 j) b))))
  :hints (("Goal" :induct (fn-hp-pk-ind j n b) :in-theory (enable nth)
           :expand ((fn-hp-pack8 n b)))))

(defthm fn-hp-nthcdr-pack8
  (implies (and (natp m) (<= m (nfix n)))
           (equal (nthcdr m (fn-hp-pack8 n b)) (fn-hp-pack8 (- (nfix n) m) (nthcdr (* 8 m) b))))
  :hints (("Goal" :induct (fn-hp-pk-ind m n b) :in-theory (enable nthcdr)
           :expand ((fn-hp-pack8 n b)))))

(defthm fn-hp-take-pack8
  (implies (and (natp m) (<= m (nfix n)))
           (equal (take m (fn-hp-pack8 n b)) (fn-hp-pack8 m b)))
  :hints (("Goal" :induct (fn-hp-pk-ind m n b) :in-theory (enable take)
           :expand ((fn-hp-pack8 n b) (fn-hp-pack8 m b)))))

; Page K of the words is page K of the octets.
(defthm fn-hp-page-words-of-pack8
  (implies (and (natp k) (natp e) (< k e) (adt-octetsp b) (equal (len b) (* 16384 e)))
           (equal (pgs-words-le-octets (take 2048 (nthcdr (* 2048 k) (fn-hp-pack8 (* 2048 e) b))))
                  (take 16384 (nthcdr (* 16384 k) b))))
  :hints (("Goal" :do-not-induct t)))

; Word alignment arithmetic (the pool entries are padded to 8 octets).
(defthm fn-hp-pad-to-8
  (implies (natp n) (equal (mod (+ n (mod (- 8 (mod n 8)) 8)) 8) 0)))

(defthm fn-hp-mod-8-sum
  (implies (and (natp x) (natp y) (equal (mod x 8) 0) (equal (mod y 8) 0))
           (equal (mod (+ x y) 8) 0)))

(defthm fn-hp-floor-8-exact
  (implies (and (natp x) (equal (mod x 8) 0))
           (equal (* 8 (floor x 8)) x)))

(defthm fn-hp-floor-8-plus
  (implies (and (natp x) (natp y) (equal (mod x 8) 0))
           (equal (floor (+ (* 16384 y) x) 8) (+ (* 2048 y) (floor x 8)))))
