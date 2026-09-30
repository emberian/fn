; Actual executor scalar-byte payload, refining the retained concrete page.
; This is a conditional visible-byte boundary, not durability or INITIAL.
(in-package "ACL2")
(include-book "history-image-effect-boundary")
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "arithmetic-5/lib/basic-ops/numerator-and-denominator" :dir :system))

(local (defthm fn-hpib-low-octet-by-definition
 (implies (integerp x) (equal (logand 255 x) (mod x 256)))
 :hints (("Goal" :use ((:instance logand-with-mask (mask 255) (size 8) (i x)))
  :in-theory (enable loghead)))))

(local (defthm fn-hpib-ash-zero-by-definition
 (equal (ash x 0) (ifix x))
 :hints (("Goal" :in-theory (enable ash)))))

(local (defthm fn-hpib-word-byte-is-model-octet
 (implies (and (natp b) (< b 8))
  (equal (logand 255 (ash (ifix w) (- (* 8 b))))
         (nth b (pgs-word-le-octets w))))
 :hints (("Goal" :do-not-induct t :cases ((equal b 0) (equal b 1) (equal b 2) (equal b 3)
                         (equal b 4) (equal b 5) (equal b 6) (equal b 7))
  :in-theory (e/d (pgs-word-le-octets pgs-octet nth) (ash logand mod floor commutativity-of-logand logand-with-mask))))))

(local (defthm fn-hpib-word-model-length
 (equal (len (pgs-word-le-octets w)) 8)
 :hints (("Goal" :in-theory (enable pgs-word-le-octets)))))

(local (defthm fn-hpib-nth-append
 (implies (natp i)
  (equal (nth i (append xs ys))
         (if (< i (len xs)) (nth i xs) (nth (- i (len xs)) ys))))
 :hints (("Goal" :induct (nth i xs) :in-theory (enable nth)))))

(local (defthm fn-hpib-serialized-word-position
 (implies (and (natp k) (< k (len ws)) (natp b) (< b 8))
  (equal (nth (+ (* 8 k) b) (pgs-words-le-octets ws))
         (nth b (pgs-word-le-octets (nth k ws)))))
 :hints (("Goal" :induct (nth k ws)
  :in-theory (e/d (pgs-words-le-octets nth)
   (pgs-word-le-octets pgs-words-le-octets-loop ash logand mod floor))))))

(local (defun fn-hpib-prefix-index-ind (j i k fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil :measure (nfix j)))
 (if (zp j) (list i k)
  (fn-hpib-prefix-index-ind (1- j) (+ 1 i) (1- k) fn-hpb))))

(local (defthm fn-hpib-prefix-index-is-concrete-word
 (implies (and (natp i) (natp j) (natp k) (< j k))
  (equal (nth j (fn-hpb-prefix-aux i k fn-hpb))
         (fn-hpb-wi (+ i j) fn-hpb)))
 :hints (("Goal" :induct (fn-hpib-prefix-index-ind j i k fn-hpb)
  :expand ((fn-hpb-prefix-aux i k fn-hpb))
  :in-theory (e/d (nth) (fn-hpb-prefix-aux fn-hpb-wi))))))

(local (defthm fn-hpib-prefix-length-is-used
 (implies (natp k) (equal (len (fn-hpb-prefix-aux i k fn-hpb)) k))
 :hints (("Goal" :induct (fn-hpb-prefix-aux i k fn-hpb)
  :in-theory (e/d (fn-hpb-prefix-aux) (fn-hpb-wi))))))

(local (defthm fn-hpib-full-page-word-is-prefix-word
 (implies (and (equal (fn-hpb-used fn-hpb) 2048) (natp k) (< k 2048))
  (equal (fn-hpb-word k fn-hpb) (mv :word (nth k (fn-hpb-prefix fn-hpb)))))
 :hints (("Goal" :use ((:instance fn-hpib-prefix-index-is-concrete-word (i 0) (j k) (k 2048)))
  :in-theory (e/d (fn-hpb-word fn-hpb-prefix)
   (fn-hpb-prefix-aux fn-hpb-wi fn-hpb-used nth))))))

(local (defthm fn-hpib-byte-position-coordinate
 (implies (and (natp i) (< i 16384))
  (and (natp (floor i 8)) (< (floor i 8) 2048)
       (natp (mod i 8)) (< (mod i 8) 8)
       (equal (+ (* 8 (floor i 8)) (mod i 8)) i)))
 :hints (("Goal" :in-theory (enable floor mod)))))

(local (defthm fn-hpib-full-page-prefix-length
 (implies (equal (fn-hpb-used fn-hpb) 2048)
  (equal (len (fn-hpb-prefix fn-hpb)) 2048))
 :hints (("Goal" :use ((:instance fn-hpib-prefix-length-is-used (i 0) (k 2048)))
  :in-theory (e/d (fn-hpb-prefix) (fn-hpb-prefix-aux fn-hpb-used))))))

(local (defthm fn-hpib-full-page-byte-is-model-octet
 (implies (and (equal (fn-hpb-used fn-hpb) 2048) (natp i) (< i 16384))
  (equal (logand 255 (ash (ifix (nth (floor i 8) (fn-hpb-prefix fn-hpb)))
                              (- (* 8 (mod i 8)))))
         (nth i (pgs-words-le-octets (fn-hpb-prefix fn-hpb)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-hpib-byte-position-coordinate
        (:instance fn-hpib-serialized-word-position (k (floor i 8)) (b (mod i 8))
                   (ws (fn-hpb-prefix fn-hpb)))
        (:instance fn-hpib-word-byte-is-model-octet (b (mod i 8))
                   (w (nth (floor i 8) (fn-hpb-prefix fn-hpb)))))
  :in-theory (disable fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-used pgs-words-le-octets
                     pgs-word-le-octets floor mod ash logand nth
                     fn-hpib-low-octet-by-definition fn-hpib-word-byte-is-model-octet
                     fn-hpib-serialized-word-position)))))

(defun fn-hpib-selected-prefix (selector fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (case selector (0 (fn-hpb-prefix fn-hpq0)) (1 (fn-hpb-prefix fn-hpq1))
  (2 (fn-hpb-prefix fn-hpq2)) (3 (fn-hpb-prefix fn-hpq3)) (otherwise (fn-hpb-prefix fn-hpb))))

(defun fn-hpib-page-byte-contextp (c effect stage ledger i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) :verify-guards nil))
 (let* ((plan (fn-hie-plan c effect stage ledger)) (selector (fn-omk-at 5 plan)))
  (and (equal (fn-omk-at 0 plan) :io) (equal (fn-omk-at 1 plan) :write)
       (natp selector) (< selector 5) (natp i) (< i 16384)
       (equal (fn-hpi-region-used selector fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) 2048))))

(defthm fn-hie-page-byte-refines-retained-page-serialization
 (implies (fn-hpib-page-byte-contextp c effect stage ledger i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (equal (fn-hie-page-byte c effect stage ledger i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
   (mv :octet
    (nth i (pgs-words-le-octets
     (fn-hpib-selected-prefix (fn-omk-at 5 (fn-hie-plan c effect stage ledger))
       fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpib-byte-position-coordinate)
  :in-theory (e/d (fn-hie-page-byte fn-hpib-page-byte-contextp fn-hpib-selected-prefix
                  fn-hpi-region-used)
   (fn-hie-plan fn-omk-at fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-word fn-hpb-used fn-hpb-wi
    pgs-words-le-octets pgs-word-le-octets floor mod ash logand nth
    fn-hpib-low-octet-by-definition ifix)))))
