; Proof-only resource carry for the actual bounded payload decoder.
; This book is not a selected-runtime allocation assumption or an admission
; claim.  In particular, guards alone permit corrupt, unbounded registers.
(in-package "ACL2")
(include-book "payload-window")

(defun fn-pzw-walk-widthp (code first index length)
  (declare (xargs :guard t))
  (and (integerp length) (<= 1 length) (<= length 15)
       (natp code) (<= code (- (expt 2 length) 2))
       (natp first) (<= first (* 65535 (- (expt 2 length) 2)))
       (natp index) (<= index (* 65535 (- length 1)))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm fn-pzw-walk-width-next
   (implies (and (fn-pzw-walk-widthp code first index length)
                 (< length 15) (natp count) (< count 65536)
                 (natp bit) (<= bit 1))
            (fn-pzw-walk-widthp (+ (* 2 code) (* 2 bit))
                                (+ (* 2 first) (* 2 count))
                                (+ index count) (+ 1 length)))
   :hints (("Goal" :in-theory (enable fn-pzw-walk-widthp)
                   :cases ((equal length 1) (equal length 2) (equal length 3) (equal length 4) (equal length 5) (equal length 6) (equal length 7) (equal length 8) (equal length 9) (equal length 10) (equal length 11) (equal length 12) (equal length 13) (equal length 14)))))

 (defthm fn-pzw-walk-width-reset
   (fn-pzw-walk-widthp 0 0 0 1))

 (defthm fn-pzw-walk-width-constraints
   (implies (fn-pzw-walk-widthp code first index length)
            (and (integerp length) (<= 1 length) (<= length 15)
                 (natp code) (natp first) (natp index)))
   :hints (("Goal" :in-theory (enable fn-pzw-walk-widthp)))
   :rule-classes :forward-chaining)

 (defthm fn-pzw-walk-width-scalars
   (implies (fn-pzw-walk-widthp code first index length)
            (and (<= code 32766) (<= first 2147319810)
                 (<= index 917490)))
   :hints (("Goal" :in-theory (enable fn-pzw-walk-widthp)
                   :cases ((equal length 1) (equal length 2) (equal length 3)
                           (equal length 4) (equal length 5) (equal length 6)
                           (equal length 7) (equal length 8) (equal length 9)
                           (equal length 10) (equal length 11) (equal length 12)
                           (equal length 13) (equal length 14) (equal length 15))))
   :rule-classes :forward-chaining)

)

 (defthm fn-pzw-actual-walk-width
   (implies (and (fn-pzw-walk-widthp code first index length)
                 (not (equal (mv-nth 0 (fn-zin-walk tb bits nbits code first index
                                                  length fn-zin-tab)) 2)))
            (let ((r (fn-zin-walk tb bits nbits code first index length fn-zin-tab)))
              (fn-pzw-walk-widthp (mv-nth 4 r) (mv-nth 5 r)
                                  (mv-nth 6 r) (mv-nth 7 r))))
   :hints (("Goal" :induct (fn-zin-walk tb bits nbits code first index length fn-zin-tab)
                   :in-theory (e/d (fn-zin-walk) (fn-pzw-walk-widthp fn-zin-tget$inline
                                                    fn-zin-bit$inline fn-zin-half$inline)))))

(defthm fn-pzw-actual-pull-nbits
  (implies (< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
           (<= (fn-zin-nbits (fn-zin-pull ip fn-zin-st fn-octets)) 39))
  :hints (("Goal" :in-theory (enable fn-zin-pull))))

(defthm fn-pzw-actual-walk-all-exit-scalars
  (implies (fn-pzw-walk-widthp code first index length)
           (let ((r (fn-zin-walk tb bits nbits code first index length fn-zin-tab)))
             (and (natp (mv-nth 4 r)) (<= (mv-nth 4 r) 32767)
                  (natp (mv-nth 5 r)) (<= (mv-nth 5 r) 2147319810)
                  (natp (mv-nth 6 r)) (<= (mv-nth 6 r) 917490)
                  (integerp (mv-nth 7 r))
                  (<= 1 (mv-nth 7 r)) (<= (mv-nth 7 r) 15))))
  :hints (("Goal" :induct (fn-zin-walk tb bits nbits code first index length fn-zin-tab)
                  :in-theory (e/d (fn-zin-walk) (fn-pzw-walk-widthp fn-zin-tget$inline
                                                fn-zin-bit$inline fn-zin-half$inline)))))

(defun fn-pzw-bits-widthp (bits nbits)
  (declare (xargs :guard t))
  (and (natp bits) (natp nbits) (< bits (expt 2 nbits))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm fn-pzw-actual-shift-in-width
   (implies (and (fn-pzw-bits-widthp bits nbits) (fn-cbor-octetp octet))
            (fn-pzw-bits-widthp (fn-zin-shift-in bits nbits octet) (+ 8 nbits)))
   :hints (("Goal" :in-theory (enable fn-pzw-bits-widthp fn-zin-shift-in
                                     fn-cbor-octetp)
                   :nonlinearp t)))

 (defthm fn-pzw-actual-highb-width
   (implies (and (fn-pzw-bits-widthp bits nbits) (natp n) (<= n nbits))
            (fn-pzw-bits-widthp (fn-zin-highb bits n) (- nbits n)))
   :hints (("Goal" :in-theory (enable fn-pzw-bits-widthp fn-zin-highb)
                   :nonlinearp t)))
)

(defun fn-pzw-state-bits-widthp (fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (and (<= (fn-zin-nbits fn-zin-st) 39)
       (fn-pzw-bits-widthp (fn-zin-bits fn-zin-st) (fn-zin-nbits fn-zin-st))))

(defthm fn-pzw-bits-width-constraints
  (implies (fn-pzw-bits-widthp bits nbits) (and (natp bits) (natp nbits)))
  :hints (("Goal" :in-theory (enable fn-pzw-bits-widthp)))
  :rule-classes :forward-chaining)

(defthm fn-pzw-half-width
  (implies (and (fn-pzw-bits-widthp bits nbits) (posp nbits))
           (fn-pzw-bits-widthp (fn-zin-half bits) (+ -1 nbits)))
  :hints (("Goal" :use ((:instance fn-pzw-actual-highb-width (n 1)))
                  :in-theory (e/d (fn-zin-half$inline fn-zin-highb)
                                  (fn-pzw-bits-widthp)))))

(defthm fn-pzw-actual-walk-bits-width
  (implies (fn-pzw-bits-widthp bits nbits)
           (let ((r (fn-zin-walk tb bits nbits code first index length fn-zin-tab)))
             (and (fn-pzw-bits-widthp (mv-nth 2 r) (mv-nth 3 r))
                  (<= (mv-nth 3 r) nbits))))
  :hints (("Goal" :induct (fn-zin-walk tb bits nbits code first index length fn-zin-tab)
                  :in-theory (e/d (fn-zin-walk zp)
                                  (fn-pzw-bits-widthp fn-zin-tget$inline
                                   fn-zin-bit$inline fn-zin-half$inline)))))

(defthm fn-pzw-actual-take-bits-width
  (implies (and (fn-pzw-state-bits-widthp fn-zin-st) (natp n)
                (<= n (fn-zin-nbits fn-zin-st)))
           (fn-pzw-state-bits-widthp (mv-nth 1 (fn-zin-take n fn-zin-st))))
  :hints (("Goal" :use ((:instance fn-pzw-actual-highb-width
                                   (bits (fn-zin-bits fn-zin-st))
                                   (nbits (fn-zin-nbits fn-zin-st))))
                  :in-theory (e/d (fn-pzw-state-bits-widthp fn-zin-take)
                                  (fn-pzw-bits-widthp fn-zin-lowb fn-zin-highb)))))

(defthm fn-pzw-actual-pull-bits-width
  (implies (and (fn-pzw-state-bits-widthp fn-zin-st)
                (< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
                (fn-cbor-octetp (fn-octets-get ip fn-octets)))
           (fn-pzw-state-bits-widthp (fn-zin-pull ip fn-zin-st fn-octets)))
  :hints (("Goal" :use ((:instance fn-pzw-actual-shift-in-width
                                   (bits (fn-zin-bits fn-zin-st))
                                   (nbits (fn-zin-nbits fn-zin-st))
                                   (octet (fn-octets-get ip fn-octets))))
                  :in-theory (e/d (fn-pzw-state-bits-widthp fn-zin-pull)
                                  (fn-pzw-bits-widthp fn-zin-shift-in)))))

(defthm fn-pzw-highb-width-ordered
  (implies (and (fn-pzw-bits-widthp bits nbits) (natp n) (<= n nbits))
           (fn-pzw-bits-widthp (fn-zin-highb bits n) (+ (- n) nbits)))
  :hints (("Goal" :use fn-pzw-actual-highb-width
                  :in-theory (disable fn-pzw-bits-widthp fn-zin-highb))))

(defthm fn-pzw-state-bits-width-set-other
  (implies (and (not (equal i 1)) (not (equal i 2)))
           (equal (fn-pzw-state-bits-widthp (fn-zin-set i value fn-zin-st))
                  (fn-pzw-state-bits-widthp fn-zin-st)))
  :hints (("Goal" :in-theory (enable fn-pzw-state-bits-widthp))))

(defthm fn-pzw-actual-walk-bits-resources
  (implies (fn-pzw-bits-widthp bits nbits)
           (let ((r (fn-zin-walk tb bits nbits code first index length fn-zin-tab)))
             (and (natp (mv-nth 2 r)) (natp (mv-nth 3 r))
                  (<= (mv-nth 3 r) nbits))))
  :hints (("Goal" :use fn-pzw-actual-walk-bits-width
                  :in-theory (disable fn-zin-walk fn-pzw-bits-widthp fn-pzw-actual-walk-bits-width)))
  :rule-classes
  ((:type-prescription :corollary
     (implies (fn-pzw-bits-widthp bits nbits)
              (natp (mv-nth 2 (fn-zin-walk tb bits nbits code first index length fn-zin-tab)))))
   (:type-prescription :corollary
     (implies (fn-pzw-bits-widthp bits nbits)
              (natp (mv-nth 3 (fn-zin-walk tb bits nbits code first index length fn-zin-tab)))))
   (:linear :corollary
     (implies (fn-pzw-bits-widthp bits nbits)
              (<= (mv-nth 3 (fn-zin-walk tb bits nbits code first index length fn-zin-tab))
                  nbits)))))

(defthm fn-pzw-actual-decode-bit-bits-width
  (implies (fn-pzw-state-bits-widthp fn-zin-st)
           (fn-pzw-state-bits-widthp
            (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab))))
  :hints (("Goal" :in-theory
           (e/d (fn-zin-decode-bit fn-pzw-state-bits-widthp)
                (fn-pzw-bits-widthp fn-zin-tget$inline fn-zin-lowb fn-zin-highb
                 fn-zin-walk)))))

(defthm fn-pzw-actual-lit-loop-bits-width
  (implies (fn-pzw-bits-widthp bits nbits)
           (let ((r (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)))
             (and (fn-pzw-bits-widthp (mv-nth 0 r) (mv-nth 1 r))
                  (<= (mv-nth 1 r) nbits))))
  :hints (("Goal" :induct
           (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
           :in-theory (e/d (fn-zin-lit-loop zp)
                           (fn-pzw-bits-widthp fn-zin-lowb fn-zin-highb fn-zin-tget$inline)))))

(defthm fn-pzw-actual-emit-bits-unchanged
  (equal (fn-pzw-state-bits-widthp (mv-nth 1 (fn-zin-emit octet fn-zin-st fn-zin-win fn-zin-out)))
         (fn-pzw-state-bits-widthp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-zin-emit) (fn-pzw-state-bits-widthp)))))

(defthm fn-pzw-actual-match-bits-unchanged
  (equal (fn-pzw-state-bits-widthp (mv-nth 1 (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out)))
         (fn-pzw-state-bits-widthp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-zin-match) (fn-pzw-state-bits-widthp fn-zin-copy)))))

(defthm fn-pzw-actual-lit-loop-bits-resources
  (implies (fn-pzw-bits-widthp bits nbits)
           (let ((r (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)))
             (and (natp (mv-nth 0 r)) (natp (mv-nth 1 r))
                  (<= (mv-nth 1 r) nbits))))
  :hints (("Goal" :use fn-pzw-actual-lit-loop-bits-width
                  :in-theory (disable fn-zin-lit-loop fn-pzw-bits-widthp
                                      fn-pzw-actual-lit-loop-bits-width)))
  :rule-classes
  ((:type-prescription :corollary
     (implies (fn-pzw-bits-widthp bits nbits)
              (natp (mv-nth 0 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)))))
   (:type-prescription :corollary
     (implies (fn-pzw-bits-widthp bits nbits)
              (natp (mv-nth 1 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)))))
   (:linear :corollary
     (implies (fn-pzw-bits-widthp bits nbits)
              (<= (mv-nth 1 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out))
                  nbits)))))

(defthm fn-pzw-actual-lits-bits-width
  (implies (fn-pzw-state-bits-widthp fn-zin-st)
           (fn-pzw-state-bits-widthp (mv-nth 1 (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :use ((:instance fn-pzw-actual-lit-loop-bits-width
                                (k room) (bits (fn-zin-bits fn-zin-st))
                                (nbits (fn-zin-nbits fn-zin-st))
                                (w (fn-zin-wpos fn-zin-st))
                                (tout (fn-zin-tout fn-zin-st))
                                (limit (fn-zin-bomb-limit fn-zin-st))))
           :in-theory
           (e/d (fn-zin-lits fn-pzw-state-bits-widthp)
                (fn-pzw-bits-widthp fn-zin-lit-loop fn-zin-bomb-limit
                 fn-pzw-actual-lit-loop-bits-width)))))

(defthm fn-pzw-take-nbits
  (equal (fn-zin-nbits (mv-nth 1 (fn-zin-take n fn-zin-st)))
         (nfix (- (fn-zin-nbits fn-zin-st) (nfix n))))
  :hints (("Goal" :in-theory (enable fn-zin-take))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pzw-lowb-no-increase
   (<= (fn-zin-lowb bits n) (nfix bits))
   :hints (("Goal" :in-theory (enable fn-zin-lowb)))
   :rule-classes :linear))

(defthm fn-pzw-actual-act-bits-width
  (implies (and (fn-pzw-state-bits-widthp fn-zin-st)
                (<= (fn-zin-need fn-zin-st) (fn-zin-nbits fn-zin-st)))
           (fn-pzw-state-bits-widthp
            (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :cases ((equal (fn-zin-mode fn-zin-st) 0)
                          (equal (fn-zin-mode fn-zin-st) 1)
                          (equal (fn-zin-mode fn-zin-st) 2)
                          (equal (fn-zin-mode fn-zin-st) 3)
                          (equal (fn-zin-mode fn-zin-st) 4)
                          (equal (fn-zin-mode fn-zin-st) 5)
                          (equal (fn-zin-mode fn-zin-st) 6)
                          (equal (fn-zin-mode fn-zin-st) 7)
                          (equal (fn-zin-mode fn-zin-st) 8)
                          (equal (fn-zin-mode fn-zin-st) 9)
                          (equal (fn-zin-mode fn-zin-st) 10)
                          (equal (fn-zin-mode fn-zin-st) 11)
                          (equal (fn-zin-mode fn-zin-st) 12)
                          (equal (fn-zin-mode fn-zin-st) 13))
                  :in-theory
                  (e/d (fn-zin-act fn-zin-need fn-zin-block-end fn-zin-decode-reset)
                       (fn-pzw-state-bits-widthp fn-pzw-bits-widthp fn-zin-take
                        fn-zin-decode-bit fn-zin-emit fn-zin-fill fn-zin-construct
                        fn-zin-fixed-tables fn-zin-dynamic-tables fn-zin-tget$inline)))))

(defthm fn-pzw-actual-step-bits-width
  (implies (and (fn-pzw-state-bits-widthp fn-zin-st)
                (<= (fn-zin-need fn-zin-st) (fn-zin-nbits fn-zin-st)))
           (fn-pzw-state-bits-widthp
            (mv-nth 1 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory
           (e/d (fn-zin-step)
                (fn-pzw-state-bits-widthp fn-zin-match fn-zin-lits fn-zin-act)))))

(defthm fn-pzw-actual-loop-bits-width
  (implies (and (fn-pzw-state-bits-widthp fn-zin-st)
                (fn-cbor-octet-listp fn-octets))
           (fn-pzw-state-bits-widthp
            (mv-nth 3 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :induct
           (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop fn-octets$a-get fn-cbor-octetp)
                           (fn-pzw-state-bits-widthp fn-zin-pull fn-zin-step nth)))))

(encapsulate
 ()
 (local
  (defthm fn-pzw-reset-loop-below
    (implies (and (natp i) (natp j) (< j i))
             (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st))
                    (fn-zin-fld j fn-zin-st)))
    :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
                    :in-theory (enable fn-zin-reset-loop)))))
 (local
  (defthm fn-pzw-reset-loop-fields
    (implies (and (natp i) (natp j) (<= i j) (< j 18))
             (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) 0))
    :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
                    :in-theory (enable fn-zin-reset-loop)))))

(defthm fn-pzw-actual-reset-bits-width
  (fn-pzw-state-bits-widthp (fn-zin-reset fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-zin-reset fn-zin-reset-loop
                                     fn-pzw-state-bits-widthp fn-pzw-bits-widthp))))

)

(defthm fn-pzw-actual-initialize-bits-width
  (fn-pzw-state-bits-widthp
   (mv-nth 0 (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  :hints (("Goal" :in-theory (e/d (fn-pzw-initialize)
                                  (fn-pzw-state-bits-widthp fn-zin-reset
                                   fn-zin-payload-ready)))))

(defthm fn-pzw-actual-feed-bits-width
  (implies (and (fn-pzw-state-bits-widthp fn-zin-st)
                (fn-cbor-octet-listp fn-octets))
           (fn-pzw-state-bits-widthp
            (mv-nth 3 (fn-zin-feed b fn-zin-st start end lim fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-zin-feed)
                                  (fn-pzw-state-bits-widthp fn-zin-loop)))))

(defthm fn-pzw-actual-chunk-bits-width
  (implies (and (fn-pzw-state-bits-widthp fn-zin-st)
                (fn-cbor-octet-listp fn-octets))
           (fn-pzw-state-bits-widthp
            (mv-nth 3 (fn-pzw-chunk requested remaining start end expected
                                  fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-chunk)
                                  (fn-pzw-state-bits-widthp fn-zin-feed)))))

(defthm fn-pzw-actual-stored-chunk-bits-width
  (implies (and (fn-pzw-state-bits-widthp fn-zin-st)
                (fn-cbor-octet-listp fn-octets))
           (fn-pzw-state-bits-widthp
            (mv-nth 3 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-stored-chunk)
                                  (fn-pzw-state-bits-widthp fn-pzw-chunk)))))

(encapsulate
 ()
 (local
  (defthm fn-pzw-loop-input-span
    (implies (and (natp start) (<= start end))
             (let ((ip (mv-nth 2 (fn-zin-loop b start end lim fn-zin-st fn-octets
                                            fn-zin-win fn-zin-tab fn-zin-out))))
               (and (natp ip) (<= start ip) (<= ip end))))
    :hints (("Goal" :induct (fn-zin-loop b start end lim fn-zin-st fn-octets
                                        fn-zin-win fn-zin-tab fn-zin-out)
                    :in-theory (e/d (fn-zin-loop) (fn-zin-pull fn-zin-step fn-zin-loop-counts))))))

 (local
  (defthm fn-pzw-feed-input-span
    (implies (and (natp start) (<= start end))
             (let ((ip (mv-nth 2 (fn-zin-feed b fn-zin-st start end lim fn-octets
                                            fn-zin-win fn-zin-tab fn-zin-out))))
               (and (natp ip) (<= start ip) (<= ip end))))
    :hints (("Goal" :in-theory (e/d (fn-zin-feed) (fn-zin-loop))))))

 (local
  (defthm fn-pzw-chunk-input-span
    (implies (and (natp start) (<= start end))
             (let ((ip (mv-nth 2 (fn-pzw-chunk requested remaining start end expected
                                            fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
               (and (natp ip) (<= start ip) (<= ip end))))
    :hints (("Goal" :in-theory (e/d (fn-pzw-chunk) (fn-zin-feed))))))

 (defthm fn-pzw-actual-stored-chunk-input-span
   (implies (and (natp start) (<= start end))
            (let ((ip (mv-nth 2 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                                  fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
              (and (natp ip) (<= start ip) (<= ip end))))
   :hints (("Goal" :in-theory (e/d (fn-pzw-stored-chunk) (fn-pzw-chunk)))))
)
