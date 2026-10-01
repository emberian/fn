; Continuation of PRF-1132. Proof-only actual register carry, no runtime
; allocator assumption and no whole-state validation in the served path.
(in-package "ACL2")
(include-book "payload-window-width")

(defun fn-pzw-state-walk-widthp (fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (fn-pzw-walk-widthp (fn-zin-dcode fn-zin-st) (fn-zin-dfirst fn-zin-st)
                      (fn-zin-dindex fn-zin-st) (fn-zin-dlen fn-zin-st)))

(defthm fn-pzw-state-walk-width-set-other
  (implies (and (not (equal i 8)) (not (equal i 9))
                (not (equal i 10)) (not (equal i 11)))
           (equal (fn-pzw-state-walk-widthp (fn-zin-set i value fn-zin-st))
                  (fn-pzw-state-walk-widthp fn-zin-st)))
  :hints (("Goal" :in-theory (enable fn-pzw-state-walk-widthp))))

(defthm fn-pzw-actual-decode-bit-walk-width
  (implies (and (fn-pzw-state-walk-widthp fn-zin-st)
                (not (equal (mv-nth 0 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab)) 2)))
           (fn-pzw-state-walk-widthp
            (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab))))
  :hints (("Goal" :use ((:instance fn-pzw-actual-walk-width
                         (bits (fn-zin-bits fn-zin-st))
                         (nbits (fn-zin-nbits fn-zin-st))
                         (code (fn-zin-dcode fn-zin-st))
                         (first (fn-zin-dfirst fn-zin-st))
                         (index (fn-zin-dindex fn-zin-st))
                         (length (fn-zin-dlen fn-zin-st))))
                  :in-theory
                  (e/d (fn-pzw-state-walk-widthp fn-zin-decode-bit)
                       (fn-pzw-walk-widthp fn-zin-walk fn-zin-tget$inline
                        fn-pzw-actual-walk-width fn-zin-lowb fn-zin-highb)))))

(defthm fn-pzw-actual-decode-reset-walk-width
  (fn-pzw-state-walk-widthp (fn-zin-decode-reset fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-pzw-state-walk-widthp fn-zin-decode-reset))))

(defthm fn-pzw-actual-emit-walk-unchanged
  (equal (fn-pzw-state-walk-widthp (mv-nth 1 (fn-zin-emit octet fn-zin-st fn-zin-win fn-zin-out)))
         (fn-pzw-state-walk-widthp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-zin-emit) (fn-pzw-state-walk-widthp)))))

(defthm fn-pzw-actual-match-walk-unchanged
  (equal (fn-pzw-state-walk-widthp (mv-nth 1 (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out)))
         (fn-pzw-state-walk-widthp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-zin-match) (fn-pzw-state-walk-widthp fn-zin-copy)))))

(defthm fn-pzw-actual-lits-walk-unchanged
  (equal (fn-pzw-state-walk-widthp (mv-nth 1 (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
         (fn-pzw-state-walk-widthp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-zin-lits) (fn-pzw-state-walk-widthp fn-zin-lit-loop)))))

(defthm fn-pzw-actual-take-walk-unchanged
  (equal (fn-pzw-state-walk-widthp (mv-nth 1 (fn-zin-take n fn-zin-st)))
         (fn-pzw-state-walk-widthp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-zin-take) (fn-pzw-state-walk-widthp)))))

(defthm fn-pzw-actual-act-walk-width
  (implies (and (fn-pzw-state-walk-widthp fn-zin-st)
                (not (equal (mv-nth 0 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)) :bad-code)))
           (fn-pzw-state-walk-widthp
            (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory
           (e/d (fn-zin-act fn-zin-block-end)
                (fn-pzw-state-walk-widthp fn-zin-take fn-zin-decode-bit
                 fn-zin-decode-reset fn-zin-emit fn-zin-fill fn-zin-construct
                 fn-zin-fixed-tables fn-zin-dynamic-tables fn-zin-tget$inline)))))

(defthm fn-pzw-actual-step-walk-width
  (implies (and (fn-pzw-state-walk-widthp fn-zin-st)
                (not (equal (mv-nth 0 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)) :bad-code)))
           (fn-pzw-state-walk-widthp
            (mv-nth 1 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory
           (e/d (fn-zin-step)
                (fn-pzw-state-walk-widthp fn-zin-match fn-zin-lits fn-zin-act)))))

(defthm fn-pzw-actual-pull-walk-unchanged
  (equal (fn-pzw-state-walk-widthp (fn-zin-pull ip fn-zin-st fn-octets))
         (fn-pzw-state-walk-widthp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-zin-pull) (fn-pzw-state-walk-widthp)))))

(defthm fn-pzw-actual-loop-walk-width
  (implies (and (fn-pzw-state-walk-widthp fn-zin-st)
                (not (equal (mv-nth 0 (fn-zin-loop b ip end lim fn-zin-st fn-octets
                                                 fn-zin-win fn-zin-tab fn-zin-out)) '(:refused :bad-code))))
           (fn-pzw-state-walk-widthp
            (mv-nth 3 (fn-zin-loop b ip end lim fn-zin-st fn-octets
                                  fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets
                                      fn-zin-win fn-zin-tab fn-zin-out)
                  :in-theory (e/d (fn-zin-loop)
                                  (fn-pzw-state-walk-widthp fn-zin-pull fn-zin-step)))))

(encapsulate
 ()
 (local
  (defthm fn-pzw-register-reset-loop-below
    (implies (and (natp i) (natp j) (< j i))
             (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st))
                    (fn-zin-fld j fn-zin-st)))
    :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
                    :in-theory (enable fn-zin-reset-loop)))))
 (local
  (defthm fn-pzw-register-reset-loop-fields
    (implies (and (natp i) (natp j) (<= i j) (< j 18))
             (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) 0))
    :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
                    :in-theory (enable fn-zin-reset-loop)))))
 (defthm fn-pzw-actual-reset-walk-width
   (fn-pzw-state-walk-widthp (fn-zin-reset fn-zin-st))
   :hints (("Goal" :in-theory (enable fn-zin-reset fn-pzw-state-walk-widthp)))))

(defthm fn-pzw-actual-initialize-walk-width
  (fn-pzw-state-walk-widthp
   (mv-nth 0 (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  :hints (("Goal" :in-theory (e/d (fn-pzw-initialize)
                                  (fn-pzw-state-walk-widthp fn-zin-reset fn-zin-payload-ready)))))

(defthm fn-pzw-actual-feed-walk-width
  (implies (and (fn-pzw-state-walk-widthp fn-zin-st)
                (not (equal (mv-nth 0 (fn-zin-feed b fn-zin-st start end lim fn-octets
                                                 fn-zin-win fn-zin-tab fn-zin-out)) '(:refused :bad-code))))
           (fn-pzw-state-walk-widthp
            (mv-nth 3 (fn-zin-feed b fn-zin-st start end lim fn-octets
                                  fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-zin-feed)
                                  (fn-pzw-state-walk-widthp fn-zin-loop)))))

(defthm fn-pzw-actual-chunk-walk-width
  (implies (and (fn-pzw-state-walk-widthp fn-zin-st)
                (not (equal (mv-nth 0 (fn-pzw-chunk requested remaining start end expected
                                                  fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) '(:refused :bad-code))))
           (fn-pzw-state-walk-widthp
            (mv-nth 3 (fn-pzw-chunk requested remaining start end expected
                                  fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-chunk)
                                  (fn-pzw-state-walk-widthp fn-zin-feed)))))

(defthm fn-pzw-actual-stored-chunk-walk-width
  (implies (and (fn-pzw-state-walk-widthp fn-zin-st)
                (not (equal (mv-nth 0 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) '(:refused :bad-code))))
           (fn-pzw-state-walk-widthp
            (mv-nth 3 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-stored-chunk)
                                  (fn-pzw-state-walk-widthp fn-pzw-chunk)))))

(defun fn-pzw-state-walk-scalarp (fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (and (<= (fn-zin-dcode fn-zin-st) 32767)
       (<= (fn-zin-dfirst fn-zin-st) 2147319810)
       (<= (fn-zin-dindex fn-zin-st) 917490)
       (<= 1 (fn-zin-dlen fn-zin-st)) (<= (fn-zin-dlen fn-zin-st) 15)))

(defthm fn-pzw-state-walk-width-implies-scalars
  (implies (fn-pzw-state-walk-widthp fn-zin-st)
           (fn-pzw-state-walk-scalarp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-pzw-state-walk-scalarp fn-pzw-state-walk-widthp)
                                  (fn-pzw-walk-widthp)))))

(defthm fn-pzw-state-walk-scalars-set-other
  (implies (and (not (equal i 8)) (not (equal i 9))
                (not (equal i 10)) (not (equal i 11)))
           (equal (fn-pzw-state-walk-scalarp (fn-zin-set i value fn-zin-st))
                  (fn-pzw-state-walk-scalarp fn-zin-st)))
  :hints (("Goal" :in-theory (enable fn-pzw-state-walk-scalarp))))

(defthm fn-pzw-actual-decode-bit-walk-scalars
  (implies (fn-pzw-state-walk-widthp fn-zin-st)
           (fn-pzw-state-walk-scalarp
            (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab))))
  :hints (("Goal" :use ((:instance fn-pzw-actual-walk-all-exit-scalars
                         (bits (fn-zin-bits fn-zin-st))
                         (nbits (fn-zin-nbits fn-zin-st))
                         (code (fn-zin-dcode fn-zin-st))
                         (first (fn-zin-dfirst fn-zin-st))
                         (index (fn-zin-dindex fn-zin-st))
                         (length (fn-zin-dlen fn-zin-st))))
                  :in-theory
                  (e/d (fn-pzw-state-walk-scalarp fn-pzw-state-walk-widthp fn-zin-decode-bit)
                       (fn-pzw-walk-widthp fn-zin-walk fn-zin-tget$inline
                        fn-pzw-actual-walk-all-exit-scalars fn-zin-lowb fn-zin-highb)))))

(defthm fn-pzw-actual-emit-walk-scalars-unchanged
  (equal (fn-pzw-state-walk-scalarp (mv-nth 1 (fn-zin-emit octet fn-zin-st fn-zin-win fn-zin-out)))
         (fn-pzw-state-walk-scalarp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-zin-emit) (fn-pzw-state-walk-scalarp)))))

(defthm fn-pzw-actual-take-walk-scalars-unchanged
  (equal (fn-pzw-state-walk-scalarp (mv-nth 1 (fn-zin-take n fn-zin-st)))
         (fn-pzw-state-walk-scalarp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-zin-take) (fn-pzw-state-walk-scalarp)))))

(defthm fn-pzw-actual-act-all-exit-walk-scalars
  (implies (fn-pzw-state-walk-widthp fn-zin-st)
           (fn-pzw-state-walk-scalarp
            (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory
           (e/d (fn-zin-act fn-zin-block-end)
                (fn-pzw-state-walk-scalarp fn-pzw-state-walk-widthp
                 fn-zin-take fn-zin-decode-bit fn-zin-decode-reset fn-zin-emit fn-zin-fill fn-zin-construct
                 fn-zin-fixed-tables fn-zin-dynamic-tables fn-zin-tget$inline)))))

(defthm fn-pzw-actual-step-all-exit-walk-scalars
  (implies (fn-pzw-state-walk-widthp fn-zin-st)
           (fn-pzw-state-walk-scalarp
            (mv-nth 1 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory
           (e/d (fn-zin-step)
                (fn-pzw-state-walk-scalarp fn-pzw-state-walk-widthp fn-zin-match fn-zin-lits fn-zin-act)))))

(defthm fn-pzw-actual-loop-all-exit-walk-scalars
  (implies (fn-pzw-state-walk-widthp fn-zin-st)
           (fn-pzw-state-walk-scalarp
            (mv-nth 3 (fn-zin-loop b ip end lim fn-zin-st fn-octets
                                  fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets
                                      fn-zin-win fn-zin-tab fn-zin-out)
                  :in-theory (e/d (fn-zin-loop)
                                  (fn-pzw-state-walk-scalarp fn-pzw-state-walk-widthp
                                   fn-zin-pull fn-zin-step)))))

(defthm fn-pzw-actual-feed-all-exit-walk-scalars
  (implies (fn-pzw-state-walk-widthp fn-zin-st)
           (fn-pzw-state-walk-scalarp
            (mv-nth 3 (fn-zin-feed b fn-zin-st start end lim fn-octets
                                  fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-zin-feed)
                                  (fn-pzw-state-walk-scalarp fn-pzw-state-walk-widthp fn-zin-loop)))))

(defthm fn-pzw-actual-chunk-all-exit-walk-scalars
  (implies (fn-pzw-state-walk-widthp fn-zin-st)
           (fn-pzw-state-walk-scalarp
            (mv-nth 3 (fn-pzw-chunk requested remaining start end expected
                                  fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-chunk)
                                  (fn-pzw-state-walk-scalarp fn-pzw-state-walk-widthp fn-zin-feed)))))

(defthm fn-pzw-actual-stored-chunk-all-exit-walk-scalars
  (implies (fn-pzw-state-walk-widthp fn-zin-st)
           (fn-pzw-state-walk-scalarp
            (mv-nth 3 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-stored-chunk)
                                  (fn-pzw-state-walk-scalarp fn-pzw-state-walk-widthp fn-pzw-chunk)))))

(defun fn-pzw-state-header-widthp (fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (and (<= (fn-zin-mode fn-zin-st) 13)
       (<= (fn-zin-n fn-zin-st) 65535)
       (<= (fn-zin-dist fn-zin-st) 32768)
       (< (fn-zin-wpos fn-zin-st) 32768)
       (<= (fn-zin-final fn-zin-st) 1)
       (<= (fn-zin-sym fn-zin-st) 65535)
       (<= (fn-zin-hlit fn-zin-st) 286)
       (<= (fn-zin-hdist fn-zin-st) 30)
       (<= (fn-zin-hclen fn-zin-st) 19)
       (<= (fn-zin-idx fn-zin-st) 316)
       (<= (fn-zin-preset fn-zin-st) 32768)
       (<= (fn-zin-fld 19 fn-zin-st) 1)))

(defthm fn-pzw-actual-walk-symbol-width
  (implies (fn-cbor-octet-listp fn-zin-tab)
           (< (mv-nth 1 (fn-zin-walk tb bits nbits code first index length fn-zin-tab))
              65536))
  :hints (("Goal" :induct (fn-zin-walk tb bits nbits code first index length fn-zin-tab)
                  :in-theory (e/d (fn-zin-walk)
                                  (fn-zin-tget$inline fn-zin-bit$inline fn-zin-half$inline))))
  :rule-classes :linear)

(defthm fn-pzw-actual-decode-bit-symbol-width
  (implies (fn-cbor-octet-listp fn-zin-tab)
           (< (mv-nth 1 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab)) 65536))
  :hints (("Goal" :in-theory (e/d (fn-zin-decode-bit)
                                  (fn-zin-walk fn-zin-tget$inline fn-zin-lowb fn-zin-highb))))
  :rule-classes :linear)

(defthm fn-pzw-header-take-unchanged
  (equal (fn-pzw-state-header-widthp (mv-nth 1 (fn-zin-take n fn-zin-st)))
         (fn-pzw-state-header-widthp fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-pzw-state-header-widthp fn-zin-take))))

(defthm fn-pzw-header-decode-bit-unchanged
  (equal (fn-pzw-state-header-widthp (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab)))
         (fn-pzw-state-header-widthp fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-pzw-state-header-widthp fn-zin-decode-bit)
                                  (fn-zin-walk fn-zin-tget$inline fn-zin-lowb fn-zin-highb)))))

(defthm fn-pzw-header-decode-reset-unchanged
  (equal (fn-pzw-state-header-widthp (fn-zin-decode-reset fn-zin-st))
         (fn-pzw-state-header-widthp fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-pzw-state-header-widthp fn-zin-decode-reset))))

(defthm fn-pzw-header-emit-width
  (implies (fn-pzw-state-header-widthp fn-zin-st)
           (fn-pzw-state-header-widthp
            (mv-nth 1 (fn-zin-emit octet fn-zin-st fn-zin-win fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-state-header-widthp fn-zin-emit)
                                  (fn-zin-wrap fn-zin-bomb-limit)))))

(defthm fn-pzw-take-other-fields
  (implies (and (not (equal (nfix i) 1)) (not (equal (nfix i) 2)))
           (equal (fn-zin-fld i (mv-nth 1 (fn-zin-take n fn-zin-st)))
                  (fn-zin-fld i fn-zin-st)))
  :hints (("Goal" :in-theory (enable fn-zin-take))))

(defthm fn-pzw-decode-bit-other-fields
  (implies (not (member-equal (nfix i) '(1 2 8 9 10 11)))
           (equal (fn-zin-fld i (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab)))
                  (fn-zin-fld i fn-zin-st)))
  :hints (("Goal" :in-theory (e/d (fn-zin-decode-bit)
                                  (fn-zin-walk fn-zin-tget$inline fn-zin-lowb fn-zin-highb)))))

(defthm fn-pzw-decode-reset-other-fields
  (implies (not (member-equal (nfix i) '(8 9 10 11)))
           (equal (fn-zin-fld i (fn-zin-decode-reset fn-zin-st))
                  (fn-zin-fld i fn-zin-st)))
  :hints (("Goal" :in-theory (enable fn-zin-decode-reset))))

(defthm fn-pzw-emit-other-fields
  (implies (not (member-equal (nfix i) '(5 6)))
           (equal (fn-zin-fld i (mv-nth 1 (fn-zin-emit octet fn-zin-st fn-zin-win fn-zin-out)))
                  (fn-zin-fld i fn-zin-st)))
  :hints (("Goal" :in-theory (e/d (fn-zin-emit)
                                  (fn-zin-wrap fn-zin-bomb-limit)))))

(defthm fn-pzw-emit-history-position
  (and (natp (fn-zin-wpos (mv-nth 1 (fn-zin-emit octet fn-zin-st fn-zin-win fn-zin-out))))
       (implies (< (fn-zin-wpos fn-zin-st) 32768)
                (< (fn-zin-wpos (mv-nth 1 (fn-zin-emit octet fn-zin-st fn-zin-win fn-zin-out)))
                   32768)))
  :hints (("Goal" :in-theory (e/d (fn-zin-emit) (fn-zin-wrap fn-zin-bomb-limit)))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pzw-take-small-extra
   (implies (and (natp n) (<= n 5))
            (< (mv-nth 0 (fn-zin-take n fn-zin-st)) 32))
   :hints (("Goal" :use fn-zin-take-bound
                   :in-theory (disable fn-zin-take)
                   :nonlinearp t))
   :rule-classes :linear))

(defthm fn-pzw-take-length-extra-bound
  (< (mv-nth 0 (fn-zin-take (fn-zin-lext-of sym) fn-zin-st)) 32)
  :hints (("Goal" :use ((:instance fn-pzw-take-small-extra
                          (n (fn-zin-lext-of sym)))
                        (:instance fn-zin-lext-of-bounds (i sym)))
                  :in-theory (disable fn-zin-take fn-pzw-take-small-extra)))
  :rule-classes :linear)

(defthm fn-pzw-length-plus-extra-bound
  (< (+ (fn-zin-lbase-of sym)
        (mv-nth 0 (fn-zin-take (fn-zin-lext-of sym) fn-zin-st))) 290)
  :hints (("Goal" :use ((:instance fn-pzw-take-length-extra-bound)
                        (:instance fn-zin-lbase-of-bounds (i sym)))
                  :in-theory (disable fn-zin-take fn-pzw-take-length-extra-bound)))
  :rule-classes :linear)

(defthm fn-pzw-actual-act-header-width
  (implies (and (fn-pzw-state-header-widthp fn-zin-st)
                (fn-cbor-octet-listp fn-zin-tab))
           (fn-pzw-state-header-widthp
            (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :use ((:instance fn-pzw-length-plus-extra-bound
                                       (sym (fn-zin-sym fn-zin-st))))
                  :cases ((equal (fn-zin-mode fn-zin-st) 0)
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
                  (e/d (fn-pzw-state-header-widthp fn-zin-act fn-zin-block-end)
                       (fn-zin-take fn-zin-decode-bit fn-zin-emit fn-zin-decode-reset
                        fn-pzw-length-plus-extra-bound
                        fn-zin-fill fn-zin-construct fn-zin-fixed-tables
                        fn-zin-dynamic-tables fn-zin-tget$inline)))))

(defthm fn-pzw-actual-copy-history-position
  (< (car (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)) 32768)
  :hints (("Goal" :induct (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)
                  :in-theory (e/d (fn-zin-copy) (fn-zin-source fn-zin-wrap))))
  :rule-classes (:rewrite :linear))

(defthm fn-pzw-header-match-width
  (implies (fn-pzw-state-header-widthp fn-zin-st)
           (fn-pzw-state-header-widthp
            (mv-nth 1 (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-state-header-widthp fn-zin-match)
                                  (fn-zin-copy fn-zin-bomb-limit)))))

(defthm fn-pzw-actual-lit-loop-history-position
  (implies (< w 32768)
           (< (mv-nth 2 (fn-zin-lit-loop k bits nbits w tout limit
                                       fn-zin-tab fn-zin-win fn-zin-out)) 32768))
  :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit
                                         fn-zin-tab fn-zin-win fn-zin-out)
                  :in-theory (e/d (fn-zin-lit-loop)
                                  (fn-zin-wrap fn-zin-tget$inline fn-zin-lowb fn-zin-highb))))
  :rule-classes (:rewrite :linear))

(defthm fn-pzw-header-lits-width
  (implies (fn-pzw-state-header-widthp fn-zin-st)
           (fn-pzw-state-header-widthp
            (mv-nth 1 (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-state-header-widthp fn-zin-lits)
                                  (fn-zin-lit-loop fn-zin-bomb-limit)))))

(defthm fn-pzw-actual-step-header-width
  (implies (and (fn-pzw-state-header-widthp fn-zin-st)
                (fn-cbor-octet-listp fn-zin-tab))
           (fn-pzw-state-header-widthp
            (mv-nth 1 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-zin-step)
                                  (fn-pzw-state-header-widthp fn-zin-match fn-zin-lits fn-zin-act)))))

(defthm fn-pzw-header-pull-unchanged
  (equal (fn-pzw-state-header-widthp (fn-zin-pull ip fn-zin-st fn-octets))
         (fn-pzw-state-header-widthp fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-pzw-state-header-widthp fn-zin-pull))))

(defthm fn-pzw-header-set-input-count
  (equal (fn-pzw-state-header-widthp (fn-zin-set 7 value fn-zin-st))
         (fn-pzw-state-header-widthp fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-pzw-state-header-widthp))))

(defthm fn-pzw-actual-act-table-width
  (implies (and (fn-cbor-octet-listp fn-zin-tab)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp
                 (mv-nth 3 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                (equal (len (mv-nth 3 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                       *fn-zin-tab-octets*)))
  :hints (("Goal" :in-theory (e/d (fn-zin-act fn-zin-block-end)
                                  (fn-zin-take fn-zin-decode-bit fn-zin-emit fn-zin-decode-reset
                                   fn-zin-fill fn-zin-construct fn-zin-fixed-tables
                                   fn-zin-dynamic-tables fn-zin-tget$inline)))))

(defthm fn-pzw-actual-step-table-width
  (implies (and (fn-cbor-octet-listp fn-zin-tab)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp
                 (mv-nth 3 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                (equal (len (mv-nth 3 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                       *fn-zin-tab-octets*)))
  :hints (("Goal" :in-theory (e/d (fn-zin-step)
                                  (fn-zin-match fn-zin-lits fn-zin-act)))))

(defthm fn-pzw-actual-loop-header-width
  (implies (and (fn-pzw-state-header-widthp fn-zin-st)
                (fn-cbor-octet-listp fn-zin-tab)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (fn-pzw-state-header-widthp
            (mv-nth 3 (fn-zin-loop b ip end lim fn-zin-st fn-octets
                                  fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets
                                      fn-zin-win fn-zin-tab fn-zin-out)
                  :in-theory (e/d (fn-zin-loop)
                                  (fn-pzw-state-header-widthp fn-zin-pull fn-zin-step)))))

(defthm fn-pzw-actual-feed-header-width
  (implies (and (fn-pzw-state-header-widthp fn-zin-st)
                (fn-cbor-octet-listp fn-zin-tab)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (fn-pzw-state-header-widthp
            (mv-nth 3 (fn-zin-feed b fn-zin-st start end lim fn-octets
                                  fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-zin-feed)
                                  (fn-pzw-state-header-widthp fn-zin-loop)))))

(defthm fn-pzw-actual-chunk-header-width
  (implies (and (fn-pzw-state-header-widthp fn-zin-st)
                (fn-cbor-octet-listp fn-zin-tab)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (fn-pzw-state-header-widthp
            (mv-nth 3 (fn-pzw-chunk requested remaining start end expected
                                  fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-chunk)
                                  (fn-pzw-state-header-widthp fn-zin-feed)))))

(defthm fn-pzw-actual-stored-chunk-header-width-unfolds
  (implies (and (fn-pzw-state-header-widthp fn-zin-st)
                (fn-cbor-octet-listp fn-zin-tab)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (fn-pzw-state-header-widthp
            (mv-nth 3 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-stored-chunk)
                                  (fn-pzw-state-header-widthp fn-pzw-chunk)))))

(defthm fn-pzw-actual-payload-ready-preset
  (equal (car (fn-zin-payload-ready dict fn-zin-win fn-zin-tab))
         (min (len dict) 32768))
  :hints (("Goal" :in-theory
          (e/d (fn-zin-payload-ready)
               (fn-oct-back-copy (:e fn-oct-back-copy)
                fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet
                fn-zin-win-append-list fn-zin-win-append-back
                fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet
                fn-zin-tab-append-back nthcdr
                (:e fn-zin-win-clear) (:e fn-zin-win-reserve)
                (:e fn-zin-win-append-octet) (:e fn-zin-win-append-list)
                (:e fn-zin-win-append-back) (:e fn-zin-tab-clear)
                (:e fn-zin-tab-reserve) (:e fn-zin-tab-append-octet)
                (:e fn-zin-tab-append-back))))))

(encapsulate
 ()
 (local
  (defthm fn-pzw-register-reset-loop-below
    (implies (and (natp i) (natp j) (< j i))
             (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st))
                    (fn-zin-fld j fn-zin-st)))
    :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
                    :in-theory (enable fn-zin-reset-loop)))))
 (local
  (defthm fn-pzw-register-reset-loop-fields
    (implies (and (natp i) (natp j) (<= i j) (< j 18))
             (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) 0))
    :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
                    :in-theory (enable fn-zin-reset-loop)))))
 (defthm fn-pzw-actual-initialize-header-width
   (fn-pzw-state-header-widthp
    (mv-nth 0 (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   :hints (("Goal" :in-theory
            (e/d (fn-pzw-initialize fn-pzw-state-header-widthp fn-zin-reset)
                 (fn-zin-reset-loop fn-zin-payload-ready
                  fn-oct-back-copy (:e fn-oct-back-copy)))))))

; The representation component is captured/carry-proved, not recomputed by
; scanning the fixed table at each served action. Octet contents and exact
; physical length are one table representation boundary.
(defun-nx fn-pzw-table-representationp (table)
  (and (fn-cbor-octet-listp table)
       (equal (len table) *fn-zin-tab-octets*)))

(defthm fn-pzw-actual-stored-chunk-header-representation
  (implies (and (fn-pzw-state-header-widthp fn-zin-st)
                (fn-pzw-table-representationp fn-zin-tab))
           (fn-pzw-state-header-widthp
            (mv-nth 3 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :in-theory
           (e/d (fn-pzw-stored-chunk fn-pzw-table-representationp)
                (fn-pzw-state-header-widthp fn-pzw-chunk
                 fn-pzw-actual-stored-chunk-header-width-unfolds)))))
