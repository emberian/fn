; PRF-1132 continuation. Actual internal decoder profile-counter carry.
; The byte-source controller supplies the initial unread-span premise.
; This book proves source arithmetic widths, not compiler allocation costs.
(in-package "ACL2")
(include-book "payload-window-register-width")

(defun fn-pzw-profile-carryp (compressed expected ip end lim fn-zin-st fn-zin-out)
  (declare (xargs :stobjs (fn-zin-st fn-zin-out) :guard t))
  (and (natp compressed) (natp expected) (natp ip) (natp end) (<= ip end)
       (<= (+ (fn-zin-tin fn-zin-st) (- end ip)) (* 2 compressed))
       (<= (+ (fn-zin-tout fn-zin-st)
              (nfix (- (nfix lim) (fn-zin-out-len fn-zin-out))))
           (+ 1 expected))))

(defthm fn-pzw-actual-pull-profile-carry
  (implies (and (fn-pzw-profile-carryp compressed expected ip end lim fn-zin-st fn-zin-out)
                (< ip end))
           (fn-pzw-profile-carryp compressed expected (+ 1 ip) end lim
                                  (fn-zin-pull ip fn-zin-st fn-octets) fn-zin-out))
  :hints (("Goal" :in-theory (enable fn-pzw-profile-carryp fn-zin-pull))))

(defthm fn-pzw-actual-step-profile-carry
  (implies (and (fn-pzw-profile-carryp compressed expected ip end lim fn-zin-st fn-zin-out)
                (true-listp fn-zin-out)
                (< (len fn-zin-out) (nfix lim))
                (equal room (- (nfix lim) (len fn-zin-out))))
           (let ((r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
             (fn-pzw-profile-carryp compressed expected ip end lim
                                    (mv-nth 1 r) (mv-nth 4 r))))
  :hints (("Goal" :use (fn-zin-step-counts fn-zin-step-out-extends)
                  :in-theory (e/d (fn-pzw-profile-carryp)
                                  (fn-zin-step fn-zin-step-counts fn-zin-step-out-extends)))))

(defthm fn-pzw-actual-loop-profile-carry
  (implies (and (fn-pzw-profile-carryp compressed expected ip end lim fn-zin-st fn-zin-out)
                (true-listp fn-zin-out))
           (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets
                                  fn-zin-win fn-zin-tab fn-zin-out)))
             (fn-pzw-profile-carryp compressed expected (mv-nth 2 r) end lim
                                    (mv-nth 3 r) (mv-nth 6 r))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets
                                      fn-zin-win fn-zin-tab fn-zin-out)
                  :in-theory (e/d (fn-zin-loop)
                                  (fn-pzw-profile-carryp fn-zin-pull fn-zin-step
                                   fn-zin-step-out-free)))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pzw-profile-carried-input-upper
   (implies (fn-pzw-profile-carryp compressed expected ip end lim fn-zin-st fn-zin-out)
            (<= (fn-zin-tin fn-zin-st) (* 2 compressed)))
   :hints (("Goal" :in-theory (enable fn-pzw-profile-carryp)))
   :rule-classes nil)
 (defthm fn-pzw-profile-carried-output-upper
   (implies (fn-pzw-profile-carryp compressed expected ip end lim fn-zin-st fn-zin-out)
            (<= (fn-zin-tout fn-zin-st) (+ 1 expected)))
   :hints (("Goal" :in-theory (enable fn-pzw-profile-carryp)))
   :rule-classes nil)
 (defthm fn-pzw-actual-supported-bomb-width
   (implies (and (fn-pzw-profile-carryp compressed expected ip end lim fn-zin-st fn-zin-out)
                 (<= compressed 9223372036854775807))
            (and (natp (fn-zin-bomb-limit fn-zin-st))
                 (< (fn-zin-bomb-limit fn-zin-st) 9444732965739290427392)))
   :hints (("Goal" :use fn-pzw-profile-carried-input-upper
                   :in-theory (enable fn-pzw-profile-carryp fn-zin-bomb-limit)
                   :nonlinearp t))
   :rule-classes nil)
 (defthm fn-pzw-actual-supported-output-plus-preset-width
   (implies (and (fn-pzw-profile-carryp compressed expected ip end lim fn-zin-st fn-zin-out)
                 (fn-pzw-state-header-widthp fn-zin-st)
                 (<= expected 9223372036854775807))
            (and (natp (+ (fn-zin-tout fn-zin-st) (fn-zin-preset fn-zin-st)))
                 (< (+ (fn-zin-tout fn-zin-st) (fn-zin-preset fn-zin-st))
                    18446744073709551616)))
   :hints (("Goal" :in-theory (enable fn-pzw-profile-carryp fn-pzw-state-header-widthp)))
   :rule-classes nil)
 (defthm fn-pzw-actual-supported-budget-width
   (implies (and (<= (nfix compressed) 9223372036854775807)
                 (<= (nfix expected) 9223372036854775807))
            (and (natp (fn-pzd-budget compressed expected))
                 (< (fn-pzd-budget compressed expected) 295147905179352825856)))
   :hints (("Goal" :in-theory (enable fn-pzd-budget)))
   :rule-classes nil))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pzw-actual-stored-credit-establishes-profile-carry
   (implies (and (natp compressed) (natp expected) (natp start) (natp end)
                 (<= start end)
                 (<= (+ (fn-zin-tin fn-zin-st) (- end start)) compressed)
                 (<= (fn-zin-tout fn-zin-st)
                     (min expected (fn-pzw-stored-allowance compressed))))
            (fn-pzw-profile-carryp
             compressed expected start end
             (fn-pzw-room (min expected (fn-pzw-stored-allowance compressed))
                          (fn-zin-tout fn-zin-st))
             (fn-zin-set 7 (+ compressed (fn-zin-tin fn-zin-st)) fn-zin-st) nil))
   :hints (("Goal" :in-theory (enable fn-pzw-profile-carryp fn-pzw-room)))
   :rule-classes nil)
 (defthm fn-pzw-restore-credit-keeps-profile-carry
   (implies (fn-pzw-profile-carryp compressed expected ip end lim fn-zin-st fn-zin-out)
            (fn-pzw-profile-carryp
             compressed expected ip end lim
             (fn-zin-set 7 (nfix (- (fn-zin-tin fn-zin-st) (nfix credit))) fn-zin-st)
             fn-zin-out))
   :hints (("Goal" :in-theory (enable fn-pzw-profile-carryp)))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pzw-profile-carry-input-decrease
   (implies (and (fn-pzw-profile-carryp compressed expected ip end lim fn-zin-st fn-zin-out)
                 (<= (nfix value) (fn-zin-tin fn-zin-st)))
            (fn-pzw-profile-carryp compressed expected ip end lim
                                   (fn-zin-set 7 value fn-zin-st) fn-zin-out))
   :hints (("Goal" :in-theory (enable fn-pzw-profile-carryp))))
 (defthm fn-pzw-natural-subtraction-no-increase
   (implies (natp x) (<= (nfix (- x (nfix y))) x))
   :rule-classes (:rewrite :linear)))

(defthm fn-pzw-actual-stored-chunk-profile-carry
  (implies (and (natp compressed) (natp expected) (natp start) (natp end)
                (<= start end)
                (<= (+ (fn-zin-tin fn-zin-st) (- end start)) compressed)
                (<= (fn-zin-tout fn-zin-st)
                    (min expected (fn-pzw-stored-allowance compressed))))
           (let ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                        fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
             (fn-pzw-profile-carryp
              compressed expected (mv-nth 2 r) end
              (fn-pzw-room (min expected (fn-pzw-stored-allowance compressed))
                           (fn-zin-tout fn-zin-st))
              (mv-nth 3 r) (mv-nth 6 r))))
  :hints (("Goal" :use fn-pzw-actual-stored-credit-establishes-profile-carry
                  :in-theory
                  (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed)
                       (fn-pzw-profile-carryp fn-zin-loop fn-pzw-room
                        fn-pzw-stored-allowance fn-zin-loop-counts)))))
