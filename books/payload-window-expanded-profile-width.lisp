; PRF-1132 continuation. The stored ratio allowance is wider than signed63
; decoded bytes. No new decoded-length policy is installed by these proofs.
(in-package "ACL2")
(include-book "payload-window-profile-width")

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pzw-stored-supported-expected-width
   (implies (and (fn-pzw-stored-admissiblep compressed expected)
                 (<= compressed 9223372036854775807))
            (and (natp expected) (< expected 4722366482869645213696)))
   :hints (("Goal" :in-theory (enable fn-pzw-stored-admissiblep
                                    fn-pzw-stored-allowance
                                    fn-zin-stored-allowance)))
   :rule-classes nil)
 (defthm fn-pzw-stored-supported-budget-width
   (implies (and (fn-pzw-stored-admissiblep compressed expected)
                 (<= compressed 9223372036854775807))
            (and (natp (fn-pzd-budget compressed expected))
                 (< (fn-pzd-budget compressed expected) 9444732965739290427392)))
   :hints (("Goal" :in-theory (enable fn-pzw-stored-admissiblep
                                    fn-pzw-stored-allowance
                                    fn-zin-stored-allowance fn-pzd-budget)))
   :rule-classes nil)
 (defthm fn-pzw-actual-stored-supported-output-plus-preset-width
   (implies (and (fn-pzw-profile-carryp compressed expected ip end lim fn-zin-st fn-zin-out)
                 (fn-pzw-state-header-widthp fn-zin-st)
                 (fn-pzw-stored-admissiblep compressed expected)
                 (<= compressed 9223372036854775807))
            (and (natp (+ (fn-zin-tout fn-zin-st) (fn-zin-preset fn-zin-st)))
                 (< (+ (fn-zin-tout fn-zin-st) (fn-zin-preset fn-zin-st))
                    4722366482869645213696)))
   :hints (("Goal" :in-theory (enable fn-pzw-profile-carryp
                                    fn-pzw-state-header-widthp
                                    fn-pzw-stored-admissiblep
                                    fn-pzw-stored-allowance fn-zin-stored-allowance)))
   :rule-classes nil))
