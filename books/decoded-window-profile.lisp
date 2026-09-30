; PRF-1132 / SCN-1039: descriptor-to-funding scalar domain.
; Exact descriptor source imported from b8b721116. This joins the actual
; descriptor recognizer to the selected signed off_t domain. It is neither
; a job-demand vector nor permission to activate a supplied-demand caller.
(in-package "ACL2")
(include-book "decoded-window-descriptor")
(include-book "payload-window-expanded-profile-width")

(defun fn-pwz-native-offsetp (descriptor)
  (declare (xargs :guard t))
  (<= (+ (nfix (fn-pwz-nth 1 descriptor))
         (nfix (fn-pwz-nth 2 descriptor)) 32)
      9223372036854775807))

(defun fn-pwz-demand-join (a b)
  (declare (xargs :guard t))
  (max (nfix a) (nfix b)))
(in-theory (disable fn-pwz-demand-join))

; File identities, issued tickets, trailer integers and dictionary IDs are
; not restricted to signed63 bits. Fund their actual limb widths separately.
; This fixed nine-field ceiling includes next-ticket construction, file end,
; actual action budget and the credited-input bomb intermediate512*C+65536.
; It supplies an operand/retained-width input, NOT a complete runtime tariff.
(defun fn-pwz-demand-natural-ceiling (descriptor ticket)
  (declare (xargs :guard t))
  (fn-pwz-demand-join
   (+ 1 (nfix ticket))
   (fn-pwz-demand-join (nfix (fn-pwz-nth 0 descriptor))
    (fn-pwz-demand-join (+ (nfix (fn-pwz-nth 1 descriptor))
            (nfix (fn-pwz-nth 2 descriptor)) 32)
     (fn-pwz-demand-join (nfix (fn-pwz-nth 3 descriptor))
      (fn-pwz-demand-join (+ 65536 (* 512 (nfix (fn-pwz-nth 4 descriptor))))
       (fn-pwz-demand-join (nfix (fn-pwz-nth 5 descriptor))
        (fn-pwz-demand-join (nfix (fn-pwz-nth 6 descriptor))
         (fn-pwz-demand-join (+ 65537 (nfix (fn-pwz-nth 7 descriptor)))
          (fn-pwz-demand-join (nfix (fn-pwz-nth 8 descriptor))
           (fn-pwz-demand-join (fn-pzd-budget (fn-pwz-nth 4 descriptor)
                                (fn-pwz-nth 7 descriptor))
                231584178474632390847141970017375815706539969331281128078915168015826259279871)))))))))))

; Keep the shared nested expression opaque before clausification, not only
; after a hint runs. Its individual max bounds are opened below explicitly.
(in-theory (disable fn-pwz-demand-natural-ceiling))

(local
 (defun fn-pwz-profile-nth-induct (count index fields)
   (if (zp index) (list count fields)
     (fn-pwz-profile-nth-induct (1- count) (1- index)
                               (if (consp fields) (cdr fields) nil)))))

(local
 (defthm fn-pwz-profile-nth-natural
   (implies (and (fn-pwz-naturals count fields)
                 (natp count) (natp index) (< index count))
            (natp (fn-pwz-nth index fields)))
   :hints (("Goal" :induct (fn-pwz-profile-nth-induct count index fields)
            :in-theory (enable fn-pwz-naturals fn-pwz-nth)))))

(local
 (defthm fn-pwz-profile-descriptor-scalars
   (implies (fn-pwz-descriptorp descriptor)
            (and (natp (fn-pwz-nth 0 descriptor))
                 (natp (fn-pwz-nth 1 descriptor))
                 (natp (fn-pwz-nth 2 descriptor))
                 (natp (fn-pwz-nth 3 descriptor))
                 (natp (fn-pwz-nth 4 descriptor))
                 (natp (fn-pwz-nth 5 descriptor))
                 (natp (fn-pwz-nth 6 descriptor))
                 (natp (fn-pwz-nth 7 descriptor))
                 (natp (fn-pwz-nth 8 descriptor))))
   :hints (("Goal" :use (
                  (:instance fn-pwz-profile-nth-natural (count 9) (index 0) (fields descriptor))
                  (:instance fn-pwz-profile-nth-natural (count 9) (index 1) (fields descriptor))
                  (:instance fn-pwz-profile-nth-natural (count 9) (index 2) (fields descriptor))
                  (:instance fn-pwz-profile-nth-natural (count 9) (index 3) (fields descriptor))
                  (:instance fn-pwz-profile-nth-natural (count 9) (index 4) (fields descriptor))
                  (:instance fn-pwz-profile-nth-natural (count 9) (index 5) (fields descriptor))
                  (:instance fn-pwz-profile-nth-natural (count 9) (index 6) (fields descriptor))
                  (:instance fn-pwz-profile-nth-natural (count 9) (index 7) (fields descriptor))
                  (:instance fn-pwz-profile-nth-natural (count 9) (index 8) (fields descriptor)))
            :in-theory
            (e/d (fn-pwz-descriptorp) (fn-pwz-naturals fn-pwz-nth
                  fn-pzw-stored-admissiblep fn-pwz-shipped-idp
                  fn-pwz-profile-nth-natural))))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pwz-actual-descriptor-establishes-decoder-funding-domain
   (implies (and (fn-pwz-descriptorp descriptor)
                 (fn-pwz-native-offsetp descriptor))
            (let ((compressed (fn-pwz-nth 4 descriptor))
                  (expected (fn-pwz-nth 7 descriptor)))
              (and (natp compressed) (< compressed 9223372036854775808)
                   (natp expected) (< expected 4722366482869645213696)
                   (natp (fn-pzd-budget compressed expected))
                   (< (fn-pzd-budget compressed expected) 9444732965739290427392)
                   (<= (+ (fn-pwz-nth 1 descriptor)
                          (fn-pwz-nth 2 descriptor) 32)
                       9223372036854775807))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-pwz-profile-descriptor-scalars)
                  (:instance fn-pzw-stored-supported-expected-width
                             (compressed (fn-pwz-nth 4 descriptor))
                             (expected (fn-pwz-nth 7 descriptor)))
                  (:instance fn-pzw-stored-supported-budget-width
                             (compressed (fn-pwz-nth 4 descriptor))
                             (expected (fn-pwz-nth 7 descriptor))))
            :in-theory
            (e/d (fn-pwz-descriptorp fn-pwz-native-offsetp)
                 (fn-pwz-naturals fn-pwz-nth fn-pzd-budget
                  fn-pwz-profile-descriptor-scalars fn-pwz-profile-nth-natural
                  fn-pzw-stored-admissiblep))))))

(local
 (defthm fn-pwz-profile-max-natural
   (natp (fn-pwz-demand-join a b))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-pwz-demand-join)))))

(local
 (defthm fn-pwz-profile-max-upper
   (implies (and (natp a) (natp b))
            (and (<= a (fn-pwz-demand-join a b))
                 (<= b (fn-pwz-demand-join a b))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-pwz-demand-join)))))

(defthm fn-pwz-demand-ceiling-covers-issued-identity-by-definition
  (and (natp (fn-pwz-demand-natural-ceiling descriptor ticket))
       (<= (+ 1 (nfix ticket))
           (fn-pwz-demand-natural-ceiling descriptor ticket))
       (<= (nfix (fn-pwz-nth 0 descriptor))
           (fn-pwz-demand-natural-ceiling descriptor ticket))
       (<= (nfix (fn-pwz-nth 6 descriptor))
           (fn-pwz-demand-natural-ceiling descriptor ticket))
       (<= (nfix (fn-pwz-nth 8 descriptor))
           (fn-pwz-demand-natural-ceiling descriptor ticket)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :in-theory
           (e/d (fn-pwz-demand-natural-ceiling)
                (nfix natp fn-pwz-demand-join fn-pwz-nth fn-pzd-budget)))))

(in-theory (disable fn-pwz-native-offsetp fn-pwz-demand-join
                    fn-pwz-demand-natural-ceiling))
