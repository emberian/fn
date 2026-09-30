; Full literal descriptor/funding-domain teeth. These are library source
; predicates and actual core descriptor construction, not live file reads.
(in-package "ACL2")
(include-book "../../books/decoded-window-profile")

(defconst *pwzpt-small*
  (fn-pwz-cold-descriptor 1 0 1040 16 1024
                          115792089237316195423570985008687907853269984665640564039457584007913129639936
                          93100 nil 250))
; A supported scalar descriptor with N above2^63: no materialized body/file
; or live runtime admission is claimed by constructing these nine fields.
(defconst *pwzpt-wide*
  (fn-pwz-cold-descriptor 1 0 144115188075855888 16 144115188075855872
                          115792089237316195423570985008687907853269984665640564039457584007913129639936
                          36893488147419103232 nil 0))

;@positive fn-pwz-actual-descriptor-establishes-decoder-funding-domain
(defthm pwzpt-actual-small-descriptor-complete-positive
  (let* ((descriptor *pwzpt-small*)
         (compressed (fn-pwz-nth 4 descriptor))
         (expected (fn-pwz-nth 7 descriptor)))
    (and (fn-pwz-descriptorp descriptor) (fn-pwz-native-offsetp descriptor)
         (natp compressed) (< compressed 9223372036854775808)
         (natp expected) (< expected 4722366482869645213696)
         (natp (fn-pzd-budget compressed expected))
         (< (fn-pzd-budget compressed expected) 9444732965739290427392)
         (<= (+ (fn-pwz-nth 1 descriptor) (fn-pwz-nth 2 descriptor) 32)
             9223372036854775807)))
  :rule-classes nil)

;@positive fn-pwz-actual-descriptor-establishes-decoder-funding-domain
(defthm pwzpt-actual-wide-descriptor-complete-positive
  (let* ((descriptor *pwzpt-wide*)
         (compressed (fn-pwz-nth 4 descriptor))
         (expected (fn-pwz-nth 7 descriptor)))
    (and (fn-pwz-descriptorp descriptor) (fn-pwz-native-offsetp descriptor)
         (natp compressed) (< compressed 9223372036854775808)
         (natp expected) (< expected 4722366482869645213696)
         (natp (fn-pzd-budget compressed expected))
         (< (fn-pzd-budget compressed expected) 9444732965739290427392)
         (<= (+ (fn-pwz-nth 1 descriptor) (fn-pwz-nth 2 descriptor) 32)
             9223372036854775807)
         (<= 9223372036854775808 expected)))
  :rule-classes nil)

; Corrupted extent containment, keeping the exact native-end hypothesis.
;@hypothesis-removal fn-pwz-actual-descriptor-establishes-decoder-funding-domain
(defthm pwzpt-corrupted-descriptor-removal
  (let* ((descriptor '(1 0 0 0 18446744073709551616 0 0 0 0))
         (compressed (fn-pwz-nth 4 descriptor))
         (expected (fn-pwz-nth 7 descriptor)))
    (and (not (fn-pwz-descriptorp descriptor)) (fn-pwz-native-offsetp descriptor)
         (not
          (and (natp compressed) (< compressed 9223372036854775808)
               (natp expected) (< expected 4722366482869645213696)
               (natp (fn-pzd-budget compressed expected))
               (< (fn-pzd-budget compressed expected) 9444732965739290427392)
               (<= (+ (fn-pwz-nth 1 descriptor) (fn-pwz-nth 2 descriptor) 32)
                   9223372036854775807)))))
  :rule-classes nil)

; Valid logical descriptor outside the selected offset ABI; not truncation.
;@hypothesis-removal fn-pwz-actual-descriptor-establishes-decoder-funding-domain
(defthm pwzpt-selected-offset-removal
  (let* ((descriptor (fn-pwz-cold-descriptor
                      1 0 1180591620717411303424 0 1180591620717411303424
                      0 4722366482869645213696 nil 0))
         (compressed (fn-pwz-nth 4 descriptor))
         (expected (fn-pwz-nth 7 descriptor)))
    (and (fn-pwz-descriptorp descriptor) (not (fn-pwz-native-offsetp descriptor))
         (not
          (and (natp compressed) (< compressed 9223372036854775808)
               (natp expected) (< expected 4722366482869645213696)
               (natp (fn-pzd-budget compressed expected))
               (< (fn-pzd-budget compressed expected) 9444732965739290427392)
               (<= (+ (fn-pwz-nth 1 descriptor) (fn-pwz-nth 2 descriptor) 32)
                   9223372036854775807)))))
  :rule-classes nil)

; The descriptor recognizer does not certify the captured32-byte trailer.
; This deliberately corrupted captured trailer passes the scalar recognizer
; and offset predicate. Therefore neither can justify a257-bit tariff alone.
(defthm pwzpt-corrupted-trailer-has-no-descriptor-width-guarantee
  (let* ((trailer (expt 2 400))
         (descriptor (fn-pwz-cold-descriptor 1 0 1040 16 1024 trailer 93100 nil 0)))
    (and (fn-pwz-descriptorp descriptor) (fn-pwz-native-offsetp descriptor)
         (not (< (fn-pwz-nth 6 descriptor) (expt 2 257)))
         (<= trailer (fn-pwz-demand-natural-ceiling descriptor 1))))
  :rule-classes nil)

; Complete unconditional ceiling conclusion with wide identity/ticket boxes.
; This is a by-definition helper witness, not actual issued-file provenance.
(defthm pwzpt-wide-issued-identity-ceiling-complete-positive
  (let* ((ticket (expt 2 500))
         (descriptor (fn-pwz-cold-descriptor
                      (expt 2 300) 0 1040 16 1024 (expt 2 256) 93100 nil 0)))
    (and (natp (fn-pwz-demand-natural-ceiling descriptor ticket))
         (<= (+ 1 (nfix ticket)) (fn-pwz-demand-natural-ceiling descriptor ticket))
         (<= (nfix (fn-pwz-nth 0 descriptor))
             (fn-pwz-demand-natural-ceiling descriptor ticket))
         (<= (nfix (fn-pwz-nth 6 descriptor))
             (fn-pwz-demand-natural-ceiling descriptor ticket))
         (<= (nfix (fn-pwz-nth 8 descriptor))
             (fn-pwz-demand-natural-ceiling descriptor ticket))))
  :rule-classes nil)
