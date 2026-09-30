(in-package "ACL2")
(include-book "../../books/decoded-window-initial-funding-domain")

(defun pwzif-test-report (token)
 (declare (xargs :verify-guards nil))
 (with-local-stobj pgs-digest-state
 (mv-let (answer pgs-digest-state)
 (with-local-stobj fn-zin-st
 (mv-let (answer fn-zin-st pgs-digest-state)
 (with-local-stobj fn-zin-win
 (mv-let (answer fn-zin-win fn-zin-st pgs-digest-state)
 (with-local-stobj fn-zin-tab
 (mv-let (answer fn-zin-tab fn-zin-win fn-zin-st pgs-digest-state)
 (with-local-stobj fn-zin-out
 (mv-let (answer fn-zin-out fn-zin-tab fn-zin-win fn-zin-st pgs-digest-state)
 (mv-let (z pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
 (fn-pwz-begin token 301 pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
 (mv (list
       (and (fn-pzw-state-bits-widthp fn-zin-st)
            (fn-pzw-state-walk-widthp fn-zin-st)
            (fn-pzw-state-header-widthp fn-zin-st))
       (and (equal (fn-zin-win-len fn-zin-win) *fn-zin-win-octets*)
            (equal (fn-zin-tab-len fn-zin-tab) *fn-zin-tab-octets*)
            (fn-cbor-octet-listp (fn-zin-win-list fn-zin-win)) (fn-cbor-octet-listp (fn-zin-tab-list fn-zin-tab))
            (equal (fn-zin-out-list fn-zin-out) nil))
       (and (natp (nth 2 z)) (< (nth 2 z) 4722366482869645213696)
            (natp (nth 3 z)) (<= (nth 3 z) (nth 2 z))
            (natp (nth 4 z)) (<= (nth 4 z) 16384)
            (natp (nth 5 z)) (< (nth 5 z) 9444732965739290427392)
            (equal (nth 5 z) (fn-pzd-budget (fn-pwz-nth 6 token) (fn-pwz-nth 9 token)))
            (equal (nth 6 z) 0) (equal (nth 7 z) 0) (equal (nth 8 z) :more))
       (and (equal (fn-zin-tin fn-zin-st) 0) (equal (fn-zin-tout fn-zin-st) 0)))
     fn-zin-out fn-zin-tab fn-zin-win fn-zin-st pgs-digest-state))
 (mv answer fn-zin-tab fn-zin-win fn-zin-st pgs-digest-state)))
 (mv answer fn-zin-win fn-zin-st pgs-digest-state)))
 (mv answer fn-zin-st pgs-digest-state)))
 (mv answer pgs-digest-state)))
 answer)))

; Reachable core scalar positive, actual empty-preset initializer.
(defthm pwzif-literal-actual-positive
 (let* ((d (fn-pwz-cold-descriptor 7 100 2048 120 1024
                                 115792089237316195423570985008687907853269984665640564039457584007913129639936
                                 93100 nil 200))
        (token (cons :decoded-window (cons 17 d))) (r (pwzif-test-report token)))
   (and (fn-pwz-tokenp token) (fn-pwz-native-offsetp (cddr token))
        (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r)))
 :rule-classes nil)

; Scalar supported-profile positive; no materialized huge file is asserted.
(defthm pwzif-literal-wide-decoded-positive
 (let* ((d (fn-pwz-cold-descriptor 7 0 144115188075855872 0 144115188075855872
                                 99 36893488147419103232 nil 200))
        (token (cons :decoded-window (cons 17 d))) (r (pwzif-test-report token)))
   (and (fn-pwz-tokenp token) (fn-pwz-native-offsetp (cddr token))
        (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r)))
 :rule-classes nil)

; Corrupted typed-state removal: retained selected offset is true, complete
; actual control conclusion is false. Reset/buffer facts remain unconditional.
(defthm pwzif-literal-remove-typed-token
 (let* ((token '(:decoded-window 17 7 0 0 0 0 0 99 4722366482869645213696 0))
        (r (pwzif-test-report token)))
   (and (not (fn-pwz-tokenp token)) (fn-pwz-native-offsetp (cddr token))
        (not (nth 2 r)) (nth 0 r) (nth 1 r) (nth 3 r)))
 :rule-classes nil)

; Logical descriptor outside the selected native offset profile; not an I/O
; attempt or a new stored-data policy. Affirm retained typed token in full.
(defthm pwzif-literal-remove-native-offset
 (let* ((d (fn-pwz-cold-descriptor 7 0 1180591620717411303424 0 1180591620717411303424
                                 99 4722366482869645213696 nil 200))
        (token (cons :decoded-window (cons 17 d))) (r (pwzif-test-report token)))
   (and (fn-pwz-tokenp token) (not (fn-pwz-native-offsetp (cddr token)))
        (not (nth 2 r)) (nth 0 r) (nth 1 r) (nth 3 r)))
 :rule-classes nil)

; Actual shipped preset lookup and initialization, not a per-borrow copied
; dictionary in a served path. Full source conclusions are asserted again.
(defthm pwzif-literal-shipped-preset-positive
 (let* ((dict (fn-lzd-lookup (fn-lzd-current-id)))
        (d (fn-pwz-cold-descriptor 7 100 2048 120 1024 99 93100 dict 200))
        (token (cons :decoded-window (cons 17 d))) (r (pwzif-test-report token)))
   (and (fn-pwz-tokenp token) (fn-pwz-native-offsetp (cddr token))
        (equal (fn-pwz-nth 10 token) (fn-lzd-current-id))
        (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r)))
 :rule-classes nil)
