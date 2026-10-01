; SCN-1039 continuation. Literal actual profile carry and width witnesses.
(in-package "ACL2")
(include-book "../../books/payload-window-profile-width")

(defun-nx pzwpwt-stored-probe (compressed expected start end tin tout input quantum)
  (let* ((state (fn-zin-reset (create-fn-zin-st)))
         (state (fn-zin-set 7 tin state))
         (state (fn-zin-set 6 tout state))
         (r (fn-pzw-stored-chunk quantum quantum start end compressed expected
                                 state input (make-list 65536 :initial-element 0)
                                 (make-list 3494 :initial-element 0) nil)))
    (list (natp compressed) (natp expected) (natp start) (natp end)
          (<= start end)
          (<= (+ (fn-zin-tin state) (- end start)) compressed)
          (<= (fn-zin-tout state) (min expected (fn-pzw-stored-allowance compressed)))
          (fn-pzw-profile-carryp
           compressed expected (mv-nth 2 r) end
           (fn-pzw-room (min expected (fn-pzw-stored-allowance compressed))
                        (fn-zin-tout state)) (mv-nth 3 r) (mv-nth 6 r))
          (mv-nth 2 r)
          (fn-pzw-profile-carryp
           compressed expected (mv-nth 2 r) end
           (fn-pzw-room (min expected (fn-pzw-stored-allowance compressed))
                        (fn-zin-tout state))
           (fn-zin-set 7 (+ 1 (* 2 (nfix compressed))) (mv-nth 3 r))
           (mv-nth 6 r)))))

(defthm pzwpwt-actual-stored-profile-positive
  (equal (pzwpwt-stored-probe 1 100 0 1 0 0 '(255) 1)
         '(t t t t t t t t 1 nil))
  :rule-classes nil)

; Each literal removal retains every other hypothesis, negates the omitted
; one and the actual endpoint conclusion. Invalid scalar/physical spans
; here are logical-only witnesses, never native guard bypasses.
(defthm pzwpwt-remove-natural-compressed
  (equal (pzwpwt-stored-probe 1/2 0 0 0 0 0 nil 0)
         '(nil t t t t t t nil 0 nil))
  :rule-classes nil)
(defthm pzwpwt-remove-natural-expected
  (equal (pzwpwt-stored-probe 1 1/2 0 0 0 0 nil 0)
         '(t nil t t t t t nil 0 nil))
  :rule-classes nil)
(defthm pzwpwt-remove-natural-start
  (equal (pzwpwt-stored-probe 1 0 -1 0 0 0 nil 0)
         '(t t nil t t t t nil -1 nil))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (disable (:executable-counterpart fn-pzw-stored-chunk)
                    (:executable-counterpart fn-pzw-chunk)
                    (:executable-counterpart fn-zin-feed)
                    (:executable-counterpart fn-zin-loop)))))
(defthm pzwpwt-remove-natural-end
  (equal (pzwpwt-stored-probe 1 0 0 'bad 0 0 nil 0)
         '(t t t nil t t t nil 0 nil))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (disable (:executable-counterpart fn-pzw-stored-chunk)
                    (:executable-counterpart fn-pzw-chunk)
                    (:executable-counterpart fn-zin-feed)
                    (:executable-counterpart fn-zin-loop)))))
(defthm pzwpwt-remove-span-order
  (equal (pzwpwt-stored-probe 0 0 1 0 0 0 nil 0)
         '(t t t t nil t t nil 1 nil))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (disable (:executable-counterpart fn-pzw-stored-chunk)
                    (:executable-counterpart fn-pzw-chunk)
                    (:executable-counterpart fn-zin-feed)
                    (:executable-counterpart fn-zin-loop)))))
(defthm pzwpwt-remove-source-containment
  (equal (pzwpwt-stored-probe 0 0 0 1 0 0 '(0) 0)
         '(t t t t t nil t nil 0 nil))
  :rule-classes nil)
(defthm pzwpwt-remove-produced-bound
  (equal (pzwpwt-stored-probe 1 0 0 0 0 2 nil 0)
         '(t t t t t t nil nil 0 nil))
  :rule-classes nil)

(defun-nx pzwpwt-width-probe (compressed expected tin tout preset)
  (let* ((state (fn-zin-reset (create-fn-zin-st)))
         (state (fn-zin-set 7 tin state))
         (state (fn-zin-set 6 tout state))
         (state (fn-zin-set 18 preset state)))
    (list (fn-pzw-profile-carryp compressed expected 0 0 0 state nil)
          (<= compressed 9223372036854775807)
          (and (natp (fn-zin-bomb-limit state))
               (< (fn-zin-bomb-limit state) 9444732965739290427392))
          (< (fn-zin-bomb-limit state) 4722366482869645213696)
          (fn-pzw-state-header-widthp state)
          (<= expected 9223372036854775807)
          (and (natp (+ (fn-zin-tout state) (fn-zin-preset state)))
               (< (+ (fn-zin-tout state) (fn-zin-preset state))
                  18446744073709551616)))))

; Maximum supported C gives an actual bomb value above2^72 but below2^73.
; This positive witness distinguishes73magnitude bits from a false72bit cap.
(defthm pzwpwt-actual-bomb-width-positive
  (let ((r (pzwpwt-width-probe 9223372036854775807 0
                              18446744073709551614 0 0)))
    (and (nth 0 r) (nth 1 r) (nth 2 r) (not (nth 3 r))))
  :rule-classes nil)
(defthm pzwpwt-remove-bomb-profile-carry
  (let ((r (pzwpwt-width-probe 0 0 (expt 2 80) 0 0)))
    (and (not (nth 0 r)) (nth 1 r) (not (nth 2 r))))
  :rule-classes nil)
(defthm pzwpwt-remove-bomb-supported-compressed
  (let* ((c (expt 2 80)) (r (pzwpwt-width-probe c 0 (* 2 c) 0 0)))
    (and (nth 0 r) (not (nth 1 r)) (not (nth 2 r))))
  :rule-classes nil)
(defthm pzwpwt-actual-output-plus-preset-positive
  (let ((r (pzwpwt-width-probe 0 9223372036854775807 0
                              9223372036854775808 32768)))
    (and (nth 0 r) (nth 4 r) (nth 5 r) (nth 6 r)))
  :rule-classes nil)
(defthm pzwpwt-remove-output-profile-carry
  (let ((r (pzwpwt-width-probe 0 0 0 (expt 2 80) 0)))
    (and (not (nth 0 r)) (nth 4 r) (nth 5 r) (not (nth 6 r))))
  :rule-classes nil)
(defthm pzwpwt-remove-header-carry
  (let ((r (pzwpwt-width-probe 0 0 0 0 (expt 2 80))))
    (and (nth 0 r) (not (nth 4 r)) (nth 5 r) (not (nth 6 r))))
  :rule-classes nil)
(defthm pzwpwt-remove-supported-expected
  (let* ((n (expt 2 80)) (r (pzwpwt-width-probe 0 n 0 n 0)))
    (and (nth 0 r) (nth 4 r) (not (nth 5 r)) (not (nth 6 r))))
  :rule-classes nil)

(defun-nx pzwpwt-budget-probe (c n)
  (list (<= (nfix c) 9223372036854775807)
        (<= (nfix n) 9223372036854775807)
        (and (natp (fn-pzd-budget c n))
             (< (fn-pzd-budget c n) 295147905179352825856))))
(defthm pzwpwt-budget-positive
  (equal (pzwpwt-budget-probe 9223372036854775807 9223372036854775807) '(t t t))
  :rule-classes nil)
(defthm pzwpwt-budget-remove-compressed-domain
  (equal (pzwpwt-budget-probe (expt 2 80) 0) '(nil t nil))
  :rule-classes nil)
(defthm pzwpwt-budget-remove-expected-domain
  (equal (pzwpwt-budget-probe 0 (expt 2 80)) '(t nil nil))
  :rule-classes nil)

; Labelled counter update mutant: the real consuming chunk keeps its
; literal complete antecedent/conclusion; replacing its TIN by2C+1 fails.
(defthm pzwpwt-stored-counter-mutation
  (let ((r (pzwpwt-stored-probe 1 100 0 1 0 0 '(255) 1)))
    (and (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r)
         (nth 5 r) (nth 6 r) (nth 7 r) (not (nth 9 r))))
  :rule-classes nil)

; Labelled bomb coefficient mutant, retaining the full literal carry and
; supported-C premises and the actual73bit conclusion before doubling it.
(defthm pzwpwt-bomb-coefficient-mutation
  (let* ((c 9223372036854775807) (tin (* 2 c))
         (r (pzwpwt-width-probe c 0 tin 0 0)))
    (and (nth 0 r) (nth 1 r) (nth 2 r)
         (not (< (+ (* 512 tin) 65536) 9444732965739290427392))))
  :rule-classes nil)
(defthm pzwpwt-output-coefficient-mutation
  (let* ((n 9223372036854775807) (tout (+ 1 n))
         (r (pzwpwt-width-probe 0 n 0 tout 32768)))
    (and (nth 0 r) (nth 4 r) (nth 5 r) (nth 6 r)
         (not (< (+ (* 3 tout) 32768) 18446744073709551616))))
  :rule-classes nil)
(defthm pzwpwt-budget-coefficient-mutation
  (let* ((c 9223372036854775807) (n c)
         (r (pzwpwt-budget-probe c n)))
    (and (nth 0 r) (nth 1 r) (nth 2 r)
         (not (< (+ 4096 (* 64 c) (* 2 n)) 295147905179352825856))))
  :rule-classes nil)
