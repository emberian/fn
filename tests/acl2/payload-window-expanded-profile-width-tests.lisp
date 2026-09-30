; SCN-1039 continuation. Literal widened stored-profile width teeth.
(in-package "ACL2")
(include-book "../../books/payload-window-expanded-profile-width")

(defun-nx pzwewt-width-probe (compressed expected tout preset)
  (let* ((state (fn-zin-reset (create-fn-zin-st)))
         (state (fn-zin-set 6 tout state))
         (state (fn-zin-set 18 preset state)))
    (list (fn-pzw-stored-admissiblep compressed expected)
          (<= compressed 9223372036854775807)
          (and (natp expected) (< expected 4722366482869645213696))
          (and (natp (fn-pzd-budget compressed expected))
               (< (fn-pzd-budget compressed expected) 9444732965739290427392))
          (fn-pzw-profile-carryp compressed expected 0 0 0 state nil)
          (fn-pzw-state-header-widthp state)
          (and (natp (+ (fn-zin-tout state) (fn-zin-preset state)))
               (< (+ (fn-zin-tout state) (fn-zin-preset state))
                  4722366482869645213696)))))

(defthm pzwewt-actual-expanded-positive
  (let* ((c 9223372036854775807) (n (fn-pzw-stored-allowance c))
         (r (pzwewt-width-probe c n (+ 1 n) 32768)))
    (and (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r)
         (nth 4 r) (nth 5 r) (nth 6 r)
         (< 9223372036854775807 n)))
  :rule-classes nil)

(defthm pzwewt-remove-expected-admissible
  (let ((r (pzwewt-width-probe 0 (expt 2 80) 0 0)))
    (and (not (nth 0 r)) (nth 1 r) (not (nth 2 r)) (not (nth 3 r))))
  :rule-classes nil)
(defthm pzwewt-remove-expected-supported-compressed
  (let* ((c (expt 2 80)) (r (pzwewt-width-probe c (fn-pzw-stored-allowance c) 0 0)))
    (and (nth 0 r) (not (nth 1 r)) (not (nth 2 r)) (not (nth 3 r))))
  :rule-classes nil)

(defthm pzwewt-remove-output-profile-carry
  (let ((r (pzwewt-width-probe 0 0 (expt 2 80) 0)))
    (and (nth 0 r) (nth 1 r) (not (nth 4 r)) (nth 5 r) (not (nth 6 r))))
  :rule-classes nil)
(defthm pzwewt-remove-output-header-carry
  (let ((r (pzwewt-width-probe 0 0 0 (expt 2 80))))
    (and (nth 0 r) (nth 1 r) (nth 4 r) (not (nth 5 r)) (not (nth 6 r))))
  :rule-classes nil)
(defthm pzwewt-remove-output-admissible
  (let ((r (pzwewt-width-probe 0 (expt 2 80) (expt 2 80) 0)))
    (and (not (nth 0 r)) (nth 1 r) (nth 4 r) (nth 5 r) (not (nth 6 r))))
  :rule-classes nil)
(defthm pzwewt-remove-output-supported-compressed
  (let* ((c (expt 2 80)) (n (fn-pzw-stored-allowance c))
         (r (pzwewt-width-probe c n n 0)))
    (and (nth 0 r) (not (nth 1 r)) (nth 4 r) (nth 5 r) (not (nth 6 r))))
  :rule-classes nil)

; Mutation: the old decoded signed63 ceiling would reject a permitted span.
(defthm pzwewt-signed63-decoded-ceiling-mutant
  (let* ((c 9223372036854775807) (n (fn-pzw-stored-allowance c)))
    (and (fn-pzw-stored-admissiblep c n)
         (<= c 9223372036854775807)
         (not (<= n 9223372036854775807))))
  :rule-classes nil)
