(in-package "ACL2")
(include-book "../../books/extent-window-buffer")

(defun ewbt-byte (src count dst input j)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (answer fn-octets)
      (with-local-stobj fn-ew-buffer
        (mv-let (answer fn-ew-buffer fn-octets)
          (let* ((fn-octets (fn-octets-from-list input fn-octets))
                 (fn-ew-buffer (fn-ewb-copy src count dst fn-octets fn-ew-buffer)))
            (mv (fn-ew-bytesi j fn-ew-buffer) fn-ew-buffer fn-octets))
          (mv answer fn-octets)))
      answer)))

; REACHABLE POSITIVE: actual concrete copy, full literal antecedent and
; pointwise conclusion, with a nonempty copy and an independently named byte.
(assert-event
 (let ((src 1) (count 3) (dst 10) (j 11) (input '(5 17 18 19 20)))
   (and (natp src) (natp count) (natp dst) (natp j)
        (equal (ewbt-byte src count dst input j)
               (if (and (<= dst j) (< j (+ dst count)))
                   (nth (+ src (- j dst)) input) 0))
        (equal (ewbt-byte src count dst input j) 18)
        (equal (ewbt-byte src count dst input 9) 0)
        (equal (ewbt-byte src count dst input 10) 17)
        (equal (ewbt-byte src count dst input 12) 19)
        (equal (ewbt-byte src count dst input 13) 0))))

; Final byte of fixed storage is usable; no off-by-one lost cell.
(assert-event
 (and (equal (ewbt-byte 2 1 16383 '(6 7 255) 16383) 255)
      (equal (ewbt-byte 2 1 16383 '(6 7 255) 16382) 0)))

; Literal logical hypothesis-removal witness for capacity preservation.
; This out-of-guard tiny buffer is not a reachable concrete host buffer.
(defthm ewbt-capacity-removal
  (let* ((src 0) (count 1) (dst 2) (before (list '(0 0)))
         (after (fn-ewb-copy src count dst '(42) before)))
    (and (natp src) (natp count) (natp dst)
         (not (<= (+ dst count) (len (nth 0 before))))
         (not (equal (len (nth 0 after)) (len (nth 0 before))))))
  :hints (("Goal" :in-theory (enable fn-ewb-copy)))
  :rule-classes nil)
