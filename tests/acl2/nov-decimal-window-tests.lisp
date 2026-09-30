(in-package "ACL2")
(include-book "../../books/nov-decimal-window")

(defthm ndwt-codec-maximum-positive
  (let* ((n *fn-record-max-octets*) (r (fn-nbw-decimal-tick n 10 nil)))
    (and (natp n) (<= n *fn-record-max-octets*)
         (mv-nth 0 r) (equal (mv-nth 2 r) 0)
         (character-listp (mv-nth 1 r)) (<= (mv-nth 3 r) 10)
         (< 0 (len (mv-nth 1 r))) (<= (len (mv-nth 1 r)) 10)
         (equal (mv-nth 1 r) (explode-nonnegative-integer n 10 nil))
         (equal (coerce (mv-nth 1 r) 'string) "4294967295")))
  :rule-classes nil)

(defthm ndwt-codec-zero-positive
  (let ((r (fn-nbw-decimal-tick 0 10 nil)))
    (and (natp 0) (<= 0 *fn-record-max-octets*)
         (mv-nth 0 r) (equal (mv-nth 2 r) 0)
         (character-listp (mv-nth 1 r)) (<= (mv-nth 3 r) 10)
         (< 0 (len (mv-nth 1 r))) (<= (len (mv-nth 1 r)) 10)
         (equal (mv-nth 1 r) (explode-nonnegative-integer 0 10 nil))
         (equal (mv-nth 3 r) 0)))
  :rule-classes nil)

(defthm ndwt-codec-without-natural-corrupted-state
  (let* ((n -1) (r (fn-nbw-decimal-tick n 10 nil)))
    (and (not (natp n)) (<= n *fn-record-max-octets*)
         (not (equal (mv-nth 2 r) 0))))
  :rule-classes nil)

(defthm ndwt-codec-without-bound-corrupted-state
  (let* ((n 10000000000) (r (fn-nbw-decimal-tick n 10 nil)))
    (and (natp n) (not (<= n *fn-record-max-octets*))
         (not (mv-nth 0 r))))
  :rule-classes nil)

(defthm ndwt-residual-positive
  (let* ((n 4294967295) (chars '(#\7))
         (r (fn-nbw-decimal-tick n 3 chars)))
    (and (true-listp chars) (not (mv-nth 0 r))
         (equal (mv-nth 2 r) 4294967) (equal (mv-nth 3 r) 3)
         (equal (coerce (mv-nth 1 r) 'string) "2957")
         (equal (explode-nonnegative-integer (mv-nth 2 r) 10 (mv-nth 1 r))
                (explode-nonnegative-integer n 10 chars))))
  :rule-classes nil)

(defthm ndwt-residual-without-list-corrupted-state
  (let* ((chars 'bad-tail) (r (fn-nbw-decimal-tick 0 1 chars)))
    (and (not (true-listp chars))
         (not (equal (explode-nonnegative-integer (mv-nth 2 r) 10 (mv-nth 1 r))
                     (explode-nonnegative-integer 0 10 chars)))))
  :rule-classes nil)

(defthm ndwt-resume-keeps-complete-digits
  (let* ((first (fn-nbw-decimal-tick 4294967295 3 nil))
         (next (fn-nbw-decimal-tick (mv-nth 2 first) 7 (mv-nth 1 first))))
    (and (not (mv-nth 0 first)) (mv-nth 0 next)
         (equal (coerce (mv-nth 1 next) 'string) "4294967295")
         (equal (+ (mv-nth 3 first) (mv-nth 3 next)) 10)))
  :rule-classes nil)

(defthm ndwt-progress-positive
  (let* ((n 123456789012345678901234567890) (fuel 2)
         (r (fn-nbw-decimal-tick n fuel nil)))
    (and (posp n) (posp fuel) (< (mv-nth 2 r) n)
         (not (mv-nth 0 r)) (equal (mv-nth 3 r) 2)
         (equal (coerce (mv-nth 1 r) 'string) "90")))
  :rule-classes nil)

(defthm ndwt-progress-without-positive-number
  (let ((n 0) (fuel 2))
    (and (not (posp n)) (posp fuel)
         (not (< (mv-nth 2 (fn-nbw-decimal-tick n fuel nil)) n))))
  :rule-classes nil)

(defthm ndwt-progress-without-positive-fuel
  (let ((n 123) (fuel 0))
    (and (posp n) (not (posp fuel))
         (not (< (mv-nth 2 (fn-nbw-decimal-tick n fuel nil)) n))))
  :rule-classes nil)
