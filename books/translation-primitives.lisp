; Rational intermediates and character/string obligations at the bridge.
(in-package "ACL2")
(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn2-tv-ash-negative
  (implies (and (integerp count) (< count 0))
           (equal (ash i count) (floor (ifix i) (expt 2 (- count)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable ash))))

(defthm fn2-tv-ash-nonnegative
  (implies (natp count)
           (equal (ash i count) (* (ifix i) (expt 2 count))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable ash))))

(defthm fn2-tv-floor-rational-interval
  (implies (and (rationalp a) (rationalp b) (not (equal b 0)))
           (and (integerp (floor a b))
                (<= (floor a b) (/ a b))
                (< (/ a b) (+ 1 (floor a b)))))
  :rule-classes nil)

(defthm fn2-tv-ceiling-rational-interval
  (implies (and (rationalp a) (rationalp b) (not (equal b 0)))
           (and (integerp (ceiling a b))
                (< (- (ceiling a b) 1) (/ a b))
                (<= (/ a b) (ceiling a b))))
  :rule-classes nil)

(defthm fn2-tv-string-roundtrip
  (implies (stringp s) (equal (coerce (coerce s 'list) 'string) s))
  :rule-classes nil)

(defthm fn2-tv-character-roundtrip
  (implies (characterp c) (equal (code-char (char-code c)) c))
  :rule-classes nil)

(assert-event
 (and (equal (ash -3 -1) -2)
      (not (equal (ash -3 -1) (truncate -3 2)))
      (equal (floor 3 -2) -2)
      (equal (ceiling 3 -2) -1)
      (equal (expt 2 -1) 1/2)
      (not (integerp (expt 2 -1)))
      (let* ((codes (list (code-char 13) (code-char 10)))
             (s (coerce codes 'string)))
        (and (equal (coerce s 'list) codes)
             (not (equal s (coerce (list (code-char 10)) 'string)))))))
