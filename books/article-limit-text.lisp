; Bounded decimal syntax for the public article-limit startup option.
; Admission belongs to the actual upload/profile consumer.
(in-package "ACL2")

(defun fn2-article-limit-decimal-aux (text index value)
 (declare (xargs :measure (nfix (- (length text) (nfix index)))
  :guard (and (stringp text) (natp index) (<= index (length text)) (natp value))))
 (if (>= (nfix index) (length text))
     (if (unsigned-byte-p 32 value) value nil)
   (let ((digit (- (char-code (char text (nfix index))) 48)))
    (if (and (<= 0 digit) (<= digit 9))
        (fn2-article-limit-decimal-aux text (+ 1 (nfix index)) (+ (* 10 value) digit))
      nil))))
(defun fn2-article-limit-decimal (text)
 (declare (xargs :guard t))
 (if (and (stringp text) (< 0 (length text)) (<= (length text) 10))
     (fn2-article-limit-decimal-aux text 0 0) nil))

