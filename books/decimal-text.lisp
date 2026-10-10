; fn: the decimal renderer, once.
;
; FN-DECIMAL-TEXT renders a natural in base ten as a string (a non-natural
; renders as 0).  Every book that prints a number calls this; the per-book
; copies are retired.

(in-package "ACL2")

(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-decimal-explode-characters
   (implies (and (natp number) (character-listp accumulator))
            (character-listp
             (explode-nonnegative-integer number 10 accumulator)))))

(defun fn-decimal-text (n)
  (declare (xargs :guard t))
  (coerce (explode-nonnegative-integer (nfix n) 10 nil) 'string))

(defthm fn-decimal-text-stringp
  (stringp (fn-decimal-text n))
  :rule-classes :type-prescription)
