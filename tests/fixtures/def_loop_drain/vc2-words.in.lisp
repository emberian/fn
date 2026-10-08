(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-hp-x-words-loop (i k acc pgs-mem)
  ; words I .. I+K-1 reversed onto ACC, then the whole reversed
  ; (depth_check: a loop twin)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp k) (<= (+ i k) (pgs-w-length pgs-mem)) (true-listp acc))))
  (if (zp k) (revappend acc nil)
    (fn-hp-x-words-loop (+ 1 i) (1- k) (cons (pgs-wi i pgs-mem) acc) pgs-mem)))

(defun fn-hp-x-words (i k pgs-mem)
  ; words I .. I+K-1 of the image, as a list
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp k) (<= (+ i k) (pgs-w-length pgs-mem)))
                  :verify-guards nil))
  (mbe :logic (if (zp k) nil (cons (pgs-wi i pgs-mem) (fn-hp-x-words (+ 1 i) (1- k) pgs-mem)))
       :exec (fn-hp-x-words-loop i k nil pgs-mem)))

(local
 (defthm fn-hp-x-words-loop-is
   (equal (fn-hp-x-words-loop i k acc pgs-mem)
          (revappend acc (fn-hp-x-words i k pgs-mem)))))

(verify-guards fn-hp-x-words)
