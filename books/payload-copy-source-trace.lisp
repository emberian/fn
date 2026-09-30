; PRF-1132. Large output-counter source arithmetic in the actual match copy.
; Small ring/index arithmetic, compiled frames and runtime workspaces remain
; separate obligations; this observer is not a total decoder allocation tax.
(in-package "ACL2")
(include-book "payload-profile-source-trace")

(defun-nx fn-pzc-source (d tout h w fn-zin-win)
  (let* ((d (min (nfix d) *fn-zin-window*))
         (h (min (nfix h) *fn-zin-window*))
         (tout (nfix tout))
         (negative-tout (- tout))
         (e (+ d negative-tout))
         (value
          (if (and (< 0 e) (<= e h))
              (fn-zin-win-get (+ *fn-zin-window* (- h e)) fn-zin-win)
            (let ((w (fn-zin-wrap w)))
              (fn-zin-win-get
               (fn-zin-wrap (if (<= d w) (- w d) (- (+ w *fn-zin-window*) d)))
               fn-zin-win)))))
    (cons value (list (list :negate (list tout) :source-negative-tout)
                      (list :add (list d negative-tout) :source-distance)))))

(defthm fn-pzc-source-value-projection
  (equal (car (fn-pzc-source d tout h w fn-zin-win))
         (fn-zin-source d tout h w fn-zin-win))
  :hints (("Goal" :in-theory (e/d (fn-pzc-source fn-zin-source)
                                (fn-zin-wrap fn-zin-win-get)))))

(defun-nx fn-pzc-copy (k w d tout h fn-zin-win fn-zin-out)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      (cons (list (fn-zin-wrap w) fn-zin-win fn-zin-out) nil)
    (let* ((w (fn-zin-wrap w))
           (source (fn-pzc-source d tout h w fn-zin-win))
           (o (car source))
           (fn-zin-out (fn-zin-out-append-octet o fn-zin-out))
           (fn-zin-win (fn-zin-win-put w o fn-zin-win))
           (tout (nfix tout))
           (next-tout (+ 1 tout))
           (tail (fn-pzc-copy (1- k) (fn-zin-wrap (1+ w)) d next-tout h
                              fn-zin-win fn-zin-out)))
      (cons (car tail)
            (append (cdr source)
                    (list (list :add (list 1 tout) :copy-next-tout))
                    (cdr tail))))))

(defthm fn-pzc-copy-value-and-effects-projection
  (equal (car (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out))
         (fn-zin-copy k w d tout h fn-zin-win fn-zin-out))
  :hints (("Goal" :induct (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out)
                  :in-theory (e/d (fn-pzc-copy fn-zin-copy)
                                  (fn-pzc-source fn-zin-source
                                   fn-zin-wrap fn-zin-win-get
                                   fn-zin-win-put fn-zin-out-append-octet)))))

(defthm fn-pzc-copy-counter-source-counts
  (let ((trace (cdr (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out))))
    (and (equal (fn-pzt-count :negate trace) (nfix k))
         (equal (fn-pzt-count :add trace) (* 2 (nfix k)))
         (equal (fn-pzt-count :multiply trace) 0)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out)
                  :in-theory (e/d (fn-pzc-copy fn-pzc-source)
                                  (fn-zin-wrap fn-zin-win-get
                                   fn-zin-win-put fn-zin-out-append-octet min)))))

(defun fn-pzc-operands-below (limit xs)
  (if (consp xs)
      (and (integerp (car xs)) (< (- limit) (car xs)) (< (car xs) limit)
           (fn-pzc-operands-below limit (cdr xs)))
    t))
(defun fn-pzc-trace-operands-below (limit trace)
  (if (consp trace)
      (and (fn-pzc-operands-below limit (cadar trace))
           (fn-pzc-trace-operands-below limit (cdr trace)))
    t))

(defthm fn-pzc-trace-operands-below-append
  (equal (fn-pzc-trace-operands-below limit (append left right))
         (and (fn-pzc-trace-operands-below limit left)
              (fn-pzc-trace-operands-below limit right))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pzc-source-counter-operands-width
   (implies (< (nfix tout) 4722366482869645213696)
            (fn-pzc-trace-operands-below
             4722366482869645213696 (cdr (fn-pzc-source d tout h w fn-zin-win))))
   :hints (("Goal" :in-theory (enable fn-pzc-source)))
   :rule-classes nil)
 (defthm fn-pzc-copy-counter-operands-width
   (implies (<= (+ (nfix tout) (nfix k)) 4722366482869645213696)
            (fn-pzc-trace-operands-below
             4722366482869645213696
             (cdr (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-pzc-copy k w d tout h fn-zin-win fn-zin-out)
                   :in-theory (e/d (fn-pzc-copy fn-pzc-source)
                                   (fn-zin-wrap fn-zin-win-get
                                    fn-zin-win-put fn-zin-out-append-octet))))))

(in-theory (disable fn-pzc-source fn-pzc-copy))
