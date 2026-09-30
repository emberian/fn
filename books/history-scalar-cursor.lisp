; PRF-1095: resumable current Store atom codec. Library component only.
(in-package "ACL2")
(include-book "store-tree-codec")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(defconst *fn-hrsc-integer-bound* (expt 256 255))

(defun fn-hrsc-codecp (n)
  (declare (xargs :guard t))
  (and (natp n) (< n *fn-hrsc-integer-bound*)))
(local
 (defthm fn-hrsc-codecp-natp
   (implies (fn-hrsc-codecp n) (natp n))
   :rule-classes :compound-recognizer))
(local
 (defthm fn-hrsc-codecp-floor
   (implies (fn-hrsc-codecp n) (fn-hrsc-codecp (floor n 256)))
   :hints (("Goal" :in-theory (e/d (fn-hrsc-codecp) (floor mod))))))
(local
 (defthm fn-hrsc-negative-bound
   (implies (and (integerp x) (fn-hrsc-codecp (- -1 x)))
            (not (< x (- *fn-hrsc-integer-bound*))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-hrsc-codecp)))))

(local
 (defthm fn-hrsc-nat-width-bound
   (implies (and (natp n) (natp k) (<= (len (fn-scc-le-digits n)) k))
            (< n (expt 256 k)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scc-u64 n k)
            :in-theory (e/d (fn-scc-le-digits fn-scc-u64 expt) (floor mod))))))
(local
 (defthm fn-hrsc-encodable-bound
   (implies (and (natp n) (< (len (fn-scc-le-digits n)) 256))
            (fn-hrsc-codecp n))
   :rule-classes ((:forward-chaining :trigger-terms ((fn-scc-le-digits n))))
   :hints (("Goal" :use ((:instance fn-hrsc-nat-width-bound (k 255)))))))

(defun fn-hrsc-field (i c)
  (declare (xargs :guard (natp i)))
  (if (consp c)
      (if (zp i) (car c) (fn-hrsc-field (1- i) (cdr c)))
    nil))

(defun fn-hrsc-widthp (c k)
  (declare (xargs :guard (natp k)))
  (if (zp k) (null c)
    (and (consp c) (fn-hrsc-widthp (cdr c) (1- k)))))

(defun fn-hrsc-prefixp (p)
  (declare (xargs :guard t))
  (or (null p)
      (and (consp p) (fn-scc-octetp (car p))
           (or (null (cdr p))
               (and (consp (cdr p)) (fn-scc-octetp (cadr p))
                    (null (cddr p)))))))

; Ten cells: phase, source reference, <=2-octet prefix, numeric remainder,
; counting remainder, width, string reference, character offset, capture, lease.
; This recognizer inspects only fixed metadata, never source content or suffix.
(defun fn-hrsc-shapep (c)
  (declare (xargs :guard t))
  (and (fn-hrsc-widthp c 10)
       (member-eq (fn-hrsc-field 0 c)
                  '(:init :count :prefix :bare :width :digits :body :done :refused))
       (fn-hrsc-prefixp (fn-hrsc-field 2 c))
       (fn-hrsc-codecp (fn-hrsc-field 3 c))
       (fn-hrsc-codecp (fn-hrsc-field 4 c))
       (natp (fn-hrsc-field 5 c)) (<= (fn-hrsc-field 5 c) 255)
       (stringp (fn-hrsc-field 6 c))
       (fn-hrsc-codecp (length (fn-hrsc-field 6 c)))
       (natp (fn-hrsc-field 7 c))
       (<= (fn-hrsc-field 7 c) (length (fn-hrsc-field 6 c)))))

(defun fn-hrsc-begin (x capture lease)
  (declare (xargs :guard t))
  (list :init x nil 0 0 0 "" 0 capture lease))

(defun fn-hrsc-tick (c)
  (declare (xargs :guard t))
  (let* ((phase (fn-hrsc-field 0 c)) (x (fn-hrsc-field 1 c))
         (p (fn-hrsc-field 2 c)) (n (fn-hrsc-field 3 c))
         (q (fn-hrsc-field 4 c)) (k (fn-hrsc-field 5 c))
         (s (fn-hrsc-field 6 c)) (i (fn-hrsc-field 7 c))
         (capture (fn-hrsc-field 8 c)) (lease (fn-hrsc-field 9 c)))
    (cond
     ((not (fn-hrsc-shapep c))
      (mv '(:refused :cursor) nil (list :refused x nil 0 0 0 "" 0 capture lease)))
     ((eq phase :init)
      (cond
       ((null x) (mv :continue nil (list :bare x '(0) 0 0 0 "" 0 capture lease)))
       ((integerp x)
        (if (if (< x 0) (< x (- *fn-hrsc-integer-bound*))
              (not (fn-hrsc-codecp x)))
            (mv '(:refused :codec-width) nil
                (list :refused x nil 0 0 0 "" 0 capture lease))
          (let ((v (if (< x 0) (- -1 x) x)))
            (mv :continue nil
                (list :count x (list (if (< x 0) 2 1)) v v 0 "" 0 capture lease)))))
       ((characterp x)
        (mv :continue nil (list :bare x (list 7 (char-code x)) 0 0 0 "" 0 capture lease)))
       ((stringp x)
        (if (fn-hrsc-codecp (length x))
            (mv :continue nil (list :count x '(3) (length x) (length x) 0 x 0 capture lease))
          (mv '(:refused :codec-width) nil (list :refused x nil 0 0 0 "" 0 capture lease))))
       ((and (symbolp x) (fn-scc-package-index (symbol-package-name x)))
        (let ((name (symbol-name x)))
          (if (fn-hrsc-codecp (length name))
              (mv :continue nil
                  (list :count x (list 4 (fn-scc-package-index (symbol-package-name x)))
                        (length name) (length name) 0 name 0 capture lease))
            (mv '(:refused :codec-width) nil (list :refused x nil 0 0 0 "" 0 capture lease)))))
       (t (mv '(:refused :atom) nil (list :refused x nil 0 0 0 "" 0 capture lease)))))
     ((eq phase :count)
      (cond ((zp q) (mv :continue nil (list :prefix x p n q k s i capture lease)))
            ((< k 255) (mv :continue nil
                           (list :count x p n (floor q 256) (+ 1 k) s i capture lease)))
            (t (mv '(:refused :codec-width) nil
                   (list :refused x nil 0 0 0 "" 0 capture lease)))))
     ((or (eq phase :prefix) (eq phase :bare))
      (if (consp p)
          (mv :emit (car p) (list phase x (cdr p) n q k s i capture lease))
        (mv :continue nil
            (list (if (eq phase :bare) :done :width) x nil n q k s i capture lease))))
     ((eq phase :width)
      (mv :emit k (list :digits x nil n q k s i capture lease)))
     ((eq phase :digits)
      (if (zp n)
          (mv :continue nil (list :body x nil n q k s i capture lease))
        (mv :emit (mod n 256)
            (list :digits x nil (floor n 256) q k s i capture lease))))
     ((eq phase :body)
      (if (< i (length s))
          (mv :emit (char-code (char s i))
              (list :body x nil n q k s (+ 1 i) capture lease))
        (mv :prepared nil (list :done x nil n q k s i capture lease))))
     ((eq phase :done) (mv :prepared nil c))
     (t (mv '(:refused :cursor) nil c)))))

; Logical proof vocabulary; none is evaluated by begin/tick or their guards.
(defun fn-hrsc-domainp (x)
  (declare (xargs :guard t))
  (and (fn-scc-atomp x)
       (cond ((stringp x) (fn-scc-nat-encodablep (length x)))
             ((and x (symbolp x)) (fn-scc-nat-encodablep (length (symbol-name x))))
             (t t))))

(defun fn-hrsc-text-rest (s i)
  (declare (xargs :guard (and (stringp s) (natp i)) :verify-guards nil))
  (fn-scc-chars-octets (nthcdr i (coerce s 'list))))

(defun fn-hrsc-invariantp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hrsc-shapep c)
       (let ((phase (fn-hrsc-field 0 c)) (n (fn-hrsc-field 3 c))
             (q (fn-hrsc-field 4 c)) (k (fn-hrsc-field 5 c)))
         (cond ((eq phase :init) (fn-hrsc-domainp (fn-hrsc-field 1 c)))
               ((eq phase :count)
                (and (< (len (fn-scc-le-digits n)) 256)
                     (equal (+ k (len (fn-scc-le-digits q))) (len (fn-scc-le-digits n)))))
               ((or (eq phase :prefix) (eq phase :width))
                (equal k (len (fn-scc-le-digits n))))
               ((eq phase :bare) (equal (fn-hrsc-field 7 c) (length (fn-hrsc-field 6 c))))
               ((eq phase :refused) nil)
               ((eq phase :done) (equal (fn-hrsc-field 7 c) (length (fn-hrsc-field 6 c))))
               (t t)))))

(defun fn-hrsc-rest (c)
  (declare (xargs :guard t :verify-guards nil))
  (let ((phase (fn-hrsc-field 0 c)) (x (fn-hrsc-field 1 c))
        (p (fn-hrsc-field 2 c)) (n (fn-hrsc-field 3 c))
        (s (fn-hrsc-field 6 c)) (i (fn-hrsc-field 7 c)))
    (cond ((eq phase :init) (fn-scc-atom-octets x))
          ((eq phase :bare) p)
          ((or (eq phase :count) (eq phase :prefix))
           (append p (fn-scc-nat-octets n) (fn-hrsc-text-rest s i)))
          ((eq phase :width) (append (fn-scc-nat-octets n) (fn-hrsc-text-rest s i)))
          ((eq phase :digits) (append (fn-scc-le-digits n) (fn-hrsc-text-rest s i)))
          ((eq phase :body) (fn-hrsc-text-rest s i))
          (t nil))))

(local
 (defthm fn-hrsc-chars-length
   (equal (len (fn-scc-chars-octets xs)) (len xs))
   :hints (("Goal" :induct (len xs) :in-theory (enable fn-scc-chars-octets)))))
(local
 (defthm fn-hrsc-chars-step
   (implies (and (natp i) (< i (len xs)))
            (equal (fn-scc-chars-octets (nthcdr i xs))
                   (cons (char-code (nth i xs))
                         (fn-scc-chars-octets (nthcdr (+ 1 i) xs)))))
   :hints (("Goal" :induct (nthcdr i xs)
            :in-theory (enable fn-scc-chars-octets)))))
(local
 (defthm fn-hrsc-chars-end
   (implies (and (natp i) (<= (len xs) i))
            (equal (fn-scc-chars-octets (nthcdr i xs)) nil))
   :hints (("Goal" :induct (nthcdr i xs)
            :in-theory (enable fn-scc-chars-octets)))))
(local
 (defthm fn-hrsc-digits-step
   (implies (and (natp n) (< 0 n))
            (equal (fn-scc-le-digits n)
                   (cons (mod n 256) (fn-scc-le-digits (floor n 256)))))
   :hints (("Goal" :expand (fn-scc-le-digits n)))))

(defthm fn-hrsc-begin-refines-atom-codec
  (implies (fn-hrsc-domainp x)
           (and (fn-hrsc-invariantp (fn-hrsc-begin x capture lease))
                (equal (fn-hrsc-rest (fn-hrsc-begin x capture lease))
                       (fn-scc-atom-octets x))))
  :hints (("Goal" :in-theory (e/d (fn-hrsc-begin fn-hrsc-rest fn-hrsc-invariantp
                                    fn-hrsc-shapep)
                                   (fn-hrsc-domainp fn-scc-atom-octets)))))

(defthm fn-hrsc-tick-preserves-capture-lease
  (and (equal (fn-hrsc-field 8 (mv-nth 2 (fn-hrsc-tick c))) (fn-hrsc-field 8 c))
       (equal (fn-hrsc-field 9 (mv-nth 2 (fn-hrsc-tick c))) (fn-hrsc-field 9 c)))
  :hints (("Goal" :in-theory (e/d (fn-hrsc-tick) (fn-hrsc-shapep)))))

(defthm fn-hrsc-tick-preserves-invariant
  (implies (fn-hrsc-invariantp c)
           (fn-hrsc-invariantp (mv-nth 2 (fn-hrsc-tick c))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrsc-negative-bound (x (fn-hrsc-field 1 c))))
           :in-theory (e/d (fn-hrsc-invariantp fn-hrsc-tick
                              fn-hrsc-domainp fn-scc-atomp fn-scc-nat-encodablep
                              fn-scc-package-index)
                             (fn-scc-le-digits floor mod char-code fn-hrsc-codecp)))))

(defthm fn-hrsc-tick-refines-atom-residual
  (implies (fn-hrsc-invariantp c)
           (let ((v (mv-nth 0 (fn-hrsc-tick c)))
                 (b (mv-nth 1 (fn-hrsc-tick c)))
                 (next (mv-nth 2 (fn-hrsc-tick c))))
             (and (member-eq v '(:continue :emit :prepared))
                  (equal (fn-hrsc-rest c)
                         (if (eq v :emit) (cons b (fn-hrsc-rest next))
                           (fn-hrsc-rest next)))
                  (implies (eq v :prepared) (equal (fn-hrsc-rest next) nil)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrsc-negative-bound (x (fn-hrsc-field 1 c))))
           :in-theory (e/d (fn-hrsc-invariantp fn-hrsc-tick fn-hrsc-rest
                              fn-hrsc-shapep fn-hrsc-domainp fn-scc-atomp
                              fn-scc-nat-encodablep fn-scc-atom-octets
                              fn-scc-string-octets fn-scc-nat-octets
                              fn-hrsc-text-rest fn-scc-package-index char)
                             (fn-hrsc-codecp fn-scc-le-digits floor mod char-code fn-scc-chars-octets)))))

(defthm fn-hrsc-tick-emits-one-octet
  (implies (eq (mv-nth 0 (fn-hrsc-tick c)) :emit)
           (fn-scc-octetp (mv-nth 1 (fn-hrsc-tick c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrsc-tick fn-hrsc-shapep fn-scc-octetp)
                             (fn-hrsc-codecp floor mod char-code)))))

(defun fn-hrsc-work (c)
  (declare (xargs :guard t :verify-guards nil))
  (let ((phase (fn-hrsc-field 0 c))
        (p (len (fn-hrsc-field 2 c)))
        (d (len (fn-scc-le-digits (fn-hrsc-field 3 c))))
        (q (len (fn-scc-le-digits (fn-hrsc-field 4 c))))
        (text (len (fn-hrsc-text-rest (fn-hrsc-field 6 c) (fn-hrsc-field 7 c)))))
    (cond ((eq phase :init) (+ 10 (* 2 (len (fn-scc-atom-octets (fn-hrsc-field 1 c))))))
          ((eq phase :count) (+ p d text q 5))
          ((eq phase :prefix) (+ p d text 4))
          ((eq phase :width) (+ d text 3))
          ((eq phase :digits) (+ d text 2))
          ((eq phase :body) (+ text 1))
          ((eq phase :bare) (+ p 1))
          (t 0))))

(local
 (defthm fn-hrsc-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-hrsc-len-nthcdr
   (implies (and (natp i) (<= i (len xs)))
            (equal (len (nthcdr i xs)) (- (len xs) i)))
   :hints (("Goal" :induct (nthcdr i xs)))))

(defthm fn-hrsc-tick-makes-progress
  (implies (and (fn-hrsc-invariantp c)
                (not (eq (fn-hrsc-field 0 c) :done)))
           (< (fn-hrsc-work (mv-nth 2 (fn-hrsc-tick c)))
              (fn-hrsc-work c)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrsc-negative-bound (x (fn-hrsc-field 1 c))))
           :in-theory (e/d (fn-hrsc-work fn-hrsc-invariantp fn-hrsc-tick
                              fn-hrsc-shapep fn-hrsc-domainp fn-scc-atomp
                              fn-scc-nat-encodablep fn-scc-atom-octets
                              fn-scc-string-octets fn-scc-nat-octets
                              fn-hrsc-text-rest fn-scc-package-index char)
                             (fn-hrsc-codecp fn-scc-le-digits floor mod char-code fn-scc-chars-octets)))))

(in-theory (disable fn-hrsc-codecp fn-hrsc-field fn-hrsc-widthp fn-hrsc-prefixp
                    fn-hrsc-shapep fn-hrsc-begin fn-hrsc-tick fn-hrsc-domainp
                    fn-hrsc-text-rest fn-hrsc-invariantp fn-hrsc-rest fn-hrsc-work))
