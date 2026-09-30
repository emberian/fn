; S7/P12 record preparation: bounded opaque-octet leaf boundary.
; Library only. No actual producer/host, physical pool or publication claim.
(in-package "ACL2")
(include-book "store-tree-codec")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(defconst *fn-hrcur-u64-bound* 18446744073709551616)

(defun fn-hrcur-field (i c)
  (declare (xargs :guard (natp i)))
  (if (consp c)
      (if (zp i) (car c) (fn-hrcur-field (1- i) (cdr c)))
    nil))

(defun fn-hrcur-widthp (c k)
  (declare (xargs :guard (natp k)))
  (if (zp k) (null c)
    (and (consp c) (fn-hrcur-widthp (cdr c) (1- k)))))

; Fixed seven-cell outer shape, never a scan of a source suffix. Fields:
; phase, remaining source, original source, counted length, prefix, capture, lease.
(defun fn-hrcur-shapep (c)
  (declare (xargs :guard t))
  (and (fn-hrcur-widthp c 7)
       (member-eq (fn-hrcur-field 0 c) '(:count :prefix :body :done :refused))
       (natp (fn-hrcur-field 3 c)) (< (fn-hrcur-field 3 c) *fn-hrcur-u64-bound*)))

(defun fn-hrcur-leaf-begin (octets capture lease)
  (declare (xargs :guard t))
  (list :count octets octets 0 nil capture lease))

; Only the count's codec-width prefix is built in a tick: at most 10 cells
; (opcode, length-of-length, up to eight length digits). No source copying.
(defun fn-hrcur-leaf-tick (c)
  (declare (xargs :guard t))
  (let ((phase (fn-hrcur-field 0 c)) (left (fn-hrcur-field 1 c)) (original (fn-hrcur-field 2 c))
        (n (nfix (fn-hrcur-field 3 c))) (prefix (fn-hrcur-field 4 c))
        (capture (fn-hrcur-field 5 c)) (lease (fn-hrcur-field 6 c)))
    (cond
     ((not (fn-hrcur-shapep c))
      (mv (list :refused :cursor) nil
          (list :refused nil nil 0 nil capture lease)))
     ((eq phase :count)
      (cond
       ((consp left)
        (if (and (fn-scc-octetp (car left))
                 (< (+ 1 n) *fn-hrcur-u64-bound*))
            (mv :continue nil
                (list :count (cdr left) original (+ 1 n) nil capture lease))
          (mv (list :refused :event) nil
              (list :refused nil nil n nil capture lease))))
       ((and (null left) (< 0 n)
             (< (+ n 2 (len (fn-scc-le-digits n))) *fn-hrcur-u64-bound*))
        (mv :continue nil
            (list :prefix nil original n
                  (cons *fn-scc-op-octets* (fn-scc-nat-octets n)) capture lease)))
       (t (mv (list :refused :event) nil
              (list :refused nil nil n nil capture lease)))))
     ((eq phase :prefix)
      (cond
       ((consp prefix)
        (if (fn-scc-octetp (car prefix))
            (mv :emit (car prefix)
                (list :prefix nil original n (cdr prefix) capture lease))
          (mv (list :refused :cursor) nil
              (list :refused nil nil n nil capture lease))))
       ((null prefix)
        (mv :continue nil (list :body original nil n nil capture lease)))
       (t (mv (list :refused :cursor) nil
              (list :refused nil nil n nil capture lease)))))
     ((eq phase :body)
      (cond
       ((consp left)
        (if (fn-scc-octetp (car left))
            (mv :emit (car left)
                (list :body (cdr left) nil n nil capture lease))
          (mv (list :refused :cursor) nil
              (list :refused nil nil n nil capture lease))))
       ((null left)
        (mv :prepared nil (list :done nil nil n nil capture lease)))
       (t (mv (list :refused :cursor) nil
              (list :refused nil nil n nil capture lease)))))
     ((eq phase :done) (mv :prepared nil c))
     (t (mv (list :refused :cursor) nil c)))))

; Proof vocabulary only: never executed by a served tick or its guard.
(defun fn-hrcur-leaf-invariantp (c)
  (declare (xargs :guard t))
  (and (fn-hrcur-shapep c)
       (let ((phase (fn-hrcur-field 0 c)) (left (fn-hrcur-field 1 c)) (original (fn-hrcur-field 2 c))
             (n (fn-hrcur-field 3 c)) (prefix (fn-hrcur-field 4 c)))
         (cond
          ((eq phase :count)
           (and (consp original) (fn-scc-octet-listp original)
                (fn-scc-octet-listp left)
                (equal (+ n (len left)) (len original))
                (< (+ (len original) 2
                      (len (fn-scc-le-digits (len original))))
                   *fn-hrcur-u64-bound*)))
          ((eq phase :prefix)
           (and (fn-scc-octet-listp prefix) (fn-scc-octet-listp original)))
          ((eq phase :body) (fn-scc-octet-listp left))
          ((eq phase :done) (null left))
          (t nil)))))

(defun fn-hrcur-leaf-rest (c)
  (declare (xargs :guard t :verify-guards nil))
  (let ((phase (fn-hrcur-field 0 c)) (left (fn-hrcur-field 1 c)) (original (fn-hrcur-field 2 c)))
    (cond
     ((eq phase :count)
      (cons *fn-scc-op-octets*
            (append (fn-scc-nat-octets (+ (nfix (fn-hrcur-field 3 c)) (len left))) original)))
     ((eq phase :prefix) (append (fn-hrcur-field 4 c) original))
     ((eq phase :body) left)
     (t nil))))

(defthm fn-hrcur-begin-refines-octet-leaf
  (implies (and (consp octets) (fn-scc-octet-listp octets)
                (< (+ (len octets) 2 (len (fn-scc-le-digits (len octets))))
                   *fn-hrcur-u64-bound*))
           (and (fn-hrcur-leaf-invariantp
                 (fn-hrcur-leaf-begin octets capture lease))
                (equal (fn-hrcur-leaf-rest
                         (fn-hrcur-leaf-begin octets capture lease))
                       (fn-scc-encode octets))))
  :hints (("Goal" :in-theory
           (e/d (fn-hrcur-leaf-invariantp fn-hrcur-leaf-rest fn-hrcur-leaf-begin
                 fn-hrcur-shapep fn-scc-program fn-scc-octets-valuep)
                (fn-scc-le-digits fn-scc-nat-octets fn-scc-encode)))))

(local
 (defun fn-hrcur-digits-ind (n k)
   (declare (xargs :guard (and (natp n) (natp k))))
   (if (zp k) nil (fn-hrcur-digits-ind (floor n 256) (1- k)))))
(local
 (defthm fn-hrcur-digits-length-bound
   (implies (and (natp n) (natp k) (< n (expt 256 k)))
            (<= (len (fn-scc-le-digits n)) k))
   :hints (("Goal" :induct (fn-hrcur-digits-ind n k)
            :in-theory (e/d (fn-scc-le-digits) (floor))))))
(local
 (defthm fn-hrcur-u64-digits-length
   (implies (and (natp n) (< n *fn-hrcur-u64-bound*))
            (< (len (fn-scc-le-digits n)) 256))
   :hints (("Goal" :use ((:instance fn-hrcur-digits-length-bound (k 8)))))))

(local
 (defthm fn-hrcur-consp-len-positive
   (implies (consp x) (< 0 (len x))) :rule-classes :linear))

(defthm fn-hrcur-leaf-tick-preserves
  (implies (fn-hrcur-leaf-invariantp c)
           (and (fn-hrcur-leaf-invariantp (mv-nth 2 (fn-hrcur-leaf-tick c)))
                (member-eq (mv-nth 0 (fn-hrcur-leaf-tick c))
                           '(:continue :emit :prepared))
                (implies (equal (mv-nth 0 (fn-hrcur-leaf-tick c)) :emit)
                         (fn-scc-octetp (mv-nth 1 (fn-hrcur-leaf-tick c))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrcur-leaf-invariantp fn-hrcur-shapep
                             fn-hrcur-leaf-tick fn-scc-octetp
                             fn-scc-nat-octets)
                            (fn-scc-le-digits)))))

(defthm fn-hrcur-leaf-tick-refines-residual
  (implies (fn-hrcur-leaf-invariantp c)
           (equal (fn-hrcur-leaf-rest c)
                  (if (equal (mv-nth 0 (fn-hrcur-leaf-tick c)) :emit)
                      (cons (mv-nth 1 (fn-hrcur-leaf-tick c))
                            (fn-hrcur-leaf-rest (mv-nth 2 (fn-hrcur-leaf-tick c))))
                    (fn-hrcur-leaf-rest (mv-nth 2 (fn-hrcur-leaf-tick c))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrcur-leaf-invariantp fn-hrcur-shapep
                             fn-hrcur-leaf-tick fn-hrcur-leaf-rest)
                            (fn-scc-le-digits fn-scc-nat-octets)))))

(defthm fn-hrcur-leaf-tick-keeps-capture-lease
  (and (equal (fn-hrcur-field 5 (mv-nth 2 (fn-hrcur-leaf-tick c))) (fn-hrcur-field 5 c))
       (equal (fn-hrcur-field 6 (mv-nth 2 (fn-hrcur-leaf-tick c))) (fn-hrcur-field 6 c)))
  :hints (("Goal" :in-theory (enable fn-hrcur-leaf-tick))))

(in-theory (disable fn-hrcur-leaf-begin fn-hrcur-leaf-tick
                    fn-hrcur-leaf-invariantp fn-hrcur-leaf-rest))
