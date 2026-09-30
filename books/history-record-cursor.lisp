; S7/P12 record preparation: bounded resident tree/byte census and word boundaries.
; Library only. No actual producer/host, physical pool or publication claim.
(in-package "ACL2")
(include-book "store-tree-codec")
(include-book "history-pages-words")
(include-book "history-scalar-cursor")
(include-book "history-decode-nodes")
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
                             fn-hrcur-leaf-tick fn-scc-octetp fn-scc-octet-listp
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


; The accumulator holds at most seven bytes, not a growing encoded row.
(defun fn-hrcur-wordp (k w)
  (declare (xargs :guard t))
  (and (natp k) (< k 8) (natp w) (< w (expt 256 k))))

(defun fn-hrcur-word-push (octet k w)
  (declare (xargs :guard t))
  (if (and (fn-scc-octetp octet) (fn-hrcur-wordp k w))
      (let ((next (+ w (* octet (expt 256 k)))))
        (if (equal k 7) (mv :emit next 0 0)
          (mv :continue nil (+ 1 k) next)))
    (mv (list :refused :word-cursor) nil 0 0)))

(defun fn-hrcur-word-finish (k w)
  (declare (xargs :guard t))
  (cond ((not (fn-hrcur-wordp k w))
         (mv (list :refused :word-cursor) nil 0 0))
        ((equal k 0) (mv :prepared nil 0 0))
        (t (mv :emit w 0 0))))

(local
 (defthm fn-hrcur-unle-is-le-value
   (equal (adt-unle (len b) b) (fn-scc-le-value b))
   :hints (("Goal" :induct (len b) :in-theory (enable adt-unle fn-scc-le-value)))))

(local
 (defthm fn-hrcur-le-value-append
   (equal (fn-scc-le-value (append a b))
          (+ (fn-scc-le-value a) (* (expt 256 (len a)) (fn-scc-le-value b))))
   :hints (("Goal" :induct (len a) :in-theory (enable fn-scc-le-value)))))

(defthm fn-hrcur-word-push-preserves
  (implies (and (fn-scc-octetp octet) (fn-hrcur-wordp k w))
           (and (member-eq (mv-nth 0 (fn-hrcur-word-push octet k w))
                           '(:continue :emit))
                (fn-hrcur-wordp (mv-nth 2 (fn-hrcur-word-push octet k w))
                               (mv-nth 3 (fn-hrcur-word-push octet k w)))
                (implies (equal (mv-nth 0 (fn-hrcur-word-push octet k w)) :emit)
                         (unsigned-byte-p 64 (mv-nth 1 (fn-hrcur-word-push octet k w))))))
  :hints (("Goal" :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3)
                          (equal k 4) (equal k 5) (equal k 6) (equal k 7))
           :in-theory (enable fn-hrcur-wordp fn-hrcur-word-push fn-scc-octetp))))

(defthm fn-hrcur-word-push-refines-partial
  (implies (and (equal k (len prefix)) (< k 7)
                (equal w (adt-unle k prefix)) (fn-hrcur-wordp k w)
                (fn-scc-octetp octet))
           (and (equal (mv-nth 0 (fn-hrcur-word-push octet k w)) :continue)
                (equal (mv-nth 2 (fn-hrcur-word-push octet k w)) (+ 1 k))
                (equal (mv-nth 3 (fn-hrcur-word-push octet k w))
                       (adt-unle (+ 1 k) (append prefix (list octet))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-unle-is-le-value (b prefix))
                 (:instance fn-hrcur-unle-is-le-value (b (append prefix (list octet)))))
           :expand ((fn-scc-le-value (list octet)))
           :in-theory (e/d (fn-hrcur-word-push fn-scc-octetp)
                            (adt-unle fn-scc-le-value expt floor mod
                             fn-hrcur-unle-is-le-value)))))

(defthm fn-hrcur-word-push-refines-pack8
  (implies (and (equal (len prefix) 7)
                (equal w (adt-unle 7 prefix)) (fn-hrcur-wordp 7 w)
                (fn-scc-octetp octet))
           (and (equal (mv-nth 0 (fn-hrcur-word-push octet 7 w)) :emit)
                (equal (mv-nth 1 (fn-hrcur-word-push octet 7 w))
                       (car (fn-hp-pack8 1 (append prefix (list octet)))))
                (equal (mv-nth 2 (fn-hrcur-word-push octet 7 w)) 0)
                (equal (mv-nth 3 (fn-hrcur-word-push octet 7 w)) 0)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-unle-is-le-value (b prefix))
                 (:instance fn-hrcur-unle-is-le-value (b (append prefix (list octet)))))
           :expand ((fn-scc-le-value (list octet)))
           :in-theory (e/d (fn-hrcur-word-push fn-hp-pack8 fn-scc-octetp)
                            (adt-unle fn-scc-le-value floor mod
                             fn-hrcur-unle-is-le-value)))))

(local
 (defthm fn-hrcur-le-value-zeros
   (equal (fn-scc-le-value (adt-zeros n)) 0)
   :hints (("Goal" :induct (adt-zeros n)
            :in-theory (e/d (fn-scc-le-value adt-zeros) (floor mod))))))

(local
 (defthm fn-hrcur-unle-zero-pad
   (implies (and (natp k) (<= k 8) (equal (len prefix) k))
            (equal (adt-unle 8 (append prefix (adt-zeros (- 8 k))))
                   (adt-unle k prefix)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-unle-is-le-value (b prefix))
                  (:instance fn-hrcur-unle-is-le-value
                             (b (append prefix (adt-zeros (- 8 k))))))
            :in-theory (disable adt-unle fn-scc-le-value adt-zeros
                                fn-hrcur-unle-is-le-value floor mod)))))

(defthm fn-hrcur-word-finish-refines-pad8
  (implies (and (equal k (len prefix)) (< 0 k)
                (equal w (adt-unle k prefix)) (fn-hrcur-wordp k w))
           (and (equal (mv-nth 0 (fn-hrcur-word-finish k w)) :emit)
                (equal (mv-nth 1 (fn-hrcur-word-finish k w))
                       (car (fn-hp-pack8 1
                                        (append prefix (adt-zeros (- 8 k))))))
                (equal (mv-nth 2 (fn-hrcur-word-finish k w)) 0)
                (equal (mv-nth 3 (fn-hrcur-word-finish k w)) 0)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-unle-zero-pad))
           :expand ((:free (bs) (fn-hp-pack8 1 bs)))
           :in-theory (e/d (fn-hrcur-word-finish)
                            (adt-unle fn-scc-le-value adt-zeros fn-hp-pack8
                             fn-hrcur-unle-is-le-value fn-hrcur-unle-zero-pad)))))

(in-theory (disable fn-hrcur-wordp fn-hrcur-word-push fn-hrcur-word-finish))

; General tree traversal emits source-reference descriptors. Atom descriptor
; expansion belongs to the scalar cursor; it is not whole-atom byte emission.
(defun fn-hrcur-tree-begin (tree capture lease)
  (declare (xargs :guard t))
  (list (list (list :tree tree)) capture lease))

(defun fn-hrcur-tree-tick (c)
  (declare (xargs :guard t))
  (let* ((todo (fn-hrcur-field 0 c))
         (capture (fn-hrcur-field 1 c)) (lease (fn-hrcur-field 2 c))
         (task (if (consp todo) (car todo) nil))
         (tail (if (consp todo) (cdr todo) nil))
         (tag (fn-hrcur-field 0 task)) (x (fn-hrcur-field 1 task)))
    (cond
     ((not (fn-hrcur-widthp c 3))
      (mv (list :refused :tree-cursor) nil (list nil capture lease)))
     ((null todo) (mv :prepared nil c))
     ((not (consp todo))
      (mv (list :refused :tree-cursor) nil (list nil capture lease)))
     ((and (eq tag :tree) (fn-hrcur-widthp task 2))
      (if (consp x)
          (mv :continue nil
              (list (cons (list :scan x x 0) tail) capture lease))
        (mv :emit (list :atom x) (list tail capture lease))))
     ((and (eq tag :non-octets) (fn-hrcur-widthp task 2))
      (if (consp x)
          (mv :continue nil
              (list (cons (list :tree (car x))
                          (cons (list (if (fn-scc-octetp (car x)) :non-octets :tree) (cdr x))
                                (cons (list :byte *fn-scc-op-cons*) tail)))
                    capture lease))
        (mv :emit (list :atom x) (list tail capture lease))))
     ((and (eq tag :byte) (fn-hrcur-widthp task 2) (fn-scc-octetp x))
      (mv :emit (list :byte x) (list tail capture lease)))
     ((and (eq tag :scan) (fn-hrcur-widthp task 4)
           (consp x) (natp (fn-hrcur-field 3 task))
           (< (fn-hrcur-field 3 task) *fn-hrcur-u64-bound*))
      (let ((left (fn-hrcur-field 2 task)) (n (fn-hrcur-field 3 task)))
        (cond
         ((and (consp left) (fn-scc-octetp (car left)))
          (if (< (+ 1 n) *fn-hrcur-u64-bound*)
              (mv :continue nil
                  (list (cons (list :scan x (cdr left) (+ 1 n)) tail) capture lease))
            (mv (list :refused :event) nil (list nil capture lease))))
         ((null left)
          (mv :emit (list :octets x n) (list tail capture lease)))
         (t (mv :continue nil
                (list (cons (list :tree (car x))
                            (cons (list (if (< 0 n) :non-octets :tree) (cdr x))
                                  (cons (list :byte *fn-scc-op-cons*) tail)))
                      capture lease))))))
     (t (mv (list :refused :tree-cursor) nil (list nil capture lease))))))

; No recognizer/residual below is executed by tree begin/tick or its guard.
(defun fn-hrcur-tree-domainp (x)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count x)))
  (if (consp x)
      (and (< (len x) *fn-hrcur-u64-bound*)
           (fn-hrcur-tree-domainp (car x)) (fn-hrcur-tree-domainp (cdr x)))
    (fn-hrsc-domainp x)))

(defthm fn-hrcur-tree-domain-is-treep
  (implies (fn-hrcur-tree-domainp x) (fn-scc-treep x))
  :hints (("Goal" :induct (fn-hrcur-tree-domainp x)
           :in-theory (enable fn-scc-treep fn-hrsc-domainp))))

(defun fn-hrcur-tail (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n) x
    (if (consp x) (fn-hrcur-tail (1- n) (cdr x)) nil)))

(defun fn-hrcur-prefix (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil
    (cons (if (consp x) (car x) nil)
          (fn-hrcur-prefix (1- n) (if (consp x) (cdr x) nil)))))

(defthm fn-hrcur-tail-is-nthcdr
  (implies (natp n) (equal (fn-hrcur-tail n x) (nthcdr n x)))
  :hints (("Goal" :induct (fn-hrcur-tail n x) :in-theory (enable nthcdr))))

(defthm fn-hrcur-prefix-is-take
  (implies (natp n) (equal (fn-hrcur-prefix n x) (take n x)))
  :hints (("Goal" :induct (fn-hrcur-prefix n x) :in-theory (enable take))))

(defun fn-hrcur-tree-taskp (task)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tag (fn-hrcur-field 0 task)) (x (fn-hrcur-field 1 task)))
    (cond
     ((eq tag :tree)
      (and (fn-hrcur-widthp task 2) (fn-hrcur-tree-domainp x)))
     ((eq tag :non-octets)
      (and (fn-hrcur-widthp task 2) (fn-hrcur-tree-domainp x)
           (not (fn-scc-octet-listp x))))
     ((eq tag :byte)
      (and (fn-hrcur-widthp task 2) (fn-scc-octetp x)))
     ((eq tag :scan)
      (let ((left (fn-hrcur-field 2 task)) (n (fn-hrcur-field 3 task)))
        (and (fn-hrcur-widthp task 4) (consp x) (fn-hrcur-tree-domainp x)
             (natp n) (<= n (len x)) (< (len x) *fn-hrcur-u64-bound*)
             (equal left (fn-hrcur-tail n x)) (fn-scc-octet-listp (fn-hrcur-prefix n x)))))
     (t nil))))

(defun fn-hrcur-tree-todop (todo)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp todo)
      (and (fn-hrcur-tree-taskp (car todo)) (fn-hrcur-tree-todop (cdr todo)))
    (null todo)))

(defun fn-hrcur-tree-invariantp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hrcur-widthp c 3) (fn-hrcur-tree-todop (fn-hrcur-field 0 c))))

(defun fn-hrcur-tree-task-rest (task)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tag (fn-hrcur-field 0 task)) (x (fn-hrcur-field 1 task)))
    (if (eq tag :byte) (list x) (fn-scc-program x))))

(defun fn-hrcur-tree-rest (todo)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp todo)
      (append (fn-hrcur-tree-task-rest (car todo)) (fn-hrcur-tree-rest (cdr todo)))
    nil))

(defun fn-hrcur-descriptor-octets (descriptor)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tag (fn-hrcur-field 0 descriptor)) (x (fn-hrcur-field 1 descriptor)))
    (cond ((eq tag :atom) (fn-scc-atom-octets x))
          ((eq tag :octets)
           (cons *fn-scc-op-octets*
                 (append (fn-scc-nat-octets (nfix (fn-hrcur-field 2 descriptor))) x)))
          ((eq tag :byte) (list x))
          (t nil))))

; Byte-list recognizers here are proof facts, not runtime suffix scans.
(local
 (defthm fn-hrcur-octet-listp-append
   (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
            (fn-scc-octet-listp (append a b)))
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))))

(local
 (defun fn-hrcur-prefix-ind (n x)
   (declare (xargs :guard (natp n)))
   (if (or (zp n) (not (consp x))) nil
     (fn-hrcur-prefix-ind (1- n) (cdr x)))))

(local
 (defthm fn-hrcur-prefix-reconstruct
   (implies (and (natp n) (<= n (len x)))
            (equal (append (take n x) (nthcdr n x)) x))
   :hints (("Goal" :induct (fn-hrcur-prefix-ind n x)
            :in-theory (enable take nthcdr)))))

(local
 (defthm fn-hrcur-len-take
   (equal (len (take n x)) (nfix n))
   :hints (("Goal" :induct (take n x) :in-theory (enable take)))))

(local
 (defthm fn-hrcur-counted-prefix-octets
   (implies (and (natp n) (<= n (len x))
                 (fn-scc-octet-listp (take n x))
                 (equal (nthcdr n x) nil))
            (and (equal (len x) n) (fn-scc-octet-listp x)))
   :hints (("Goal" :use ((:instance fn-hrcur-prefix-reconstruct))
            :in-theory (disable fn-hrcur-prefix-reconstruct take nthcdr
                                fn-scc-octet-listp)))))

(local
 (defthm fn-hrcur-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-hrcur-bad-head-not-octets
   (implies (or (and (consp left) (not (fn-scc-octetp (car left))))
                (and (not (consp left)) left))
            (not (fn-scc-octet-listp left)))
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp fn-scc-octetp)))))

(local
 (defthm fn-hrcur-scan-rejection-not-octets
   (implies (and (equal left (nthcdr n x))
                 (or (and (consp left) (not (fn-scc-octetp (car left))))
                     (and (not (consp left)) left)))
            (not (fn-scc-octet-listp x)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-octet-listp-facts)
                  (:instance fn-hrcur-bad-head-not-octets))
            :in-theory (disable nthcdr fn-scc-octet-listp fn-scc-octetp
                                fn-scc-octet-listp-facts
                                fn-hrcur-bad-head-not-octets)))))

(local
 (defthm fn-hrcur-nthcdr-consp-length
   (implies (and (natp n) (consp (nthcdr n x))) (< n (len x)))
   :rule-classes :linear
   :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr)))))

(local
 (defthm fn-hrcur-nthcdr-at-end-not-consp
   (implies (and (natp n) (<= (len x) n))
            (not (consp (nthcdr n x))))
   :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr)))))

(defthm fn-hrcur-tree-tick-refines-residual
  (implies (fn-hrcur-tree-invariantp c)
           (equal (fn-hrcur-tree-rest (fn-hrcur-field 0 c))
                  (if (equal (mv-nth 0 (fn-hrcur-tree-tick c)) :emit)
                      (append (fn-hrcur-descriptor-octets
                               (mv-nth 1 (fn-hrcur-tree-tick c)))
                              (fn-hrcur-tree-rest
                               (fn-hrcur-field 0 (mv-nth 2 (fn-hrcur-tree-tick c)))))
                    (fn-hrcur-tree-rest
                     (fn-hrcur-field 0 (mv-nth 2 (fn-hrcur-tree-tick c)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrcur-tree-invariantp fn-hrcur-tree-todop
                             fn-hrcur-tree-taskp fn-hrcur-tree-tick
                             fn-hrcur-tree-rest fn-hrcur-tree-task-rest
                             fn-hrcur-descriptor-octets fn-scc-program
                             fn-scc-octets-valuep)
                            (fn-scc-atom-octets fn-scc-treep fn-scc-nat-octets
                             fn-hrcur-tree-domainp fn-scc-octet-listp take nthcdr)))))

(local
 (defthm fn-hrcur-nthcdr-successor
   (implies (natp n) (equal (cdr (nthcdr n x)) (nthcdr (+ 1 n) x)))
   :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr)))))

(local
 (defthm fn-hrcur-singleton-octets
   (implies (fn-scc-octetp byte) (fn-scc-octet-listp (list byte)))
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp fn-scc-octetp)))))

(local
 (defthm fn-hrcur-count-prefix-extends
   (implies (and (natp n) (fn-scc-octet-listp (take n x))
                 (consp (nthcdr n x)) (fn-scc-octetp (car (nthcdr n x))))
            (fn-scc-octet-listp (take (+ 1 n) x)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hp-take-plus (m n) (k 1) (b x))
                  (:instance fn-hrcur-octet-listp-append
                             (a (take n x)) (b (list (car (nthcdr n x))))))
            :expand ((:free (xs) (take 0 xs)) (take 1 (nthcdr n x))
                     (fn-scc-octet-listp (list (car (nthcdr n x)))))
            :in-theory (disable take nthcdr fn-scc-octet-listp
                                fn-hrcur-octet-listp-append
                                fn-hrcur-nthcdr-successor)))))

(defun fn-hrcur-descriptorp (d)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tag (fn-hrcur-field 0 d)) (x (fn-hrcur-field 1 d)))
    (cond ((eq tag :atom) (and (fn-hrcur-widthp d 2) (fn-hrsc-domainp x)))
          ((eq tag :octets)
           (and (fn-hrcur-widthp d 3) (consp x) (fn-scc-octet-listp x)
                (equal (fn-hrcur-field 2 d) (len x))
                (< (len x) *fn-hrcur-u64-bound*)))
          ((eq tag :byte) (and (fn-hrcur-widthp d 2) (fn-scc-octetp x)))
          (t nil))))

(defthm fn-hrcur-tree-begin-refines-encode
  (implies (fn-hrcur-tree-domainp tree)
           (and (fn-hrcur-tree-invariantp (fn-hrcur-tree-begin tree capture lease))
                (equal (fn-hrcur-tree-rest
                         (fn-hrcur-field 0 (fn-hrcur-tree-begin tree capture lease)))
                       (fn-scc-encode tree))))
  :hints (("Goal" :in-theory
           (e/d (fn-hrcur-tree-begin fn-hrcur-tree-invariantp fn-hrcur-tree-todop
                 fn-hrcur-tree-taskp fn-hrcur-tree-rest fn-hrcur-tree-task-rest)
                (fn-scc-encode fn-scc-program fn-hrcur-tree-domainp)))))

(local (defthm fn-hrcur-take-zero (equal (take 0 x) nil)
         :hints (("Goal" :in-theory (enable take)))))
(local (defthm fn-hrcur-nthcdr-zero (equal (nthcdr 0 x) x)
         :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-hrcur-count-prefix-head-octet
   (implies (and (natp n) (< 0 n) (consp x)
                 (fn-scc-octet-listp (take n x)))
            (fn-scc-octetp (car x)))
   :hints (("Goal" :do-not-induct t
            :expand ((take n x))
            :in-theory (disable take nthcdr)))))

(local
 (defthm fn-hrcur-non-octets-tail
   (implies (and (consp x) (not (fn-scc-octet-listp x))
                 (fn-scc-octetp (car x)))
            (not (fn-scc-octet-listp (cdr x))))
   :hints (("Goal" :expand ((fn-scc-octet-listp x))
            :in-theory (disable fn-scc-octet-listp)))))

(defthm fn-hrcur-tree-tick-preserves
  (implies (fn-hrcur-tree-invariantp c)
           (and (fn-hrcur-tree-invariantp (mv-nth 2 (fn-hrcur-tree-tick c)))
                (member-eq (mv-nth 0 (fn-hrcur-tree-tick c))
                           '(:continue :emit :prepared))
                (implies (equal (mv-nth 0 (fn-hrcur-tree-tick c)) :emit)
                         (fn-hrcur-descriptorp (mv-nth 1 (fn-hrcur-tree-tick c))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrcur-tree-tick fn-hrcur-tree-invariantp
                             fn-hrcur-tree-taskp fn-hrcur-tree-todop
                             fn-hrcur-descriptorp fn-hrcur-tree-domainp)
                            (fn-scc-atomp fn-scc-treep fn-scc-octet-listp
                             take nthcdr)))))

(defthm fn-hrcur-tree-tick-keeps-capture-lease
  (and (equal (fn-hrcur-field 1 (mv-nth 2 (fn-hrcur-tree-tick c)))
              (fn-hrcur-field 1 c))
       (equal (fn-hrcur-field 2 (mv-nth 2 (fn-hrcur-tree-tick c)))
              (fn-hrcur-field 2 c)))
  :hints (("Goal" :in-theory (enable fn-hrcur-tree-tick))))

(in-theory (disable fn-hrcur-tree-begin fn-hrcur-tree-tick fn-hrcur-tree-domainp
                    fn-hrcur-tree-taskp fn-hrcur-tree-todop fn-hrcur-tree-invariantp
                    fn-hrcur-tree-rest fn-hrcur-tree-task-rest
                    fn-hrcur-descriptorp fn-hrcur-descriptor-octets))

; Six cells: phase, suspended descriptor traversal, active scalar/leaf cursor,
; captured root token, lease, reserved. Every tick has one bounded subaction.
(defun fn-hrcur-byte-begin (source capture lease)
  (declare (xargs :guard t))
  (if (and (fn-hrcur-widthp source 2) (eq (car source) :resident))
      (list :tree (fn-hrcur-tree-begin (cadr source) capture lease) nil capture lease nil)
    (list :refused nil nil capture lease nil)))

(defun fn-hrcur-byte-tick (c)
  (declare (xargs :guard t))
  (let ((phase (fn-hrcur-field 0 c)) (tree (fn-hrcur-field 1 c))
        (active (fn-hrcur-field 2 c)) (capture (fn-hrcur-field 3 c))
        (lease (fn-hrcur-field 4 c)))
    (cond
     ((not (fn-hrcur-widthp c 6))
      (mv '(:refused :byte-cursor) nil (list :refused nil nil capture lease nil)))
     ((eq phase :tree)
      (mv-let (verdict d next) (fn-hrcur-tree-tick tree)
        (cond
         ((eq verdict :continue) (mv :continue nil (list :tree next nil capture lease nil)))
         ((eq verdict :prepared) (mv :prepared nil (list :done next nil capture lease nil)))
         ((eq verdict :emit)
          (let ((tag (fn-hrcur-field 0 d)) (x (fn-hrcur-field 1 d))
                (n (fn-hrcur-field 2 d)))
            (cond
             ((eq tag :byte) (mv :emit x (list :tree next nil capture lease nil)))
             ((eq tag :atom)
              (mv :continue nil
                  (list :scalar next (fn-hrsc-begin x capture lease) capture lease nil)))
             ((and (eq tag :octets) (natp n) (< n *fn-hrcur-u64-bound*))
              (mv :continue nil
                  (list :leaf next
                        (list :prefix nil x n (cons 6 (fn-scc-nat-octets n)) capture lease)
                        capture lease nil)))
             (t (mv '(:refused :descriptor) nil
                    (list :refused nil nil capture lease nil))))))
         (t (mv verdict nil (list :refused nil nil capture lease nil))))))
     ((or (eq phase :scalar) (eq phase :leaf))
      (mv-let (verdict byte next)
        (if (eq phase :scalar) (fn-hrsc-tick active) (fn-hrcur-leaf-tick active))
        (cond
         ((eq verdict :prepared) (mv :continue nil (list :tree tree nil capture lease nil)))
         ((or (eq verdict :continue) (eq verdict :emit))
          (mv verdict byte (list phase tree next capture lease nil)))
         (t (mv verdict nil (list :refused nil nil capture lease nil))))))
     ((eq phase :done) (mv :prepared nil c))
     (t (mv '(:refused :byte-cursor) nil c)))))

(defun fn-hrcur-byte-invariantp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hrcur-widthp c 6)
       (fn-hrcur-tree-invariantp (fn-hrcur-field 1 c))
       (let ((phase (fn-hrcur-field 0 c)) (active (fn-hrcur-field 2 c)))
         (cond ((eq phase :tree) (null active))
               ((eq phase :scalar) (fn-hrsc-invariantp active))
               ((eq phase :leaf) (fn-hrcur-leaf-invariantp active))
               ((eq phase :done) (null (fn-hrcur-field 0 (fn-hrcur-field 1 c))))
               (t nil)))))

(defun fn-hrcur-byte-rest (c)
  (declare (xargs :guard t :verify-guards nil))
  (append (cond ((eq (fn-hrcur-field 0 c) :scalar) (fn-hrsc-rest (fn-hrcur-field 2 c)))
                ((eq (fn-hrcur-field 0 c) :leaf) (fn-hrcur-leaf-rest (fn-hrcur-field 2 c)))
                (t nil))
          (fn-hrcur-tree-rest (fn-hrcur-field 0 (fn-hrcur-field 1 c)))))

(local
 (defthm fn-hrcur-hrsc-field-same
   (implies (natp i) (equal (fn-hrsc-field i c) (fn-hrcur-field i c)))
   :hints (("Goal" :induct (fn-hrcur-field i c)
            :in-theory (enable fn-hrsc-field)))))

(local
 (defthm fn-hrcur-leaf-prepared-empty
   (implies (and (fn-hrcur-leaf-invariantp c)
                 (eq (mv-nth 0 (fn-hrcur-leaf-tick c)) :prepared))
            (equal (fn-hrcur-leaf-rest c) nil))
   :hints (("Goal" :in-theory
            (e/d (fn-hrcur-leaf-invariantp fn-hrcur-leaf-rest
                    fn-hrcur-leaf-tick fn-hrcur-shapep)
                 (fn-hrcur-leaf-tick-refines-residual fn-hrcur-leaf-tick-preserves))))))

(local
 (defthm fn-hrcur-tree-prepared-empty
   (implies (and (fn-hrcur-tree-invariantp c)
                 (eq (mv-nth 0 (fn-hrcur-tree-tick c)) :prepared))
            (and (equal (fn-hrcur-field 0 c) nil)
                 (equal (fn-hrcur-field 0 (mv-nth 2 (fn-hrcur-tree-tick c))) nil)))
   :hints (("Goal" :in-theory
            (e/d (fn-hrcur-tree-invariantp fn-hrcur-tree-tick)
                 (fn-hrcur-tree-tick-refines-residual fn-hrcur-tree-tick-preserves))))))

(defthm fn-hrcur-byte-begin-refines-encode
  (implies (fn-hrcur-tree-domainp row)
           (and (fn-hrcur-byte-invariantp (fn-hrcur-byte-begin (list :resident row) capture lease))
                (equal (fn-hrcur-byte-rest (fn-hrcur-byte-begin (list :resident row) capture lease))
                       (fn-scc-encode row))))
  :hints (("Goal" :in-theory
           (e/d (fn-hrcur-byte-begin fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                 fn-hrcur-tree-begin fn-hrcur-tree-rest fn-hrcur-tree-task-rest
                 fn-hrcur-tree-invariantp fn-hrcur-tree-todop fn-hrcur-tree-taskp)
                (fn-scc-encode fn-scc-program)))))


(local
 (defthm fn-hrcur-scalar-verdict
   (implies (fn-hrsc-invariantp c)
            (member-eq (mv-nth 0 (fn-hrsc-tick c)) '(:continue :emit :prepared)))
   :hints (("Goal" :use fn-hrsc-tick-refines-atom-residual
            :in-theory (disable fn-hrsc-tick-refines-atom-residual fn-hrsc-rest)))))
(local
 (defthm fn-hrcur-leaf-prefix-ready
   (implies (and (consp x) (fn-scc-octet-listp x)
                 (natp n) (< n *fn-hrcur-u64-bound*))
            (fn-hrcur-leaf-invariantp
             (list :prefix nil x n (cons 6 (fn-scc-nat-octets n)) capture lease)))
   :hints (("Goal" :in-theory
            (e/d (fn-hrcur-leaf-invariantp fn-hrcur-shapep fn-scc-nat-octets
                  fn-scc-octet-listp fn-scc-octetp)
                 (fn-scc-le-digits))))))

(defthm fn-hrcur-byte-tick-preserves
  (implies (fn-hrcur-byte-invariantp c)
           (and (fn-hrcur-byte-invariantp (mv-nth 2 (fn-hrcur-byte-tick c)))
                (member-eq (mv-nth 0 (fn-hrcur-byte-tick c)) '(:continue :emit :prepared))
                (implies (eq (mv-nth 0 (fn-hrcur-byte-tick c)) :emit)
                         (fn-scc-octetp (mv-nth 1 (fn-hrcur-byte-tick c))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-tree-tick-preserves (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-tree-prepared-empty (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-leaf-tick-preserves (c (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-scalar-verdict (c (fn-hrcur-field 2 c))))
           :in-theory
           (e/d (fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-descriptorp)
                (fn-hrcur-tree-tick fn-hrcur-tree-invariantp fn-hrcur-tree-rest
                 fn-hrcur-tree-tick-preserves fn-hrcur-leaf-tick-preserves
                 fn-hrcur-leaf-invariantp fn-hrcur-leaf-tick
                 fn-hrsc-tick fn-hrsc-invariantp fn-hrsc-rest fn-hrsc-domainp
                 fn-scc-octet-listp fn-scc-octetp fn-scc-nat-octets)))))


(local
 (defthm fn-hrcur-leaf-prefix-rest
   (equal (fn-hrcur-leaf-rest
           (list :prefix nil x n (cons 6 (fn-scc-nat-octets n)) capture lease))
          (cons 6 (append (fn-scc-nat-octets n) x)))
   :hints (("Goal" :in-theory
            (e/d (fn-hrcur-leaf-rest)
                 (fn-hrcur-leaf-tick-refines-residual fn-scc-nat-octets))))))

(local
 (defthm fn-hrcur-tree-invariant-consp
   (implies (fn-hrcur-tree-invariantp c) (consp c))
   :hints (("Goal" :in-theory (enable fn-hrcur-tree-invariantp)))))

(local
 (defthm fn-hrcur-byte-scalar-residual
   (implies (and (fn-hrcur-byte-invariantp c) (eq (fn-hrcur-field 0 c) :scalar))
            (equal (fn-hrcur-byte-rest c)
                  (if (eq (mv-nth 0 (fn-hrcur-byte-tick c)) :emit)
                      (cons (mv-nth 1 (fn-hrcur-byte-tick c))
                            (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick c))))
                    (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick c))))))
   :hints (("Goal" :do-not-induct t :use ((:instance fn-hrsc-tick-refines-atom-residual (c (fn-hrcur-field 2 c))))
            :in-theory
            (e/d (fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                  fn-hrcur-descriptor-octets fn-hrcur-descriptorp)
                 (fn-hrcur-tree-tick fn-hrcur-tree-invariantp fn-hrcur-tree-rest
                 fn-hrcur-tree-tick-refines-residual fn-hrcur-tree-tick-preserves
                 fn-hrcur-leaf-tick-refines-residual fn-hrcur-leaf-tick-preserves fn-hrcur-leaf-rest
                 fn-hrcur-leaf-invariantp fn-hrcur-leaf-tick
                 fn-hrsc-tick-refines-atom-residual
                 fn-hrsc-tick fn-hrsc-invariantp fn-hrsc-rest fn-hrsc-domainp
                 fn-scc-atom-octets fn-scc-octet-listp fn-scc-octetp fn-scc-nat-octets))))))
(local
 (defthm fn-hrcur-byte-leaf-residual
   (implies (and (fn-hrcur-byte-invariantp c) (eq (fn-hrcur-field 0 c) :leaf))
            (equal (fn-hrcur-byte-rest c)
                  (if (eq (mv-nth 0 (fn-hrcur-byte-tick c)) :emit)
                      (cons (mv-nth 1 (fn-hrcur-byte-tick c))
                            (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick c))))
                    (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick c))))))
   :hints (("Goal" :do-not-induct t :use ((:instance fn-hrcur-leaf-tick-refines-residual (c (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-leaf-tick-preserves (c (fn-hrcur-field 2 c)))
                 (:instance fn-hrcur-leaf-prepared-empty (c (fn-hrcur-field 2 c))))
            :in-theory
            (e/d (fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                  fn-hrcur-descriptor-octets fn-hrcur-descriptorp)
                 (fn-hrcur-tree-tick fn-hrcur-tree-invariantp fn-hrcur-tree-rest
                 fn-hrcur-tree-tick-refines-residual fn-hrcur-tree-tick-preserves
                 fn-hrcur-leaf-tick-refines-residual fn-hrcur-leaf-tick-preserves fn-hrcur-leaf-rest
                 fn-hrcur-leaf-invariantp fn-hrcur-leaf-tick
                 fn-hrsc-tick-refines-atom-residual
                 fn-hrsc-tick fn-hrsc-invariantp fn-hrsc-rest fn-hrsc-domainp
                 fn-scc-atom-octets fn-scc-octet-listp fn-scc-octetp fn-scc-nat-octets))))))
(local
 (defthm fn-hrcur-byte-tree-residual
   (implies (and (fn-hrcur-byte-invariantp c) (eq (fn-hrcur-field 0 c) :tree))
            (equal (fn-hrcur-byte-rest c)
                  (if (eq (mv-nth 0 (fn-hrcur-byte-tick c)) :emit)
                      (cons (mv-nth 1 (fn-hrcur-byte-tick c))
                            (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick c))))
                    (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick c))))))
   :hints (("Goal" :do-not-induct t :use ((:instance fn-hrcur-tree-tick-refines-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-tree-tick-preserves (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-tree-prepared-empty (c (fn-hrcur-field 1 c))))
            :in-theory
            (e/d (fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                  fn-hrcur-descriptor-octets fn-hrcur-descriptorp)
                 (fn-hrcur-byte-scalar-residual fn-hrcur-byte-leaf-residual
                 fn-hrcur-tree-tick fn-hrcur-tree-invariantp fn-hrcur-tree-rest
                 fn-hrcur-tree-tick-refines-residual fn-hrcur-tree-tick-preserves
                 fn-hrcur-leaf-tick-refines-residual fn-hrcur-leaf-tick-preserves fn-hrcur-leaf-rest
                 fn-hrcur-leaf-invariantp fn-hrcur-leaf-tick
                 fn-hrsc-tick-refines-atom-residual
                 fn-hrsc-tick fn-hrsc-invariantp fn-hrsc-rest fn-hrsc-domainp
                 fn-scc-atom-octets fn-scc-octet-listp fn-scc-octetp fn-scc-nat-octets))))))
(local
 (defthm fn-hrcur-byte-done-residual
   (implies (and (fn-hrcur-byte-invariantp c) (eq (fn-hrcur-field 0 c) :done))
            (equal (fn-hrcur-byte-rest c)
                  (if (eq (mv-nth 0 (fn-hrcur-byte-tick c)) :emit)
                      (cons (mv-nth 1 (fn-hrcur-byte-tick c))
                            (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick c))))
                    (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick c))))))
   :hints (("Goal" :do-not-induct t
            :in-theory
            (e/d (fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                  fn-hrcur-descriptor-octets fn-hrcur-descriptorp)
                 (fn-hrcur-byte-scalar-residual fn-hrcur-byte-leaf-residual
                 fn-hrcur-tree-tick fn-hrcur-tree-invariantp fn-hrcur-tree-rest
                 fn-hrcur-tree-tick-refines-residual fn-hrcur-tree-tick-preserves
                 fn-hrcur-leaf-tick-refines-residual fn-hrcur-leaf-tick-preserves fn-hrcur-leaf-rest
                 fn-hrcur-leaf-invariantp fn-hrcur-leaf-tick
                 fn-hrsc-tick-refines-atom-residual
                 fn-hrsc-tick fn-hrsc-invariantp fn-hrsc-rest fn-hrsc-domainp
                 fn-scc-atom-octets fn-scc-octet-listp fn-scc-octetp fn-scc-nat-octets))))))
(defthm fn-hrcur-byte-tick-refines-residual
  (implies (fn-hrcur-byte-invariantp c) (equal (fn-hrcur-byte-rest c)
                  (if (eq (mv-nth 0 (fn-hrcur-byte-tick c)) :emit)
                      (cons (mv-nth 1 (fn-hrcur-byte-tick c))
                            (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick c))))
                    (fn-hrcur-byte-rest (mv-nth 2 (fn-hrcur-byte-tick c))))))
  :hints (("Goal" :use ((:instance fn-hrcur-byte-scalar-residual)
                        (:instance fn-hrcur-byte-leaf-residual)
                        (:instance fn-hrcur-byte-tree-residual)
                        (:instance fn-hrcur-byte-done-residual))
           :in-theory (e/d (fn-hrcur-byte-invariantp)
                            (fn-hrcur-byte-rest fn-hrcur-byte-tick
                             fn-hrcur-byte-scalar-residual fn-hrcur-byte-leaf-residual
                             fn-hrcur-byte-tree-residual fn-hrcur-byte-done-residual)))))

(defthm fn-hrcur-byte-tick-keeps-capture-lease
  (and (equal (fn-hrcur-field 3 (mv-nth 2 (fn-hrcur-byte-tick c))) (fn-hrcur-field 3 c))
       (equal (fn-hrcur-field 4 (mv-nth 2 (fn-hrcur-byte-tick c))) (fn-hrcur-field 4 c)))
  :hints (("Goal" :in-theory (enable fn-hrcur-byte-tick))))

(local (in-theory (disable fn-hrcur-byte-scalar-residual fn-hrcur-byte-leaf-residual
                           fn-hrcur-byte-tree-residual fn-hrcur-byte-done-residual)))
(in-theory (disable fn-hrcur-byte-tick-refines-residual
                    fn-hrcur-leaf-tick-refines-residual
                    fn-hrcur-tree-tick-refines-residual fn-hrsc-tick-refines-atom-residual))

(defthm fn-hrcur-byte-prepared-empty
  (implies (and (fn-hrcur-byte-invariantp c)
                (eq (mv-nth 0 (fn-hrcur-byte-tick c)) :prepared))
           (equal (fn-hrcur-byte-rest c) nil))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-tree-prepared-empty (c (fn-hrcur-field 1 c))))
           :in-theory
           (e/d (fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest)
                (fn-hrcur-tree-tick fn-hrcur-tree-invariantp fn-hrcur-tree-rest
                 fn-hrcur-leaf-tick fn-hrsc-tick fn-hrsc-rest fn-hrcur-leaf-rest)))))

; Census consumes the exact same byte stream as emission, with no encoded list.
; Three cells: phase, byte cursor, exact emitted-byte count.
(defun fn-hrcur-census-begin (source capture lease)
  (declare (xargs :guard t))
  (list :active (fn-hrcur-byte-begin source capture lease) 0))

(defun fn-hrcur-census-tick (c)
  (declare (xargs :guard t))
  (let ((phase (fn-hrcur-field 0 c)) (bytes (fn-hrcur-field 1 c))
        (n (fn-hrcur-field 2 c)))
    (cond
     ((not (and (fn-hrcur-widthp c 3) (natp n) (< n *fn-hrcur-u64-bound*)))
      (mv '(:refused :census-cursor) nil (list :refused bytes 0)))
     ((eq phase :done) (mv :prepared n c))
     ((eq phase :active)
      (mv-let (v byte next) (fn-hrcur-byte-tick bytes)
        (declare (ignore byte))
        (cond
         ((eq v :emit)
          (if (< (+ 1 n) *fn-hrcur-u64-bound*)
              (mv :continue nil (list :active next (+ 1 n)))
            (mv '(:refused :codec-width) nil (list :refused next n))))
         ((eq v :continue) (mv :continue nil (list :active next n)))
         ((eq v :prepared) (mv :prepared n (list :done next n)))
         (t (mv v nil (list :refused next n))))))
     (t (mv '(:refused :census-cursor) nil c)))))

(defun fn-hrcur-census-total (c)
  (declare (xargs :guard t :verify-guards nil))
  (+ (nfix (fn-hrcur-field 2 c)) (len (fn-hrcur-byte-rest (fn-hrcur-field 1 c)))))

(defun fn-hrcur-census-invariantp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hrcur-widthp c 3)
       (member-eq (fn-hrcur-field 0 c) '(:active :done))
       (fn-hrcur-byte-invariantp (fn-hrcur-field 1 c))
       (natp (fn-hrcur-field 2 c))
       (< (fn-hrcur-census-total c) *fn-hrcur-u64-bound*)
       (implies (eq (fn-hrcur-field 0 c) :done)
                (equal (fn-hrcur-byte-rest (fn-hrcur-field 1 c)) nil))))

(defthm fn-hrcur-census-begin-refines-length
  (implies (and (fn-hrcur-tree-domainp row)
                (< (len (fn-scc-encode row)) *fn-hrcur-u64-bound*))
           (and (fn-hrcur-census-invariantp
                 (fn-hrcur-census-begin (list :resident row) capture lease))
                (equal (fn-hrcur-census-total
                         (fn-hrcur-census-begin (list :resident row) capture lease))
                       (len (fn-scc-encode row)))))
  :hints (("Goal" :in-theory
           (e/d (fn-hrcur-census-begin fn-hrcur-census-invariantp fn-hrcur-census-total)
                (fn-hrcur-byte-begin fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                 fn-scc-encode fn-scc-program)))))

(defthm fn-hrcur-census-tick-refines-length
  (implies (fn-hrcur-census-invariantp c)
           (and (fn-hrcur-census-invariantp (mv-nth 2 (fn-hrcur-census-tick c)))
                (member-eq (mv-nth 0 (fn-hrcur-census-tick c)) '(:continue :prepared))
                (equal (fn-hrcur-census-total c)
                       (fn-hrcur-census-total (mv-nth 2 (fn-hrcur-census-tick c))))
                (implies (eq (mv-nth 0 (fn-hrcur-census-tick c)) :prepared)
                         (equal (mv-nth 1 (fn-hrcur-census-tick c))
                                (fn-hrcur-census-total c)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-byte-tick-refines-residual (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-byte-tick-preserves (c (fn-hrcur-field 1 c)))
                 (:instance fn-hrcur-byte-prepared-empty (c (fn-hrcur-field 1 c))))
           :in-theory
           (e/d (fn-hrcur-census-tick fn-hrcur-census-invariantp fn-hrcur-census-total)
                (fn-hrcur-byte-tick fn-hrcur-byte-invariantp fn-hrcur-byte-rest
                 fn-hrcur-byte-tick-preserves fn-hrcur-byte-prepared-empty)))))

(in-theory (disable fn-hrcur-byte-begin fn-hrcur-byte-tick fn-hrcur-byte-invariantp
                    fn-hrcur-byte-rest fn-hrcur-census-begin fn-hrcur-census-tick
                    fn-hrcur-census-invariantp fn-hrcur-census-total))

; Borrowed span component. Source/pin/pass authority is carried by the outer
; authenticated reader. This boundary requests one absolute payload position;
; supply accepts only the currently requested position and never materializes
; a source string/symbol. OP/PKG are canonical target descriptors, supplied by
; the name normalizer where needed. The wire model below is proof-only.
(DEFUN FN-HRCUR-SPAN-SHAPEP (C)
          (DECLARE (XARGS :GUARD T))
          (AND (FN-HRCUR-WIDTHP C 7)
               (MEMBER-EQ (FN-HRCUR-FIELD 0 C)
                          '(:PREFIX :BODY :DONE :REFUSED))
               (NATP (FN-HRCUR-FIELD 2 C))
               (< (FN-HRCUR-FIELD 2 C)
                  *FN-HRCUR-U64-BOUND*)
               (NATP (FN-HRCUR-FIELD 3 C))
               (< (FN-HRCUR-FIELD 3 C)
                  *FN-HRCUR-U64-BOUND*)
               (NATP (FN-HRCUR-FIELD 6 C))
               (< (FN-HRCUR-FIELD 6 C)
                  *FN-HRCUR-U64-BOUND*)))

(DEFUN FN-HRCUR-SPAN-BEGIN (OP PKG OFFSET COUNT CAPTURE LEASE)
          (DECLARE (XARGS :GUARD T))
          (IF (AND (MEMBER-EQUAL OP '(0 3 4 6))
                   (NATP PKG)
                   (< PKG 3)
                   (OR (EQUAL OP 4) (EQUAL PKG 0))
                   (NATP OFFSET)
                   (NATP COUNT)
                   (< (+ OFFSET COUNT)
                      *FN-HRCUR-U64-BOUND*)
                   (IMPLIES (EQUAL OP 0) (EQUAL COUNT 0)))
              (LIST :PREFIX
                    (IF (OR (EQUAL OP 0)
                            (AND (EQUAL OP 6) (EQUAL COUNT 0)))
                        '(0)
                      (CONS OP
                            (IF (EQUAL OP 4)
                                (CONS PKG (FN-SCC-NAT-OCTETS COUNT))
                              (FN-SCC-NAT-OCTETS COUNT))))
                    OFFSET
                    COUNT CAPTURE LEASE (+ OFFSET COUNT))
            (LIST :REFUSED NIL 0 0 CAPTURE LEASE 0)))

(DEFUN FN-HRCUR-SPAN-TICK (C)
          (DECLARE (XARGS :GUARD T))
          (LET ((PHASE (FN-HRCUR-FIELD 0 C))
                (P (FN-HRCUR-FIELD 1 C))
                (OFFSET (FN-HRCUR-FIELD 2 C))
                (LEFT (FN-HRCUR-FIELD 3 C))
                (CAPTURE (FN-HRCUR-FIELD 4 C))
                (LEASE (FN-HRCUR-FIELD 5 C))
                (END (FN-HRCUR-FIELD 6 C)))
            (COND ((NOT (FN-HRCUR-SPAN-SHAPEP C))
                   (MV '(:REFUSED :SPAN-CURSOR)
                       NIL
                       (LIST :REFUSED NIL 0 0 CAPTURE LEASE 0)))
                  ((EQ PHASE :PREFIX)
                   (COND ((AND (CONSP P) (FN-SCC-OCTETP (CAR P)))
                          (MV :EMIT (CAR P)
                              (LIST :PREFIX (CDR P)
                                    OFFSET LEFT CAPTURE LEASE END)))
                         ((NULL P)
                          (MV :CONTINUE NIL
                              (LIST :BODY
                                    NIL OFFSET LEFT CAPTURE LEASE END)))
                         (T (MV '(:REFUSED :SPAN-CURSOR) NIL C))))
                  ((EQ PHASE :BODY)
                   (IF (< 0 LEFT)
                       (MV (LIST :NEED-BYTE OFFSET) NIL C)
                     (MV :PREPARED NIL
                         (LIST :DONE NIL OFFSET 0 CAPTURE LEASE END))))
                  ((EQ PHASE :DONE) (MV :PREPARED NIL C))
                  (T (MV '(:REFUSED :SPAN-CURSOR) NIL C)))))

(DEFUN FN-HRCUR-SPAN-SUPPLY (C POSITION BYTE)
          (DECLARE (XARGS :GUARD T))
          (IF (AND (FN-HRCUR-SPAN-SHAPEP C)
                   (EQ (FN-HRCUR-FIELD 0 C) :BODY)
                   (< 0 (FN-HRCUR-FIELD 3 C))
                   (EQUAL POSITION (FN-HRCUR-FIELD 2 C))
                   (FN-SCC-OCTETP BYTE)
                   (< (+ 1 (FN-HRCUR-FIELD 2 C))
                      *FN-HRCUR-U64-BOUND*))
              (MV :EMIT BYTE
                  (LIST :BODY NIL (+ 1 (FN-HRCUR-FIELD 2 C))
                        (1- (FN-HRCUR-FIELD 3 C))
                        (FN-HRCUR-FIELD 4 C)
                        (FN-HRCUR-FIELD 5 C)
                        (FN-HRCUR-FIELD 6 C)))
            (MV '(:REFUSED :SPAN-RESPONSE) NIL C)))

(DEFUN FN-HRCUR-SPAN-INVARIANTP (C POOL)
          (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
          (AND (FN-HRCUR-SPAN-SHAPEP C)
               (FN-SCC-OCTET-LISTP POOL)
               (EQUAL (+ (FN-HRCUR-FIELD 2 C)
                         (FN-HRCUR-FIELD 3 C))
                      (FN-HRCUR-FIELD 6 C))
               (<= (FN-HRCUR-FIELD 6 C) (LEN POOL))
               (LET ((PHASE (FN-HRCUR-FIELD 0 C)))
                 (COND ((EQ PHASE :PREFIX)
                        (FN-SCC-OCTET-LISTP (FN-HRCUR-FIELD 1 C)))
                       ((EQ PHASE :BODY)
                        (NULL (FN-HRCUR-FIELD 1 C)))
                       ((EQ PHASE :DONE)
                        (AND (NULL (FN-HRCUR-FIELD 1 C))
                             (EQUAL (FN-HRCUR-FIELD 3 C) 0)))
                       (T NIL)))))

(DEFUN FN-HRCUR-SPAN-REST (C POOL)
          (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
          (APPEND (IF (EQ (FN-HRCUR-FIELD 0 C) :PREFIX)
                      (FN-HRCUR-FIELD 1 C)
                    NIL)
                  (FN-HRCUR-PREFIX (NFIX (FN-HRCUR-FIELD 3 C))
                                   (FN-HRCUR-TAIL (NFIX (FN-HRCUR-FIELD 2 C))
                                                  POOL))))

(DEFUN FN-HRCUR-SPAN-WIRE (OP PKG OFFSET COUNT POOL)
         (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
         (IF (OR (EQUAL OP 0)
                 (AND (EQUAL OP 6) (EQUAL COUNT 0)))
             '(0)
          (CONS
              OP
              (APPEND (IF (EQUAL OP 4)
                          (CONS PKG (FN-SCC-NAT-OCTETS COUNT))
                        (FN-SCC-NAT-OCTETS COUNT))
                      (FN-HRCUR-PREFIX COUNT (FN-HRCUR-TAIL OFFSET POOL))))))

(DEFTHM FN-HRCUR-SPAN-BEGIN-REFINES-WIRE
         (IMPLIES
          (AND (MEMBER-EQUAL OP '(0 3 4 6))
               (NATP PKG)
               (< PKG 3)
               (OR (EQUAL OP 4) (EQUAL PKG 0))
               (NATP OFFSET)
               (NATP COUNT)
               (< (+ OFFSET COUNT)
                  *FN-HRCUR-U64-BOUND*)
               (IMPLIES (EQUAL OP 0) (EQUAL COUNT 0))
               (FN-SCC-OCTET-LISTP POOL)
               (<= (+ OFFSET COUNT) (LEN POOL)))
          (AND
            (FN-HRCUR-SPAN-INVARIANTP
                 (FN-HRCUR-SPAN-BEGIN OP PKG OFFSET COUNT CAPTURE LEASE)
                 POOL)
            (EQUAL
                 (FN-HRCUR-SPAN-REST
                      (FN-HRCUR-SPAN-BEGIN OP PKG OFFSET COUNT CAPTURE LEASE)
                      POOL)
                 (FN-HRCUR-SPAN-WIRE OP PKG OFFSET COUNT POOL))))
         :HINTS
         (("Goal"
            :DO-NOT-INDUCT T
            :IN-THEORY
            (E/D (FN-HRCUR-SPAN-BEGIN FN-HRCUR-SPAN-INVARIANTP
                                      FN-HRCUR-SPAN-SHAPEP FN-HRCUR-SPAN-REST
                                      FN-HRCUR-SPAN-WIRE FN-SCC-NAT-OCTETS
                                      FN-SCC-OCTETP FN-SCC-OCTET-LISTP)
                 (FN-HRCUR-PREFIX FN-HRCUR-TAIL FN-SCC-LE-DIGITS)))))

(DEFTHM FN-HRCUR-SPAN-TICK-REFINES-WIRE
         (IMPLIES
          (FN-HRCUR-SPAN-INVARIANTP C POOL)
          (AND
           (FN-HRCUR-SPAN-INVARIANTP (MV-NTH 2 (FN-HRCUR-SPAN-TICK C))
                                     POOL)
           (EQUAL
              (FN-HRCUR-SPAN-REST C POOL)
              (IF (EQ (MV-NTH 0 (FN-HRCUR-SPAN-TICK C))
                      :EMIT)
                  (CONS (MV-NTH 1 (FN-HRCUR-SPAN-TICK C))
                        (FN-HRCUR-SPAN-REST (MV-NTH 2 (FN-HRCUR-SPAN-TICK C))
                                            POOL))
                (FN-HRCUR-SPAN-REST (MV-NTH 2 (FN-HRCUR-SPAN-TICK C))
                                    POOL)))
           (IMPLIES (EQ (MV-NTH 0 (FN-HRCUR-SPAN-TICK C))
                        :EMIT)
                    (FN-SCC-OCTETP (MV-NTH 1 (FN-HRCUR-SPAN-TICK C))))
           (IMPLIES (EQ (MV-NTH 0 (FN-HRCUR-SPAN-TICK C))
                        :PREPARED)
                    (EQUAL (FN-HRCUR-SPAN-REST C POOL)
                           NIL))))
         :HINTS
         (("Goal"
            :DO-NOT-INDUCT T
            :IN-THEORY
            (E/D (FN-HRCUR-SPAN-TICK FN-HRCUR-SPAN-INVARIANTP
                                     FN-HRCUR-SPAN-SHAPEP FN-HRCUR-SPAN-REST)
                 (FN-HRCUR-PREFIX FN-HRCUR-TAIL)))))

(LOCAL (DEFTHM FN-HRCUR-CAR-TAIL-IS-NTH
                 (IMPLIES (NATP POSITION)
                          (EQUAL (CAR (FN-HRCUR-TAIL POSITION POOL))
                                 (NTH POSITION POOL)))
                 :HINTS (("Goal" :INDUCT (FN-HRCUR-TAIL POSITION POOL)
                                 :IN-THEORY (ENABLE FN-HRCUR-TAIL NTH)))))

(LOCAL
         (DEFTHM FN-HRCUR-SPAN-PAYLOAD-STEP
          (IMPLIES
           (AND (NATP POSITION)
                (NATP COUNT)
                (< 0 COUNT))
           (EQUAL
               (FN-HRCUR-PREFIX COUNT (FN-HRCUR-TAIL POSITION POOL))
               (CONS (NTH POSITION POOL)
                     (FN-HRCUR-PREFIX (1- COUNT)
                                      (FN-HRCUR-TAIL (+ 1 POSITION) POOL)))))
          :HINTS
          (("Goal" :DO-NOT-INDUCT T
                   :USE ((:INSTANCE FN-HRCUR-NTHCDR-SUCCESSOR (N POSITION)
                                    (X POOL))
                         (:INSTANCE FN-HRCUR-CAR-TAIL-IS-NTH))
                   :EXPAND ((TAKE COUNT (NTHCDR POSITION POOL)))
                   :IN-THEORY (DISABLE TAKE NTHCDR
                                       FN-HRCUR-PREFIX FN-HRCUR-TAIL)))))

(LOCAL (DEFTHM FN-HRCUR-TAIL-CONSP-WITHIN
                 (IMPLIES (AND (NATP POSITION)
                               (< POSITION (LEN POOL)))
                          (CONSP (NTHCDR POSITION POOL)))
                 :HINTS (("Goal" :INDUCT (NTHCDR POSITION POOL)
                                 :IN-THEORY (ENABLE NTHCDR)))))

(LOCAL
          (DEFTHM FN-HRCUR-POOL-BYTE
            (IMPLIES (AND (FN-SCC-OCTET-LISTP POOL)
                          (NATP POSITION)
                          (< POSITION (LEN POOL)))
                     (FN-SCC-OCTETP (NTH POSITION POOL)))
            :HINTS (("Goal" :INDUCT (NTH POSITION POOL)
                            :IN-THEORY (ENABLE NTH FN-SCC-OCTET-LISTP
                                               FN-SCC-OCTETP)))))

(DEFTHM FN-HRCUR-SPAN-SUPPLY-REFINES-WIRE
         (IMPLIES
          (AND (FN-HRCUR-SPAN-INVARIANTP C POOL)
               (EQ (FN-HRCUR-FIELD 0 C) :BODY)
               (< 0 (FN-HRCUR-FIELD 3 C))
               (EQUAL POSITION (FN-HRCUR-FIELD 2 C))
               (EQUAL BYTE (NTH POSITION POOL)))
          (AND
            (EQUAL (MV-NTH 0
                           (FN-HRCUR-SPAN-SUPPLY C POSITION BYTE))
                   :EMIT)
            (EQUAL (MV-NTH 1
                           (FN-HRCUR-SPAN-SUPPLY C POSITION BYTE))
                   BYTE)
            (FN-HRCUR-SPAN-INVARIANTP
                 (MV-NTH 2
                         (FN-HRCUR-SPAN-SUPPLY C POSITION BYTE))
                 POOL)
            (EQUAL (FN-HRCUR-SPAN-REST C POOL)
                   (CONS BYTE
                         (FN-HRCUR-SPAN-REST
                              (MV-NTH 2
                                      (FN-HRCUR-SPAN-SUPPLY C POSITION BYTE))
                              POOL)))))
         :HINTS
         (("Goal"
           :DO-NOT-INDUCT T
           :USE ((:INSTANCE FN-HRCUR-SPAN-PAYLOAD-STEP
                            (POSITION (FN-HRCUR-FIELD 2 C))
                            (COUNT (FN-HRCUR-FIELD 3 C))))
           :IN-THEORY
           (E/D
               (FN-HRCUR-SPAN-SUPPLY FN-HRCUR-SPAN-INVARIANTP
                                     FN-HRCUR-SPAN-SHAPEP FN-HRCUR-SPAN-REST)
               (FN-HRCUR-SPAN-TICK-REFINES-WIRE FN-HRCUR-SPAN-PAYLOAD-STEP
                                                TAKE FN-HRCUR-PREFIX
                                                FN-HRCUR-TAIL NTH NTHCDR)))))

(DEFTHM FN-HRCUR-SPAN-SUPPLY-REFUSES-WRONG-POSITION
         (IMPLIES (NOT (EQUAL POSITION (FN-HRCUR-FIELD 2 C)))
                  (AND (EQUAL (MV-NTH 0
                                      (FN-HRCUR-SPAN-SUPPLY C POSITION BYTE))
                              '(:REFUSED :SPAN-RESPONSE))
                       (EQUAL (MV-NTH 2
                                      (FN-HRCUR-SPAN-SUPPLY C POSITION BYTE))
                              C)))
         :HINTS (("Goal" :IN-THEORY (ENABLE FN-HRCUR-SPAN-SUPPLY))))

(DEFTHM FN-HRCUR-SPAN-KEEPS-CAPTURE-LEASE
         (AND
          (EQUAL (FN-HRCUR-FIELD 4 (MV-NTH 2 (FN-HRCUR-SPAN-TICK C)))
                 (FN-HRCUR-FIELD 4 C))
          (EQUAL (FN-HRCUR-FIELD 5 (MV-NTH 2 (FN-HRCUR-SPAN-TICK C)))
                 (FN-HRCUR-FIELD 5 C))
          (EQUAL
             (FN-HRCUR-FIELD 4
                             (MV-NTH 2
                                     (FN-HRCUR-SPAN-SUPPLY C POSITION BYTE)))
             (FN-HRCUR-FIELD 4 C))
          (EQUAL
             (FN-HRCUR-FIELD 5
                             (MV-NTH 2
                                     (FN-HRCUR-SPAN-SUPPLY C POSITION BYTE)))
             (FN-HRCUR-FIELD 5 C)))
         :HINTS (("Goal" :IN-THEORY (ENABLE FN-HRCUR-SPAN-TICK
                                            FN-HRCUR-SPAN-SUPPLY))))

(LOCAL (DEFTHM FN-HRCUR-SPAN-TAIL-LENGTH
                 (IMPLIES (AND (NATP POSITION)
                               (<= POSITION (LEN POOL)))
                          (EQUAL (LEN (NTHCDR POSITION POOL))
                                 (- (LEN POOL) POSITION)))
                 :HINTS (("Goal" :INDUCT (NTHCDR POSITION POOL)
                                 :IN-THEORY (ENABLE NTHCDR)))))

(LOCAL
           (DEFTHM FN-HRCUR-SPAN-SLICE-OCTETS
             (IMPLIES (AND (FN-SCC-OCTET-LISTP POOL)
                           (NATP OFFSET)
                           (NATP COUNT)
                           (<= (+ OFFSET COUNT) (LEN POOL)))
                      (FN-SCC-OCTET-LISTP (TAKE COUNT (NTHCDR OFFSET POOL))))
             :HINTS
             (("Goal" :DO-NOT-INDUCT T
               :USE ((:instance fn-scc-octet-listp-facts (x pool) (n offset))
                     (:instance fn-scc-octet-listp-take
                                (x (nthcdr offset pool)) (n count))
                     (:instance fn-hrcur-span-tail-length (position offset)))
               :IN-THEORY (DISABLE TAKE NTHCDR FN-SCC-OCTET-LISTP
                                  fn-scc-octet-listp-facts
                                  fn-scc-octet-listp-take
                                  fn-hrcur-span-tail-length)))))

(LOCAL
          (DEFTHM FN-HRCUR-SPAN-CHARS-ROUNDTRIP
            (IMPLIES (FN-SCC-OCTET-LISTP BYTES)
                     (EQUAL (FN-SCC-CHARS-OCTETS (FN-SCC-OCTETS-CHARS BYTES))
                            BYTES))
            :HINTS
            (("Goal" :INDUCT (FN-SCC-OCTET-LISTP BYTES)
                     :IN-THEORY (ENABLE FN-SCC-OCTET-LISTP
                                        FN-SCC-OCTETP FN-SCC-CHARS-OCTETS
                                        FN-SCC-OCTETS-CHARS)))))

(local
 (defthm fn-hrcur-take-positive-consp
   (implies (and (natp count) (< 0 count)) (consp (take count x)))
   :hints (("Goal" :expand ((take count x)) :in-theory (disable take)))))

(DEFTHM FN-HRCUR-SPAN-OCTETS-REFINES-ABSTRACT-CODEC
         (IMPLIES
          (AND (FN-SCC-OCTET-LISTP POOL)
               (NATP OFFSET)
               (NATP COUNT)
               (<= (+ OFFSET COUNT) (LEN POOL)))
          (EQUAL
               (FN-HRCUR-SPAN-WIRE 6 0 OFFSET COUNT POOL)
               (FN-SCC-ENCODE (FN-HDC-ABSTRACT (FN-HDC-SPAN 6 0 OFFSET COUNT)
                                               POOL))))
         :HINTS
         (("Goal"
               :DO-NOT-INDUCT T
               :IN-THEORY
               (E/D (FN-HRCUR-SPAN-WIRE FN-HDC-SPAN FN-HDC-ABSTRACT
                                        FN-SCC-PROGRAM FN-SCC-OCTETS-VALUEP)
                    (FN-SCC-ATOM-OCTETS FN-SCC-NAT-OCTETS TAKE NTHCDR)))))

(defthm fn-hrcur-span-string-refines-abstract-codec
  (implies (and (fn-scc-octet-listp pool) (natp offset) (natp count)
                (<= (+ offset count) (len pool)))
           (equal (fn-hrcur-span-wire 3 0 offset count pool)
                  (fn-scc-encode
                    (fn-hdc-abstract (fn-hdc-span 3 0 offset count) pool))))
  :hints (("Goal" :do-not-induct t
           :in-theory
           (e/d (fn-hrcur-span-wire fn-hdc-span fn-hdc-abstract
                 fn-scc-program fn-scc-octets-valuep fn-scc-atom-octets
                 fn-scc-string-octets)
                (fn-scc-nat-octets fn-scc-chars-octets
                 fn-scc-octets-chars take nthcdr)))))

; Logical productive-work measure. A pending byte request waits for the reader;
; all other nonterminal ticks and every authenticated supply make progress.
(defun fn-hrcur-span-work (c)
  (declare (xargs :guard t :verify-guards nil))
  (case (fn-hrcur-field 0 c)
    (:prefix (+ 2 (len (fn-hrcur-field 1 c)) (nfix (fn-hrcur-field 3 c))))
    (:body (+ 1 (nfix (fn-hrcur-field 3 c))))
    (otherwise 0)))

(defthm fn-hrcur-span-tick-progress-or-request
  (implies (and (fn-hrcur-span-invariantp c pool)
                (not (eq (fn-hrcur-field 0 c) :done)))
           (or (< (fn-hrcur-span-work (mv-nth 2 (fn-hrcur-span-tick c)))
                  (fn-hrcur-span-work c))
               (and (equal (mv-nth 0 (fn-hrcur-span-tick c))
                           (list :need-byte (fn-hrcur-field 2 c)))
                    (equal (mv-nth 2 (fn-hrcur-span-tick c)) c))))
  :hints (("Goal" :do-not-induct t
           :cases ((eq (fn-hrcur-field 0 c) :prefix)
                   (eq (fn-hrcur-field 0 c) :body))
           :expand ((len (fn-hrcur-field 1 c))
                    (fn-scc-octet-listp (fn-hrcur-field 1 c)))
           :in-theory
           (e/d (fn-hrcur-span-work fn-hrcur-span-tick
                 fn-hrcur-span-invariantp fn-hrcur-span-shapep)
                (fn-hrcur-span-tick-refines-wire fn-hrcur-span-rest
                 fn-scc-octet-listp len)))))

(defthm fn-hrcur-span-supply-progress
  (implies (and (fn-hrcur-span-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :body)
                (< 0 (fn-hrcur-field 3 c))
                (equal position (fn-hrcur-field 2 c))
                (equal byte (nth position pool)))
           (< (fn-hrcur-span-work
                 (mv-nth 2 (fn-hrcur-span-supply c position byte)))
              (fn-hrcur-span-work c)))
  :hints (("Goal" :use ((:instance fn-hrcur-pool-byte))
           :in-theory
           (e/d (fn-hrcur-span-work fn-hrcur-span-supply
                 fn-hrcur-span-invariantp fn-hrcur-span-shapep)
                (fn-hrcur-span-supply-refines-wire fn-hrcur-span-rest nth)))))

(in-theory (disable fn-hrcur-span-shapep fn-hrcur-span-begin
                    fn-hrcur-span-tick fn-hrcur-span-supply
                    fn-hrcur-span-invariantp fn-hrcur-span-rest
                    fn-hrcur-span-wire fn-hrcur-span-work))
