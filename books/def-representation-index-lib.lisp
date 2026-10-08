; fn: the generic theory of an INDEXED LOG (lane s-hcf 2026-10-08).
;
; A log of objects kept as columns, with a salted eql-hash index from a key of an
; object to the positions whose object carries that key.  The model is the
; stobj as the list (ROWS COUNT MIDS SALT): ROWS the array of objects by
; position, COUNT the fill, MIDS the table (an alist HASH -> positions, newest
; first), SALT the register the hash reads.  What the instance GIVES is five
; functions; what is proved HERE, once, over them, is everything the
; abstract-stobj obligations need: the fold of appends from the empty object,
; the bucket invariant (every position in a bucket is below the count), and the
; lookup (walk a bucket with the exact test) equal to the logical filter.
;
; The table is keyed on the FULL hash (an eql hash-table), not on a reduction
; of it to a table size: no `mod' appears, and bucket completeness rests on
; IX-HASH being a natural (`ix-hash-natp') alone.  Every position in a bucket
; is checked by IX-TEST, so no answer assumes the hash separates two keys.
(in-package "ACL2")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable (tau-system))))

(encapsulate
  ((ix-key (ev) t)         ; the key of an object
   (ix-keyp (k) t)         ; an object whose key is not a key is not indexed
   (ix-hash (k salt) t)    ; the salted hash of a key
   (ix-test (k ev) t)      ; the exact test a lookup applies to each candidate
   (ix-proj (ev) t)        ; what a matching object contributes to the answer
   (ix-q (k h) t))         ; the logical answer over a history H
  (local (defun ix-key (ev) (if (stringp ev) ev nil)))
  (local (defun ix-keyp (k) (stringp k)))
  (local (defun ix-hash (k salt) (declare (ignore k)) (nfix salt)))
  (local (defun ix-test (k ev) (and (stringp k) (equal (ix-key ev) k))))
  (local (defun ix-proj (ev) ev))
  (local (defun ix-q (k h)
           (if (consp h)
               (if (ix-test k (car h))
                   (cons (ix-proj (car h)) (ix-q k (cdr h)))
                 (ix-q k (cdr h)))
             nil)))
  (defthm ix-hash-natp
    (natp (ix-hash k salt))
    :rule-classes :type-prescription)
  (defthm ix-test-implies-key
    (implies (ix-test k ev)
             (and (ix-keyp k) (equal (ix-key ev) k)))
    :rule-classes nil)
  (defthm ix-q-of-atom
    (implies (not (consp h)) (equal (ix-q k h) nil))
    :rule-classes nil)
  (defthm ix-q-of-cons
    (equal (ix-q k (cons x r))
           (if (ix-test k x)
               (cons (ix-proj x) (ix-q k r))
             (ix-q k r)))
    :rule-classes nil))

(defun ix-grow (c)
  (declare (xargs :guard t :verify-guards nil))
  (let ((n (nth 1 c)) (cap (len (nth 0 c))))
    (if (< (nfix n) cap)
        c
      (update-nth 0 (resize-list (nth 0 c) (max 16 (* 2 (max (nfix n) cap))) nil) c))))

(defun ix-append (ev c)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((n (nth 1 c))
         (c (ix-grow c))
         (c (update-nth 0 (update-nth n ev (nth 0 c)) c))
         (k (ix-key ev))
         (c (if (ix-keyp k)
                (let ((h (ix-hash k (nth 3 c))))
                  (update-nth 2 (cons (cons h (cons n (cdr (hons-assoc-equal h (nth 2 c)))))
                                      (nth 2 c))
                              c))
              c)))
    (update-nth 1 (1+ n) c)))

(defun ix-bucket (h c)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (hons-assoc-equal h (nth 2 c))))

(defun ix-collect (k seqs acc c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp seqs)
      (let ((i (car seqs)))
        (if (and (natp i) (< i (len (nth 0 c))))
            (let ((ev (nth i (nth 0 c))))
              (ix-collect k (cdr seqs)
                          (if (ix-test k ev) (cons (ix-proj ev) acc) acc)
                          c))
          (ix-collect k (cdr seqs) acc c)))
    acc))

(defun ix-cquery (k c)
  (declare (xargs :guard t :verify-guards nil))
  (ix-collect k (ix-bucket (ix-hash k (nth 3 c)) c) nil c))

(defun ix-empty (salt)
  (declare (xargs :guard t :verify-guards nil))
  (list nil 0 nil salt))

(defun ix-build (events c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (ix-build (cdr events) (ix-append (car events) c))
    c))

(defun ix-cp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp c)
       (equal (len c) 4)
       (true-listp (nth 0 c))
       (natp (nth 1 c))
       (unsigned-byte-p 32 (nth 3 c))))

(defun ix-corr (c a)
  (declare (xargs :guard t :verify-guards nil))
  (and (ix-cp c)
       (true-listp a)
       (equal c (ix-build a (ix-empty (nth 3 c))))))

(defun ix-below-p (s n)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp s)
      (and (natp (car s)) (< (car s) (nfix n)) (ix-below-p (cdr s) n))
    t))

(local
 (defun ix-resize-induct (i l k)
   (if (and (posp k) (posp i))
       (ix-resize-induct (1- i) (if (consp l) (cdr l) l) (1- k))
     (list i l k))))

(local
 (defthm ix-resize-list-open
   (and (implies (posp k)
                 (equal (resize-list l k d)
                        (cons (if (atom l) d (car l))
                              (resize-list (if (atom l) l (cdr l)) (1- k) d))))
        (implies (not (posp k))
                 (equal (resize-list l k d) nil))
        (equal (car (resize-list l k d))
               (if (posp k) (if (atom l) d (car l)) nil)))
   :hints (("Goal" :in-theory (enable resize-list)))))

(local
 (defthm ix-nth-of-resize-list
   (implies (natp i)
            (equal (nth i (resize-list l k nil))
                   (if (< i (nfix k)) (nth i l) nil)))
   :hints (("Goal" :in-theory (union-theories
             '(ix-resize-induct ix-resize-list-open nth nfix natp posp zp
               not car-cons cdr-cons fold-consts-in-+)
             (theory 'minimal-theory))
            :induct (ix-resize-induct i l k)))))

(local (in-theory (disable ix-resize-list-open)))

(local
 (defthm ix-len-of-resize-list
   (equal (len (resize-list l n d)) (nfix n))
   :hints (("Goal" :in-theory (enable resize-list)))))

(local
 (defthm ix-rows-length-of-grow
   (implies (natp (nth 1 c))
            (< (nth 1 c) (len (nth 0 (ix-grow c)))))
   :rule-classes :linear))

(local
 (defthm ix-grow-fields
   (and (equal (nth 1 (ix-grow c)) (nth 1 c))
        (equal (nth 2 (ix-grow c)) (nth 2 c))
        (equal (nth 3 (ix-grow c)) (nth 3 c)))))

(local
 (defthm ix-append-fields
   (and (equal (nth 1 (ix-append x c)) (1+ (nth 1 c)))
        (equal (nth 3 (ix-append x c)) (nth 3 c))
        (equal (nth 0 (ix-append x c))
               (update-nth (nth 1 c) x (nth 0 (ix-grow c))))
        (equal (nth 2 (ix-append x c))
               (if (ix-keyp (ix-key x))
                   (let ((h (ix-hash (ix-key x) (nth 3 c))))
                     (cons (cons h (cons (nth 1 c)
                                         (cdr (hons-assoc-equal h (nth 2 c)))))
                           (nth 2 c)))
                 (nth 2 c))))
   :hints (("Goal" :use ((:instance ix-grow-fields))
             :in-theory (union-theories
              '(ix-append nth-update-nth car-cons cdr-cons
                fold-consts-in-+ nfix natp zp)
              (theory 'minimal-theory))))))

(local (in-theory (disable ix-append)))

(defthm ix-build-of-append-one
  (equal (ix-build (append events (list x)) c)
         (ix-append x (ix-build events c)))
  :hints (("Goal" :in-theory (enable ix-build))))

(local
 (defthm ix-build-count
   (implies (natp (nth 1 c))
            (equal (nth 1 (ix-build events c))
                   (+ (nth 1 c) (len events))))
   :hints (("Goal" :in-theory (enable ix-build)))))

(local
 (defthm ix-build-salt
   (equal (nth 3 (ix-build events c)) (nth 3 c))
   :hints (("Goal" :in-theory (enable ix-build)))))

(local
 (defthm ix-append-room
   (implies (natp (nth 1 c))
            (< (nth 1 c) (len (nth 0 (ix-append x c)))))
   :rule-classes :linear))

(local
 (defthm ix-build-room
   (implies (and (natp (nth 1 c)) (<= (nth 1 c) (len (nth 0 c))))
            (<= (nth 1 (ix-build events c))
                (len (nth 0 (ix-build events c)))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (ix-build) (ix-append-fields))
            :induct (ix-build events c))
           ("Subgoal *1/1" :use ((:instance ix-append-fields (x (car events)))
                                 (:instance ix-append-room (x (car events))))))))

(local
 (defthm ix-grow-rows-below
   (implies (and (natp i) (natp (nth 1 c)) (< i (nth 1 c)))
            (equal (nth i (nth 0 (ix-grow c)))
                   (nth i (nth 0 c))))
   :hints (("Goal" :in-theory (e/d (ix-grow) (nth update-nth resize-list))))))

(local
 (defthm ix-append-rows-below
   (implies (and (natp i) (natp (nth 1 c)) (< i (nth 1 c)))
            (equal (nth i (nth 0 (ix-append x c)))
                   (nth i (nth 0 c))))
   :hints (("Goal" :in-theory (disable ix-grow nth update-nth)))))

(local
 (defthm ix-append-rows-at
   (implies (natp (nth 1 c))
            (equal (nth (nth 1 c) (nth 0 (ix-append x c))) x))))

(local
 (defthm ix-nth-cons-natural
  (implies (natp i)
   (equal (nth i (cons x xs))
          (if (zp i) x (nth (- i 1) xs))))
  :hints (("Goal" :in-theory (union-theories
             '(nth nfix natp zp car-cons cdr-cons) (theory 'minimal-theory))))))

(local
 (defthm ix-build-rows
   (implies (and (natp i) (natp (nth 1 c))
                 (< i (+ (nth 1 c) (len events))))
            (equal (nth i (nth 0 (ix-build events c)))
                   (if (< i (nth 1 c))
                       (nth i (nth 0 c))
                     (nth (- i (nth 1 c)) events))))
   :hints (("Goal" :in-theory (e/d (ix-build ix-nth-cons-natural)
                             (ix-grow ix-append nth update-nth))
            :induct (ix-build events c)))))

(local
 (defthm ix-count-natp-of-cp
   (implies (ix-cp c) (natp (nth 1 c)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable ix-cp)))))

(local
 (defthm ix-grow-shape
   (implies (ix-cp c)
            (and (true-listp (ix-grow c))
                 (equal (len (ix-grow c)) 4)
                 (true-listp (nth 0 (ix-grow c)))))
   :hints (("Goal" :in-theory (enable ix-grow ix-cp)))))

(local
 (defthm ix-append-shape
   (implies (ix-cp c)
            (and (true-listp (ix-append x c))
                 (equal (len (ix-append x c)) 4)))
   :hints (("Goal" :in-theory (e/d (ix-append) (ix-grow ix-grow-shape))
            :use ((:instance ix-grow-shape))))))

(local
 (defthm ix-cp-of-append
   (implies (ix-cp c) (ix-cp (ix-append x c)))
   :hints (("Goal" :in-theory (e/d (ix-cp) (ix-append ix-grow ix-grow-shape ix-append-shape
                                            ix-append-fields))
            :use ((:instance ix-grow-shape) (:instance ix-append-shape)
                  (:instance ix-append-fields))))))

(local
 (defthm ix-build-cp
   (implies (ix-cp c) (ix-cp (ix-build events c)))
   :hints (("Goal" :in-theory (e/d (ix-build) (ix-cp))))))

(local
 (defthm ix-below-p-monotone
   (implies (and (ix-below-p s n) (natp n) (natp k) (<= n k))
            (ix-below-p s k))))

(local
 (defthm ix-collect-append-acc
   (equal (ix-collect m s (append a b) c)
          (append (ix-collect m s a c) b))
   :hints (("Goal" :in-theory (disable)))))

(local
 (defthm ix-collect-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (ix-collect m s acc c)
                   (append (ix-collect m s nil c) acc)))
   :hints (("Goal" :use ((:instance ix-collect-append-acc (a nil) (b acc)))
            :in-theory (disable ix-collect-append-acc)))))

(local
 (defthm ix-collect-true-listp
   (implies (true-listp acc) (true-listp (ix-collect m s acc c)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (disable ix-collect-acc ix-collect-append-acc
                                        )))))

(local
 (defthm ix-collect-of-append-below
   (implies (and (ix-below-p s (nth 1 c))
                 (natp (nth 1 c))
                 (<= (nth 1 c) (len (nth 0 c))))
            (equal (ix-collect m s acc (ix-append x c))
                   (ix-collect m s acc c)))
   :hints (("Goal" :in-theory (e/d nil
                                   (nth update-nth ix-collect-acc
                                    ix-collect-append-acc 
                                     ix-grow (:definition ix-collect)))
            :induct (ix-collect m s acc c)
            :expand ((ix-collect m s acc c)
                     (ix-collect m s acc (ix-append x c)))))))

(local
 (defthm ix-bucket-of-append
   (equal (ix-bucket h (ix-append x c))
          (if (and (ix-keyp (ix-key x))
                   (equal h (ix-hash (ix-key x) (nth 3 c))))
              (cons (nth 1 c) (ix-bucket h c))
            (ix-bucket h c)))
   :hints (("Goal" :in-theory (disable   nth
                                       update-nth ix-grow)))))

(local
 (defthm ix-below-p-of-append
   (implies (and (ix-below-p (ix-bucket h c) (nth 1 c))
                 (natp (nth 1 c)))
            (ix-below-p (ix-bucket h (ix-append x c))
                             (1+ (nth 1 c))))
   :hints (("Goal" :in-theory (disable   nth
                                       update-nth ix-grow ix-bucket)))))

(local
 (defthm ix-msgid-records-is-collect-bucket
   (equal (ix-cquery m c)
          (ix-collect m (ix-bucket (ix-hash m (nth 3 c)) c)
                             nil c))
   :hints (("Goal" :in-theory (enable ix-cquery)))))

(local (in-theory (disable ix-bucket ix-cquery)))

(local
 (defthm ix-msgid-records-of-append
   (implies (and (ix-keyp m)
                 (natp (nth 1 c))
                 (<= (nth 1 c) (len (nth 0 c)))
                 (ix-below-p (ix-bucket (ix-hash m (nth 3 c)) c)
                                  (nth 1 c)))
            (equal (ix-cquery m (ix-append x c))
                   (append (ix-cquery m c)
                           (ix-q m (list x)))))
   :hints (("Goal" :in-theory (e/d nil
                                   (nth update-nth  
                                    ))
            :expand ((:free (acc c) (ix-collect m (cons (nth 1 c) s) acc c)))
            :use ((:instance ix-test-implies-key (k m) (ev x))
                  (:instance ix-q-of-cons (k m) (r nil))
                  (:instance ix-q-of-atom (k m) (h nil)))))))

(local
 (defthm ix-records-for-split
   (implies (consp events)
            (equal (ix-q m events)
                   (append (ix-q m (list (car events)))
                           (ix-q m (cdr events)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable)
            :use ((:instance ix-q-of-cons (k m) (x (car events)) (r (cdr events)))
                  (:instance ix-q-of-cons (k m) (x (car events)) (r nil))
                  (:instance ix-q-of-atom (k m) (h nil)))))))

(local
 (defthm ix-msgid-records-true-listp
   (true-listp (ix-cquery m c))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm ix-q-of-atom-rewrite
   (implies (not (consp events))
            (equal (ix-q m events) nil))
   :hints (("Goal" :use ((:instance ix-q-of-atom (k m) (h events)))))))

(local (in-theory (disable ix-msgid-records-is-collect-bucket
                           ix-bucket-of-append ix-collect-of-append-below)))

(local
 (defthm ix-build-msgid-records
   (implies (and (ix-keyp m)
                 (natp (nth 1 c))
                 (<= (nth 1 c) (len (nth 0 c)))
                 (ix-below-p (ix-bucket (ix-hash m (nth 3 c)) c)
                                  (nth 1 c)))
            (equal (ix-cquery m (ix-build events c))
                   (append (ix-cquery m c)
                           (ix-q m events))))
   :hints (("Goal" :in-theory (e/d (ix-build)
                                   ( 
                                     
                                    nth update-nth))
            :induct (ix-build events c))
           ("Subgoal *1/1" :use ((:instance ix-records-for-split)
                                 (:instance ix-below-p-of-append
                                            (x (car events))
                                            (h (ix-hash m (nth 3 c)))))))))

(local
 (defthm ix-empty-fields
   (and (equal (nth 0 (ix-empty s)) nil)
        (equal (nth 1 (ix-empty s)) 0)
        (equal (nth 2 (ix-empty s)) nil)
        (equal (nth 3 (ix-empty s)) s))))

(local
 (defthm ix-empty-bucket
   (equal (ix-bucket h (ix-empty s)) nil)
   :hints (("Goal" :in-theory (enable ix-bucket)))))

(local
 (defthm ix-empty-msgid-records
   (equal (ix-cquery m (ix-empty s)) nil)
   :hints (("Goal" :in-theory (e/d (ix-msgid-records-is-collect-bucket)
                                   (ix-empty ))))))

(local (in-theory (disable ix-empty)))

(local
 (defthm ix-count-of-build
   (implies (equal c (ix-build a (ix-empty s)))
            (equal (nth 1 c) (len a)))))

(local
 (defthm ix-room-of-build
   (implies (equal c (ix-build a (ix-empty s)))
            (<= (len a) (len (nth 0 c))))
   :hints (("Goal" :use ((:instance ix-build-room (events a)
                                    (c (ix-empty s))))
            :in-theory (disable ix-build-room)))))

(local
 (defthm ix-at-of-build
   (implies (and (equal c (ix-build a (ix-empty s)))
                 (natp seq) (< seq (len a)))
            (equal (nth seq (nth 0 c)) (nth seq a)))
   :hints (("Goal" :in-theory (disable nth ix-build-rows)
            :use ((:instance ix-build-rows (i seq) (events a)
                             (c (ix-empty s))))))))

(local
 (defthm ix-msgid-records-of-build
   (implies (and (equal c (ix-build a (ix-empty s)))
                 (ix-keyp m))
            (equal (ix-cquery m c)
                   (ix-q m a)))
   :hints (("Goal" :in-theory (disable)))))

(local (in-theory (disable ix-corr)))

(local
 (defthm ix-corr-facts
   (implies (ix-corr c a)
            (and (ix-cp c)
                 (true-listp a)
                 (equal (nth 1 c) (len a))
                 (<= (len a) (len (nth 0 c)))
                 (implies (and (natp seq) (< seq (len a)))
                          (equal (nth seq (nth 0 c)) (nth seq a)))
                 (implies (ix-keyp m)
                          (equal (ix-cquery m c)
                                 (ix-q m a)))))
   :hints (("Goal" :in-theory (e/d (ix-corr)
                                   (ix-count-of-build ix-room-of-build
                                    ix-at-of-build ix-msgid-records-of-build
                                     
                                     nth))
            :use ((:instance ix-count-of-build (s (nth 3 c)))
                  (:instance ix-room-of-build (s (nth 3 c)))
                  (:instance ix-at-of-build (s (nth 3 c)))
                  (:instance ix-msgid-records-of-build (s (nth 3 c))))))))


(defthm ix-append-preserves-corr
  (implies (and (ix-corr c a) (true-listp a))
           (ix-corr (ix-append ev c) (append a (list ev))))
  :hints (("Goal" :in-theory (e/d (ix-corr) (ix-corr-facts))
           :use ((:instance ix-build-of-append-one
                            (events a) (x ev) (c (ix-empty (nth 3 c))))))))

; The logical clear takes a salt and ignores it; the foundation's clear
; resets every column and stores the salt.
(defun ix-clear (salt c)
  (declare (xargs :guard t :verify-guards nil))
  (update-nth 3 salt
              (update-nth 2 nil
                          (update-nth 1 0
                                      (update-nth 0 (resize-list (nth 0 c) 0 nil) c)))))

(defthm ix-clear-is-empty
  (implies (ix-cp c)
           (equal (ix-clear salt c) (ix-empty salt)))
  :hints (("Goal" :in-theory (enable ix-clear ix-cp ix-empty update-nth resize-list)
           :expand ((len c) (len (cdr c)) (len (cddr c)) (len (cdddr c))
                    (len (cddddr c))))))

(local
 (defun-nx ix-model-build-induct (events h c)
   (if (consp events)
       (ix-model-build-induct (cdr events) (append h (list (car events)))
                                  (ix-append (car events) c))
     (list h c))))

(local
 (defthm ix-append-list-cons
   (equal (append (append h (list e)) rest) (append h (cons e rest)))))

(local
 (defthm ix-build-preserves-correspondence
   (implies (and (ix-corr c h) (true-listp h) (true-listp events))
            (ix-corr (ix-build events c) (append h events)))
   :hints (("Goal" :induct (ix-model-build-induct events h c)
            :in-theory (e/d (ix-build) (ix-corr ix-append))
            :do-not-induct nil)
           ("Subgoal *1/1" :use ((:instance ix-append-preserves-corr
                                            (a h) (ev (car events))))))))

(local
 (defthm ix-empty-establishes-correspondence
   (implies (unsigned-byte-p 32 salt) (ix-corr (ix-empty salt) nil))
   :hints (("Goal" :in-theory (enable ix-corr ix-empty ix-cp
                                      ix-build)))))

; Shared fold boundary for alternate physical history implementations. The
; index is shared by ordinals while its events may reside in another backing.
(defthm ix-fold-establishes-correspondence
  (implies (and (true-listp h) (unsigned-byte-p 32 salt))
           (ix-corr (ix-build h (ix-empty salt)) h))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d nil
                                  (ix-corr ix-empty ix-build))
           :use ((:instance ix-build-preserves-correspondence
                            (events h) (h nil) (c (ix-empty salt)))))))

(local
 (defthm ix-build-bucket-below
   (implies (and (natp (nth 1 c))
                 (ix-below-p (ix-bucket key c) (nth 1 c)))
            (ix-below-p (ix-bucket key (ix-build events c))
                             (+ (nth 1 c) (len events))))
   :hints (("Goal" :induct (ix-build events c)
            :in-theory (e/d (ix-build)
                            (ix-bucket ix-append 
                              nth update-nth))))))

(defthm ix-fold-table-facts
  (let ((c (ix-build h (ix-empty salt))))
    (implies (and (true-listp h) (unsigned-byte-p 32 salt))
      (and (equal (nth 1 c) (len h))
           (<= (len h) (len (nth 0 c)))
           (equal (nth 3 c) salt)
           (ix-below-p (ix-bucket key c) (len h))
           (implies (and (natp seq) (< seq (len h)))
                    (equal (nth seq (nth 0 c)) (nth seq h))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable ix-empty ix-build ix-bucket nth)
           :use ((:instance ix-build-bucket-below
                            (events h) (c (ix-empty salt)))
                 (:instance ix-room-of-build
                            (a h) (s salt)
                            (c (ix-build h (ix-empty salt))))
                 (:instance ix-at-of-build
                            (a h) (s salt)
                            (c (ix-build h (ix-empty salt))))))))

(defthm ix-fold-mids-of-append
 (let* ((c (ix-build h (ix-empty salt)))
        (m (ix-key ev)))
  (implies (and (true-listp h) (unsigned-byte-p 32 salt))
   (equal (nth 2 (ix-build (append h (list ev)) (ix-empty salt)))
          (if (ix-keyp m)
              (let ((key (ix-hash m salt)))
               (cons (cons key (cons (len h) (cdr (hons-assoc-equal key (nth 2 c)))))
                     (nth 2 c)))
            (nth 2 c)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable ix-build ix-append ix-empty
                                      nth  ))))

(defthm ix-clear-preserves-corr
  (implies (and (ix-cp c) (unsigned-byte-p 32 salt))
           (ix-corr (ix-clear salt c) nil))
  :hints (("Goal" :in-theory (disable ix-corr ix-empty ix-clear)
           :use ((:instance ix-clear-is-empty)
                 (:instance ix-empty-establishes-correspondence)))))
