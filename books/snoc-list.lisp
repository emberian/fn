;; fn: a list held newest-first, so that appending one element is one cons.
;
; The Store's durable history (books/store-files.lisp fn-sf-records) and its
; success history (fn-sf-successes) grow by one element at the END per
; committed POST: (append records (list record)).  Held as ordinary lists,
; every commit copies the whole history -- N conses per POST, the only
; N-dependent allocation of an owner POST (post-alloc, 2026-09-27: ~22 B x N;
; the success history grows with every POST since open).  No list
; representation appends at the end in O(1), so the kernel state holds each
; of the two as a snoc-list instead:
;
;   (:snoc N . REV)   the list (fn-sl-rev-onto REV nil) of N elements, newest
;                     first in REV;
;   (:raw . X)        X itself, for a value that is not a true list (the
;                     kernel's accessors are total, so a non-list must round-
;                     trip too).
;
; fn-sl-of builds the representation of a list, fn-sl-list reads it back
; (fn-sl-list-of-fn-sl-of: every value round-trips), and fn-sl-snoc appends
; one element: one cons and one increment on a snoc form
; (fn-sl-list-of-fn-sl-snoc: the list it represents is the append, for every
; value; fn-sl-snoc-of-fn-sl-of: it is the representation of the appended
; list, for every list).  fn-sl-canonp says a value is the representation of
; the list it represents; fn-sl-count and fn-sl-last read the length and the
; last element in O(1) and equal len and (car (last ...)) of the list under
; it (the last one for every value).
;
; The logical model stays the list: nothing above store-files sees a snoc-list.

(in-package "ACL2")

(defun fn-sl-rev-onto (x acc)
  (declare (xargs :guard t))
  (if (consp x)
      (fn-sl-rev-onto (cdr x) (cons (car x) acc))
    acc))

(defun fn-sl-of (x)
  (declare (xargs :guard t))
  (if (true-listp x)
      (list* :snoc (len x) (fn-sl-rev-onto x nil))
    (cons :raw x)))

(defun fn-sl-snoc-formp (h)
  (declare (xargs :guard t))
  (and (consp h) (eq (car h) :snoc) (consp (cdr h))))

(defun fn-sl-list (h)
  (declare (xargs :guard t))
  (if (fn-sl-snoc-formp h)
      (fn-sl-rev-onto (cddr h) nil)
    (if (consp h) (cdr h) nil)))

; append with (list r), total.
(defun fn-sl-append1 (x r)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x) (fn-sl-append1 (cdr x) r))
    (list r)))

(defun fn-sl-snoc (h r)
  (declare (xargs :guard t))
  (if (fn-sl-snoc-formp h)
      (list* :snoc (1+ (nfix (cadr h))) r (cddr h))
    (fn-sl-of (fn-sl-append1 (fn-sl-list h) r))))

(defun fn-sl-canonp (h)
  (declare (xargs :guard t))
  (equal (fn-sl-of (fn-sl-list h)) h))

(defun fn-sl-count (h)
  (declare (xargs :guard t))
  (if (fn-sl-snoc-formp h)
      (nfix (cadr h))
    (len (fn-sl-list h))))

(defun fn-sl-last-elem (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (consp (cdr x)) (fn-sl-last-elem (cdr x)) (car x))
    nil))

(defun fn-sl-last (h)
  (declare (xargs :guard t))
  (if (fn-sl-snoc-formp h)
      (if (consp (cddr h)) (car (cddr h)) nil)
    (fn-sl-last-elem (fn-sl-list h))))

; The I-th element (the oldest is 0), total.  On a snoc form it is the
; (N-1-I)-th of REV: the newest elements are the nearest.
(defun fn-sl-nth-elem (k x)
  (declare (xargs :guard (natp k)))
  (if (consp x)
      (if (zp k) (car x) (fn-sl-nth-elem (1- k) (cdr x)))
    nil))

(defun fn-sl-nth (i h)
  (declare (xargs :guard (natp i)))
  (if (fn-sl-snoc-formp h)
      (let ((n (nfix (cadr h))))
        (if (< (nfix i) n) (fn-sl-nth-elem (- n (+ 1 (nfix i))) (cddr h)) nil))
    (fn-sl-nth-elem i (fn-sl-list h))))

; -----------------------------------------------------------------------------
; The list facts.

(local
 (defthm fn-sl-rev-onto-true-listp
   (implies (true-listp acc) (true-listp (fn-sl-rev-onto x acc)))))

(local
 (defthm fn-sl-rev-onto-len
   (equal (len (fn-sl-rev-onto x acc)) (+ (len x) (len acc)))))

;; The accumulator comes out as a tail.
(local
 (defthm fn-sl-rev-onto-append
   (equal (fn-sl-rev-onto x (append a b))
          (append (fn-sl-rev-onto x a) b))))

(local
 (defthm fn-sl-rev-onto-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-sl-rev-onto x acc)
                   (append (fn-sl-rev-onto x nil) acc)))
   :hints (("Goal" :use ((:instance fn-sl-rev-onto-append (a nil) (b acc)))
            :in-theory (disable fn-sl-rev-onto-append)))))

(local
 (defthm fn-sl-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-sl-rev-onto-of-append
   (equal (fn-sl-rev-onto (append a b) nil)
          (append (fn-sl-rev-onto b nil) (fn-sl-rev-onto a nil)))
   :hints (("Goal" :induct (fn-sl-rev-onto a acc)))))

(local
 (defthm fn-sl-rev-onto-twice
   (implies (true-listp x)
            (equal (fn-sl-rev-onto (fn-sl-rev-onto x nil) nil) x))
   :hints (("Goal" :induct (fn-sl-rev-onto x acc)))))

(defthm fn-sl-append1-is-append
  (equal (fn-sl-append1 x r) (append x (list r))))

(local
 (defthm fn-sl-true-listp-append1
   (true-listp (append x (list r)))))

; KEYSTONE (representation).  Every value round-trips.
(defthm fn-sl-list-of-fn-sl-of
  (equal (fn-sl-list (fn-sl-of x)) x))

; KEYSTONE (append).  The snoc is the append, for every value.
(defthm fn-sl-list-of-fn-sl-snoc
  (equal (fn-sl-list (fn-sl-snoc h r))
         (append (fn-sl-list h) (list r))))

; KEYSTONE (the O(1) step is the representation of the appended list).
(defthm fn-sl-snoc-of-fn-sl-of
  (equal (fn-sl-snoc (fn-sl-of x) r)
         (fn-sl-of (append x (list r)))))

(defthm fn-sl-canonp-of-fn-sl-of
  (fn-sl-canonp (fn-sl-of x)))

(defthm fn-sl-of-list-when-canonp
  (implies (fn-sl-canonp h)
           (equal (fn-sl-of (fn-sl-list h)) h)))

(defthm fn-sl-canonp-of-fn-sl-snoc
  (implies (fn-sl-canonp h)
           (fn-sl-canonp (fn-sl-snoc h r)))
  :hints (("Goal" :in-theory (disable fn-sl-snoc fn-sl-of fn-sl-list)
           :use ((:instance fn-sl-snoc-of-fn-sl-of (x (fn-sl-list h)))))))

(defthm fn-sl-count-is-len
  (implies (fn-sl-canonp h)
           (equal (fn-sl-count h) (len (fn-sl-list h)))))

(local
 (defthm fn-sl-last-elem-is-car-last
   (equal (fn-sl-last-elem x) (car (last x)))))

(local
 (defthm fn-sl-car-last-of-rev-onto
   (equal (car (last (fn-sl-rev-onto x acc)))
          (if (consp acc) (car (last acc)) (if (consp x) (car x) nil)))
   :hints (("Goal" :induct (fn-sl-rev-onto x acc)))))

(defthm fn-sl-last-is-last
  (equal (fn-sl-last h) (car (last (fn-sl-list h)))))

(local
 (defthm fn-sl-nth-elem-is-nth
   (equal (fn-sl-nth-elem k x) (nth k x))))

(local
 (defthm fn-sl-nth-of-rev-onto
   (implies (natp i)
            (equal (nth i (fn-sl-rev-onto x acc))
                   (if (< i (len x))
                       (nth (- (len x) (+ 1 i)) x)
                     (nth (- i (len x)) acc))))
   :hints (("Goal" :induct (fn-sl-rev-onto x acc)
            :in-theory (disable fn-sl-rev-onto-acc)))))

(defthm fn-sl-nth-is-nth
  (implies (and (fn-sl-canonp h) (natp i))
           (equal (fn-sl-nth i h) (nth i (fn-sl-list h))))
  :hints (("Goal" :in-theory (disable fn-sl-rev-onto-acc))))

(in-theory (disable fn-sl-rev-onto fn-sl-of fn-sl-snoc-formp fn-sl-list
                    fn-sl-append1 fn-sl-snoc fn-sl-canonp fn-sl-count
                    fn-sl-last-elem fn-sl-last fn-sl-nth-elem fn-sl-nth))
