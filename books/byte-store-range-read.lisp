; fn: range reads of one inode (P3, design 2026-09-25-bounds section 2.4
; item 1).
;
; `fn-bs-read' (byte-store.lisp) returns an inode's whole content.  A range
; read returns OFF..OFF+N of it, or what remains when the file is shorter
; (the short read at end of file).  A read is not a transition, so within
; one state consecutive ranges are a list fact; across the states the host
; observes between its reads they concatenate only under
; A-HOST-EXCLUSIVE-READ (books/assumptions.lisp), which the keystones name.
(in-package "ACL2")
(include-book "assumptions")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-bs-read-range (s ino off n)
  (declare (xargs :guard (and (natp off) (natp n)) :verify-guards nil))
  (let ((rest (nthcdr off (true-list-fix (fn-bs-content s ino)))))
    (if (< (len rest) n) rest (take n rest))))

(local
 (defthm fn-bs-rr-take-append-nthcdr
   (implies (and (natp n) (natp m) (<= (+ n m) (len x)))
            (equal (append (take n x) (take m (nthcdr n x)))
                   (take (+ n m) x)))
   :hints (("Goal" :induct (nthcdr n x)))))

(local
 (defthm fn-bs-rr-nthcdr-nthcdr
   (implies (and (natp a) (natp b))
            (equal (nthcdr a (nthcdr b x)) (nthcdr (+ a b) x)))))

(local
 (defthm fn-bs-rr-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

(local
 (defthm fn-bs-rr-nthcdr-nil
   (equal (nthcdr n nil) nil)))

(local
 (defthm fn-bs-rr-len-nthcdr
   (implies (natp n)
            (equal (len (nthcdr n x)) (nfix (- (len x) n))))
   :hints (("Goal" :induct (nthcdr n x)))))

(local
 (defthm fn-bs-rr-append-take-rest
   (implies (and (natp n) (<= n (len x)) (true-listp x))
            (equal (append (take n x) (nthcdr n x)) x))))

(local
 (defthm fn-bs-rr-true-listp-nthcdr
   (implies (true-listp x) (true-listp (nthcdr n x)))))

(local
 (defthm fn-bs-rr-append-take-rest-off
   (implies (and (natp n) (natp off) (<= (+ n off) (len x)) (true-listp x))
            (equal (append (take n (nthcdr off x)) (nthcdr (+ n off) x))
                   (nthcdr off x)))
   :hints (("Goal" :use ((:instance fn-bs-rr-append-take-rest (x (nthcdr off x)))
                         (:instance fn-bs-rr-nthcdr-nthcdr (a n) (b off)))
            :in-theory (disable fn-bs-rr-append-take-rest fn-bs-rr-nthcdr-nthcdr)))))

(local
 (defthm fn-bs-rr-take-append-off
   (implies (and (natp n) (natp m) (natp off) (<= (+ n m off) (len x)))
            (equal (append (take n (nthcdr off x)) (take m (nthcdr (+ n off) x)))
                   (take (+ m n) (nthcdr off x))))
   :hints (("Goal" :use ((:instance fn-bs-rr-take-append-nthcdr (x (nthcdr off x)))
                         (:instance fn-bs-rr-nthcdr-nthcdr (a n) (b off)))
            :in-theory (disable fn-bs-rr-take-append-nthcdr fn-bs-rr-nthcdr-nthcdr)))))

; Two consecutive ranges, the second read in a later state, are one range
; of the first state's content.
(defthm fn-bs-read-ranges-concatenate
  (implies (and (fn-assume-host-exclusive-read s0 s1 ino)
                (natp off) (natp n) (natp m)
                (<= (+ off n) (len (fn-bs-content s0 ino))))
           (equal (append (fn-bs-read-range s0 ino off n)
                          (fn-bs-read-range s1 ino (+ off n) m))
                  (fn-bs-read-range s0 ino off (+ n m))))
  :hints (("Goal" :in-theory (disable fn-assume-host-exclusive-read-keeps-content
                               fn-bs-content)
           :use ((:instance fn-assume-host-exclusive-read-keeps-content
                            (before s0) (after s1))))))

; -----------------------------------------------------------------------------
; The whole-file statement over the host's loop (lane byte-model, PKT-043).
;
; fnn-state-checkpoint-plan (host/native/io.lisp) reads the file as a chain
; of consecutive ranges on one descriptor under the store lock: a segment
; header, that segment's chunk, its trailer, the next header, to the end of
; the file; each read runs in a later state, and consecutive states are
; related by A-HOST-EXCLUSIVE-READ (fn-assume-host-exclusive-read: nothing
; changes the content between two of the loop's reads).  fn-bs-read-ranges
; is the loop's output: the concatenation of the ranges, each read in its
; own state; fn-bs-exclusive-chainp is the assumption over the chain of
; states.  The lengths LENS are whatever the loop decides (the header's
; declared chunk length): the statement holds for every length list that
; fits the file.

(defun fn-bs-exclusive-chainp (states ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp states) (consp (cdr states)))
      (and (fn-assume-host-exclusive-read (car states) (cadr states) ino)
           (fn-bs-exclusive-chainp (cdr states) ino))
    t))

(defun fn-bs-sum-lens (lens)
  (declare (xargs :guard t))
  (if (consp lens) (+ (nfix (car lens)) (fn-bs-sum-lens (cdr lens))) 0))

(defun fn-bs-read-ranges (states ino off lens)
  (declare (xargs :guard (natp off) :verify-guards nil))
  (if (and (consp lens) (consp states))
      (append (fn-bs-read-range (car states) ino off (nfix (car lens)))
              (fn-bs-read-ranges (cdr states) ino (+ off (nfix (car lens))) (cdr lens)))
    nil))

(local
 (defthm fn-bs-rr-read-range-true-listp
   (true-listp (fn-bs-read-range s ino off n))))

(local
 (defthm fn-bs-rr-read-range-of-zero
   (equal (fn-bs-read-range s ino off 0) nil)))

(local
 (defthm fn-bs-rr-sum-lens-natp
   (natp (fn-bs-sum-lens lens))
   :rule-classes :type-prescription))

; A state per read: the loop runs one read in each state of the chain.
(defun fn-bs-states-cover-p (states lens)
  (declare (xargs :guard t))
  (if (consp lens)
      (and (consp states) (fn-bs-states-cover-p (cdr states) (cdr lens)))
    t))

; The ranges of one content, no state: what fn-bs-read-range reads of it.
(defun fn-bs-range-of (c off n)
  (declare (xargs :guard (and (natp off) (natp n)) :verify-guards nil))
  (let ((rest (nthcdr off (true-list-fix c))))
    (if (< (len rest) n) rest (take n rest))))

(defun fn-bs-ranges-of (c off lens)
  (declare (xargs :guard (natp off) :verify-guards nil))
  (if (consp lens)
      (append (fn-bs-range-of c off (nfix (car lens)))
              (fn-bs-ranges-of c (+ off (nfix (car lens))) (cdr lens)))
    nil))

(defthm fn-bs-read-range-is-the-range-of-the-content
  (equal (fn-bs-read-range s ino off n)
         (fn-bs-range-of (fn-bs-content s ino) off n)))

(local
 (defthm fn-bs-rr-ranges-of-concatenate
   (implies (and (natp off) (natp n) (natp m) (<= (+ off n) (len c)))
            (equal (append (fn-bs-range-of c off n) (fn-bs-range-of c (+ off n) m))
                   (fn-bs-range-of c off (+ n m))))))

(local
 (defthm fn-bs-rr-range-of-zero
   (equal (fn-bs-range-of c off 0) nil)))

(local
 (defthm fn-bs-rr-range-of-true-listp
   (true-listp (fn-bs-range-of c off n))))

(local
 (defthm fn-bs-rr-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

; Consecutive ranges of one content are one range.
(defthm fn-bs-ranges-of-is-the-range
  (implies (and (nat-listp lens) (natp off) (<= (+ off (fn-bs-sum-lens lens)) (len c)))
           (equal (fn-bs-ranges-of c off lens)
                  (fn-bs-range-of c off (fn-bs-sum-lens lens))))
  :hints (("Goal" :induct (fn-bs-ranges-of c off lens)
           :in-theory (union-theories
                       '(fn-bs-ranges-of fn-bs-sum-lens nat-listp natp nfix
                         fn-bs-rr-ranges-of-concatenate fn-bs-rr-sum-lens-natp
                         fn-bs-rr-range-of-zero fn-bs-rr-range-of-true-listp
                         fn-bs-rr-append-nil (:type-prescription len))
                       (theory 'minimal-theory)))))

; Over a chain of exclusive reads, every read sees the first state's
; content: the loop's output is that content's ranges.
(defthm fn-bs-read-ranges-over-a-chain-read-the-first-content
  (implies (and (fn-bs-exclusive-chainp states ino)
                (fn-bs-states-cover-p states lens)
                (consp states))
           (equal (fn-bs-read-ranges states ino off lens)
                  (fn-bs-ranges-of (fn-bs-content (car states) ino) off lens)))
  :hints (("Goal" :induct (fn-bs-read-ranges states ino off lens)
           :in-theory (union-theories
                       '(fn-bs-read-ranges fn-bs-ranges-of fn-bs-exclusive-chainp
                         fn-bs-states-cover-p fn-bs-read-range-is-the-range-of-the-content
                         fn-assume-host-exclusive-read-keeps-content
                         fn-bs-rr-range-of-true-listp fn-bs-rr-append-nil)
                       (theory 'minimal-theory)))))

; The loop's output over a chain of states is one range of the first
; state's content: the induction the pairwise lemma promised.
(defthm fn-bs-read-ranges-is-the-range
  (implies (and (fn-bs-exclusive-chainp states ino)
                (fn-bs-states-cover-p states lens)
                (consp states)
                (nat-listp lens)
                (natp off)
                (<= (+ off (fn-bs-sum-lens lens)) (len (fn-bs-content (car states) ino))))
           (equal (fn-bs-read-ranges states ino off lens)
                  (fn-bs-read-range (car states) ino off (fn-bs-sum-lens lens))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bs-range-of fn-bs-content fn-bs-read-ranges fn-bs-ranges-of
                               fn-bs-exclusive-chainp fn-bs-states-cover-p))))

(local
 (defthm fn-bs-rr-take-len
   (implies (and (true-listp x) (equal (len x) n)) (equal (take n x) x))))

; The whole file: the ranges from offset 0 whose lengths sum to the file's
; length read the file's content, as fnn-state-checkpoint-plan reads a
; checkpoint to its end.
(defthm fn-bs-read-ranges-read-the-whole-file
  (implies (and (fn-bs-exclusive-chainp states ino)
                (fn-bs-states-cover-p states lens)
                (consp states)
                (nat-listp lens)
                (equal (fn-bs-sum-lens lens) (len (fn-bs-content (car states) ino))))
           (equal (fn-bs-read-ranges states ino 0 lens)
                  (true-list-fix (fn-bs-content (car states) ino))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-read-ranges-is-the-range (off 0)))
           :in-theory (e/d (fn-bs-range-of)
                           (fn-bs-content fn-bs-read-ranges fn-bs-exclusive-chainp
                            fn-bs-states-cover-p fn-bs-read-ranges-is-the-range)))))
