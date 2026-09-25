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

; The host's loop reads a header range, then the rest of that segment, then
; the next header, to end of file; each read is the previous range's
; successor, so the loop's output is the whole range by induction on this
; lemma.  The whole-file statement over the loop is not yet an event.
