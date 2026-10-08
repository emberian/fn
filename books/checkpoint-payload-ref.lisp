; fn: the payload reference a paged-checkpoint tape row carries (lane
; s-pck-host, 2026-10-07; STORAGE-PROGRAM section 3.3, D41-STAGE5-ONE-ROW-IMAGE).
;
; A row of the events tape holds the record's metadata and a REF to its payload,
; not the payload octets.  The payloads live durably in the append-only file
; <store>/checkpoint.payloads (books/checkpoint-payloads.lisp, the payload-file
; lane).  This book is the interface both sides build to:
;
;   fn-cpl-refp REF          REF = (OFFSET LEN): OFFSET a natural byte offset into
;                            the payload file, LEN the payload's octet count.
;   fn-cpl-resolve REF FILE  the payload octets REF names in FILE (an octet
;                            list), or :absent when the file ends before
;                            OFFSET + LEN.
;
; The frame digest is checked by the extent digest path when the payload is
; realized; it is not part of the reference.

(in-package "ACL2")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/append" :dir :system))

(local (defthm cpl-nthcdr-len-append
  (equal (nthcdr (len a) (append a b)) b)))
(local (defthm cpl-take-len
  (implies (true-listp x) (equal (take (len x) x) x))))
(local (defthm cpl-take-append
  (implies (<= (nfix n) (len a))
           (equal (take n (append a b)) (take n a)))))
(local (defthm cpl-nthcdr-append
  (implies (<= (nfix n) (len a))
           (equal (nthcdr n (append a b)) (append (nthcdr n a) b)))))
(local (defthm cpl-len-nthcdr
  (implies (natp n) (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr)))))
(local (defthm cpl-len-append (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm cpl-take-len-append
  (implies (true-listp a) (equal (take (len a) (append a b)) a))))

(defun fn-cpl-refp (ref)
  (declare (xargs :guard t))
  (and (true-listp ref) (equal (len ref) 2)
       (natp (car ref)) (natp (cadr ref))))

(defun fn-cpl-ref (offset len)
  (declare (xargs :guard (and (natp offset) (natp len))))
  (list offset len))

(defun fn-cpl-resolve (ref file)
  (declare (xargs :guard (and (fn-cpl-refp ref) (true-listp file))))
  (if (and (fn-cpl-refp ref) (true-listp file)
           (<= (+ (car ref) (cadr ref)) (len file)))
      (take (cadr ref) (nthcdr (car ref) file))
    :absent))

(defthm fn-cpl-refp-of-ref
  (equal (fn-cpl-refp (fn-cpl-ref offset len)) (and (natp offset) (natp len))))

(defthm fn-cpl-resolve-of-ref-in-append
  ; A payload appended after PRE resolves to itself, whatever follows.
  (implies (and (true-listp pre) (true-listp payload) (true-listp post))
           (equal (fn-cpl-resolve (fn-cpl-ref (len pre) (len payload))
                                  (append pre payload post))
                  payload))
  :hints (("Goal" :in-theory (e/d (fn-cpl-ref) (cpl-nthcdr-append cpl-take-append))
           :do-not-induct t)))

(defthm fn-cpl-resolve-ignores-a-tail
  ; Octets past OFFSET + LEN (an uncommitted tail) do not change the answer.
  (implies (and (fn-cpl-refp ref) (true-listp file) (true-listp tail)
                (<= (+ (car ref) (cadr ref)) (len file)))
           (equal (fn-cpl-resolve ref (append file tail))
                  (fn-cpl-resolve ref file)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpl-refp) (cpl-nthcdr-append cpl-take-append))
           :use ((:instance cpl-nthcdr-append (n (car ref)) (a file) (b tail))
                 (:instance cpl-take-append (n (cadr ref)) (a (nthcdr (car ref) file)) (b tail))
                 (:instance cpl-len-nthcdr (n (car ref)) (x file))))))
