; fn: a consumer of the catalog prototype, certified ONCE against the generic
; (wave 5, lane consolidation-design, 2026-09-26).
;
; This book stands for every book above the catalog interface: it takes
; `fn-pcat' as a stobj formal, calls its exports, and proves theorems over
; the logical view.  Nothing here names a foundation.  Whether the image
; runs it over the list-backed foundation or over the arena
; (books/proto-catalog-arena.lisp) is decided where `fn-pcat' is introduced,
; and this book's certificate is the same either way: that is the property
; the prototype measures (the design's section 3).
;
; Two operations, the shape of the catalog's own: a fold that seals many
; payloads (open: a seal per retained record), and a SCALAR TOTAL, the
; octets held below a handle, advanced from a delta (gpt-6 section 6:
; "scalar totals advance from committed deltas"): `fn-pcat-total' after a
; seal is the total before it plus the sealed payload's length, without a
; walk of what was already there (`fn-pcat-total-of-seal-is-delta').

(in-package "ACL2")
(include-book "proto-catalog")

(defun fn-pcat-seal-many (payloads fn-pcat)
  (declare (xargs :stobjs fn-pcat :guard (fn-arn-payload-listp payloads)))
  (if (atom payloads)
      fn-pcat
    (let ((fn-pcat (fn-pcat-seal-list (car payloads) fn-pcat)))
      (fn-pcat-seal-many (cdr payloads) fn-pcat))))

; The octets held by the handles below H.
(defun fn-pcat-total (h fn-pcat)
  (declare (xargs :stobjs fn-pcat
                  :guard (and (natp h) (<= h (fn-pcat-count fn-pcat)))
                  :guard-hints (("Goal" :in-theory (enable fn-pcat-count fn-pcat-payload-len)))))
  (if (zp h)
      0
    (+ (fn-pcat-payload-len (- h 1) fn-pcat)
       (fn-pcat-total (- h 1) fn-pcat))))

(local
 (defthm fn-pcat-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; The seal keeps every handle it found (the arena's keystone, restated over
; the generic's names: a reader that pinned h before the fold reads the
; same octets after it).
(defthm fn-pcat-seal-many-is-append
  (implies (and (true-listp fn-pcat) (true-listp payloads))
           (equal (fn-pcat-seal-many payloads fn-pcat) (append fn-pcat payloads)))
  :hints (("Goal" :induct (fn-pcat-seal-many payloads fn-pcat)
           :in-theory (enable fn-pcat-seal-list))))

(local
 (defthm fn-pcat-nth-of-append-below
   (implies (and (natp h) (< h (len a)))
            (equal (nth h (append a b)) (nth h a)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-pcat-seal-many-keeps-sealed
  (implies (and (fn-pcat-p fn-pcat) (natp h) (< h (fn-pcat-count fn-pcat)))
           (equal (fn-pcat-payload h (fn-pcat-seal-many payloads fn-pcat))
                  (fn-pcat-payload h fn-pcat)))
  :hints (("Goal" :in-theory (e/d (fn-pcat-payload fn-pcat-count fn-pcat-p-is-payload-listp)
                                  (fn-pcat-seal-many))
           :use ((:instance fn-pcat-seal-many-is-append
                            (payloads (true-list-fix payloads))))
           :do-not-induct t)))

; The total below the old count, after one seal, is unchanged (the seal
; wrote above it); the total below the new count is the old total plus the
; delta.  Proved without walking: the fold on the sealed value is the fold
; on the old value below the old count.
(local
 (defthm fn-pcat-total-of-append-below
   (implies (and (natp h) (<= h (len a)) (true-listp a))
            (equal (fn-pcat-total h (append a b)) (fn-pcat-total h a)))
   :hints (("Goal" :in-theory (enable fn-pcat-payload-len)))))

(local
 (defthm fn-pcat-nth-len-of-append-one
   (implies (true-listp a)
            (equal (nth (len a) (append a (list xs))) xs))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-pcat-total-of-seal-is-delta
  (implies (fn-pcat-p fn-pcat)
           (equal (fn-pcat-total (+ 1 (fn-pcat-count fn-pcat))
                                 (fn-pcat-seal-list xs fn-pcat))
                  (+ (len xs) (fn-pcat-total (fn-pcat-count fn-pcat) fn-pcat))))
  :hints (("Goal" :in-theory (e/d (fn-pcat-count fn-pcat-seal-list fn-pcat-payload-len
                                   fn-pcat-p-is-payload-listp)
                                  (fn-pcat-total))
           :expand ((fn-pcat-total (+ 1 (len fn-pcat)) (append fn-pcat (list xs))))
           :do-not-induct t)))
