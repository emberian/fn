; fn: cursor fragmentation of a bounded BP payload.
;
; The reference in bp-fragment.lisp selects each byte with nth from the
; original payload.  This cut threads the unconsumed suffix, so its work is
; at most two traversals of the payload plus one traversal of the cut list.

(in-package "ACL2")
(include-book "bp-fragment")

(defun fn-bpf-prefix (xs n)
  (declare (xargs :guard (and (true-listp xs) (natp n))
                  :measure (nfix n)))
  (if (zp n)
      nil
    (cons (car xs) (fn-bpf-prefix (cdr xs) (1- n)))))

(defun fn-bpf-cut-fast (rest from boundaries total)
  (declare (xargs :guard (and (true-listp rest) (natp from) (natp total))
                  :measure (acl2-count boundaries)))
  (if (consp boundaries)
      (let ((n (nfix (- (nfix (car boundaries)) from))))
        (cons (fn-bpf-make from (fn-bpf-prefix rest n) total)
              (fn-bpf-cut-fast (nthcdr n rest)
                               (nfix (car boundaries))
                               (cdr boundaries) total)))
    (list (fn-bpf-make from (fn-bpf-prefix rest (nfix (- total from)))
                       total))))

(defun fn-bpf-fragment-fast (payload boundaries)
  (declare (xargs :guard t))
  (if (not (and (fn-cbor-octet-listp payload)
                (consp payload)
                (<= (len payload) *fn-bpf-max-length*)
                (fn-bpf-boundariesp boundaries 0 (len payload))
                (< (len boundaries) *fn-bpf-max-fragments*)))
      (list :invalid :bounds)
    (list :ok (fn-bpf-cut-fast payload 0 boundaries (len payload)))))

(verify-guards fn-bpf-prefix)
(verify-guards fn-bpf-cut-fast)
(verify-guards fn-bpf-fragment-fast)

; The cursor at `from` is the unconsumed suffix of the original payload.
(defthm fn-bpf-cdr-of-nthcdr
  (implies (natp from)
           (equal (cdr (nthcdr from xs)) (nthcdr (+ 1 from) xs)))
  :hints (("Goal" :induct (nthcdr from xs))))

(defthm fn-bpf-car-of-nthcdr-fast
  (equal (car (nthcdr n xs)) (nth n xs))
  :hints (("Goal" :induct (nthcdr n xs))))

(local
 (defun fn-bpf-prefix-extent-induction (payload from n)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list payload from n)
     (fn-bpf-prefix-extent-induction payload (+ 1 from) (1- n)))))

(defthm fn-bpf-extent-empty
  (equal (fn-bpf-extent payload from from) nil)
  :hints (("Goal" :expand ((fn-bpf-extent payload from from)))))

(defthm fn-bpf-prefix-is-extent
  (implies (and (natp from) (natp n))
           (equal (fn-bpf-prefix (nthcdr from payload) n)
                  (fn-bpf-extent payload from (+ from n))))
  :hints (("Goal" :induct (fn-bpf-prefix-extent-induction payload from n)
           :in-theory (disable mod-x-y-=-x+y-for-rationals))))

(defthm fn-bpf-nthcdr-of-nthcdr-fast
  (implies (and (natp from) (natp n))
           (equal (nthcdr n (nthcdr from xs))
                  (nthcdr (+ from n) xs)))
  :hints (("Goal" :induct (nthcdr n (nthcdr from xs)))))

(local
 (defthm fn-bpf-plus-minus-cancel
   (implies (acl2-numberp from)
            (equal (+ from (- total from)) (fix total)))))

(local
 (defthm fn-bpf-plus-neg-cancel
   (implies (acl2-numberp from)
            (equal (+ from (- from) total) (fix total)))))

(defthm fn-bpf-cut-fast-is-cut
  (implies (and (natp from) (natp total) (<= from total)
                (fn-bpf-boundariesp boundaries from total))
           (equal (fn-bpf-cut-fast (nthcdr from payload)
                                   from boundaries total)
                  (fn-bpf-cut payload from boundaries total)))
  :hints (("Goal" :induct (fn-bpf-cut payload from boundaries total)
           :in-theory (disable mod-x-y-=-x+y-for-rationals))))

(defthm fn-bpf-fragment-fast-is-fragment
  (equal (fn-bpf-fragment-fast payload boundaries)
         (fn-bpf-fragment payload boundaries))
  :hints (("Goal" :use ((:instance fn-bpf-cut-fast-is-cut
                                   (from 0) (total (len payload))))
           :in-theory (disable fn-bpf-cut-fast-is-cut))))
