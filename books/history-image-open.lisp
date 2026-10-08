; Allocate the canonical store once, write its final header once, mark all
; pages dirty. The subsequent placement quanta never resize this store.
(in-package "ACL2")
(include-book "history-image-plan")
(include-book "history-image-cursors")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-his-layout (plan)
 (declare (xargs :guard (fn-his-planp plan)))
 (let* ((n (car plan)) (lens (cadr plan))
        (starts (adt-starts-l lens 1)) (np (adt-end-l lens 1)))
   (if (and (unsigned-byte-p 64 n) (fn-hp-u64-listp lens) (fn-hp-u64-listp starts)
            (unsigned-byte-p 64 (* 16384 np)))
       (mv nil starts np)
     (mv '(:refused :out-of-range) nil 0))))

(local
 (defthm fn-his-header-u64-append
  (implies (and (fn-hp-u64-listp x) (fn-hp-u64-listp y))
           (fn-hp-u64-listp (append x y)))))
(local
 (defthm fn-his-header-u64-zeros
  (fn-hp-u64-listp (adt-zeros n))
  :hints (("Goal" :in-theory (enable adt-zeros)))))
(local
 (defthm fn-his-header-u64-meta
  (implies (and (fn-hp-u64-listp lens) (fn-hp-u64-listp starts)
                (equal (len lens) (len starts)))
           (fn-hp-u64-listp (fn-hp-meta-words starts lens)))
  :hints (("Goal" :induct (fn-hp-meta-words starts lens)
           :in-theory (enable fn-hp-meta-words fn-hp-u64-listp len)))))

(defthm fn-his-hdr2-u64
 (implies (and (unsigned-byte-p 64 n) (unsigned-byte-p 64 np)
               (fn-hp-u64-listp lens) (fn-hp-u64-listp starts)
               (equal (len lens) (len starts)))
          (fn-hp-u64-listp (fn-hp-hdr2 n lens starts np)))
 :hints (("Goal" :in-theory (e/d (fn-hp-hdr2)
                                (fn-hp-meta-words adt-zeros)))))

(defun fn-his-image-open (plan pgs-mem)
 (declare (xargs :stobjs pgs-mem :guard (fn-his-planp plan)
                 :guard-hints (("Goal" :in-theory
                                (e/d (fn-his-layout fn-his-planp)
                                     (fn-hp-hdr2 fn-hp-x-put pgs-x-grow-image
                                      fn-hp-x-mark adt-end-l adt-starts-l floor))))))
 (if (not (and (equal (pgs-v-length pgs-mem) 0) (equal (pgs-d-length pgs-mem) 0)
               (equal (pgs-w-length pgs-mem) 0)))
     (mv '(:refused :image) nil 0 pgs-mem)
   (mv-let (v starts np) (fn-his-layout plan)
     (if v (mv v nil 0 pgs-mem)
       (let* ((pgs-mem (pgs-x-grow-image np pgs-mem))
              (pgs-mem (fn-hp-x-put 0 (fn-hp-hdr2 (car plan) (cadr plan) starts np) pgs-mem))
              (pgs-mem (fn-hp-x-mark 0 np pgs-mem)))
         (mv nil starts np pgs-mem))))))
