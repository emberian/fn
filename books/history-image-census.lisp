; Census reduction after a resumable codec finishes ONE captured record.
; The source may be based disk history plus snoc suffix; no source list is
; retained, traversed or materialized by these scalar operations.
(in-package "ACL2")
(include-book "history-pages-row")

(defun fn-hcc-begin ()
  (declare (xargs :guard t))
  (mv 0 0))

(defun fn-hcc-row (count pool ordinal encoded)
  ; COUNT/POOL are the previous census, ORDINAL the source cursor's completed
  ; row ordinal, ENCODED its exact codec byte count. Never call fn-scc-encode
  ; merely to supply ENCODED here. Capture/lease stays in the enclosing cursor.
  (declare (xargs :guard (and (natp count) (natp pool)
                              (natp ordinal) (natp encoded))))
  (cond
   ((not (equal ordinal count)) (mv :stale count pool))
   ((or (<= 18446744073709551616 count)
        (<= 18446744073709551616 pool)
        (<= 18446744073709551616 encoded))
    (mv :out-of-range count pool))
   (t
    (let ((count2 (+ 1 count))
          (pool2 (+ pool encoded (fn-hp-pad8-count encoded))))
      (if (or (<= 18446744073709551616 (* 8 count2))
              (<= 18446744073709551616 pool2))
          (mv :out-of-range count pool)
        (mv :counted count2 pool2))))))

(defun fn-hcc-lens (count pool)
  (declare (xargs :guard (and (natp count) (natp pool))))
  (list (* 8 count) (* 8 count) (* 8 count) (* 8 count) pool))

(defthm fn-hcc-refusal-keeps-census
  (implies (not (equal (mv-nth 0 (fn-hcc-row count pool ordinal encoded)) :counted))
           (and (equal (mv-nth 1 (fn-hcc-row count pool ordinal encoded)) count)
                (equal (mv-nth 2 (fn-hcc-row count pool ordinal encoded)) pool)))
  :hints (("Goal" :in-theory (disable fn-hp-pad8-count))))

(local
 (defthm fn-hcc-pes-len-append1
   (equal (fn-hp-pes-len (append h (list ev)))
          (+ (fn-hp-pes-len h) (len (fn-hp-pe ev))))
   :hints (("Goal" :induct (fn-hp-pes-len h)
            :in-theory (disable fn-hp-pe)))))

; Named composition seam: the source decoder/codec must establish the exact
; ENCODED equality. It is proof vocabulary, never an executable preflight.
(defthm fn-hcc-counted-row-preserves-history-census
  (implies (and (equal count (len h)) (equal pool (fn-hp-pes-len h))
                (equal encoded (len (fn-scc-encode ev)))
                (equal (mv-nth 0 (fn-hcc-row count pool ordinal encoded)) :counted))
           (and (equal (mv-nth 1 (fn-hcc-row count pool ordinal encoded))
                       (len (append h (list ev))))
                (equal (mv-nth 2 (fn-hcc-row count pool ordinal encoded))
                       (fn-hp-pes-len (append h (list ev))))))
  :hints (("Goal" :in-theory (e/d (fn-hp-pe)
                                     (fn-scc-encode fn-hp-pad8 fn-hp-pad8-count
                                      fn-hp-pes-len)))))

(local
 (defthm fn-hcc-list5
   (implies (and (true-listp x) (equal (len x) 5))
            (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)) x))
   :hints (("Goal" :in-theory (e/d (nth) (len true-listp))
            :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
                     (len (cddddr x)) (len (cdr (cddddr x)))
                     (true-listp x) (true-listp (cdr x)) (true-listp (cddr x))
                     (true-listp (cdddr x)) (true-listp (cddddr x))
                     (true-listp (cdr (cddddr x))))))))

(defthm fn-hcc-lens-refines-history-regions
  (implies (and (fn-hp-okp h salt) (equal count (len h))
                (equal pool (fn-hp-pes-len h)))
           (equal (fn-hcc-lens count pool) (fn-hp-lens h salt)))
  :hints (("Goal"
           :use ((:instance fn-hcc-list5 (x (fn-hp-lens h salt)))
                 (:instance fn-hp-lens-col-sizes (r 0))
                 (:instance fn-hp-lens-col-sizes (r 1))
                 (:instance fn-hp-lens-col-sizes (r 2))
                 (:instance fn-hp-lens-col-sizes (r 3)))
           :in-theory (e/d (fn-hcc-lens)
                            (fn-hp-lens fn-hp-okp fn-hp-pes-len
                             fn-hp-lens-col-sizes fn-hcc-list5)))))

(in-theory (disable fn-hcc-row fn-hcc-lens))

; Two instances suffice: all four scalar columns have the same used length.
; One tick doubles a scalar once; no recursive capacity routine executes.
(defun fn-hcc-cap-begin (used)
  (declare (xargs :guard (and (natp used) (< used 18446744073709551616))))
  (mv (ceiling used 16384) (if (zp used) 0 1)))

(defun fn-hcc-cap-tick (need cap)
  (declare (xargs :guard (and (natp need) (< need 1125899906842625)
                              (natp cap) (< cap 2251799813685248))))
  (cond ((<= need cap) (mv :done cap))
        ((zp cap) (mv :invalid cap))
        (t (mv :continue (* 2 cap)))))

(defthm fn-hcc-cap-begin-refines-capacity
  (equal (mv-nth 1 (fn-hcc-cap-begin used))
         (if (zp used) (adt-cap used) 1))
  :hints (("Goal" :in-theory (enable adt-cap))))

(defthm fn-hcc-cap-tick-preserves-residual
  (implies (and (natp need) (posp cap)
                (equal (mv-nth 0 (fn-hcc-cap-tick need cap)) :continue))
           (equal (adt-pow2-at-least need (mv-nth 1 (fn-hcc-cap-tick need cap)))
                  (adt-pow2-at-least need cap)))
  :hints (("Goal" :expand ((adt-pow2-at-least need cap))
           :in-theory (disable adt-pow2-at-least))))

(defthm fn-hcc-cap-tick-terminal
  (implies (and (natp need) (posp cap)
                (equal (mv-nth 0 (fn-hcc-cap-tick need cap)) :done))
           (equal (mv-nth 1 (fn-hcc-cap-tick need cap))
                  (adt-pow2-at-least need cap)))
  :hints (("Goal" :expand ((adt-pow2-at-least need cap))
           :in-theory (disable adt-pow2-at-least))))

(defun fn-hcc-starts (column-cap)
  (declare (xargs :guard (natp column-cap)))
  (list 1 (+ 1 column-cap) (+ 1 (* 2 column-cap))
        (+ 1 (* 3 column-cap)) (+ 1 (* 4 column-cap))))

(defun fn-hcc-pages (column-cap pool-cap)
  (declare (xargs :guard (and (natp column-cap) (natp pool-cap))))
  (+ 1 (* 4 column-cap) pool-cap))

(defthm fn-hcc-starts-refines-canonical-placement
  (implies (and (natp count) (natp pool)
                (equal column-cap (adt-cap (* 8 count))))
           (equal (fn-hcc-starts column-cap)
                  (adt-starts-l (fn-hcc-lens count pool) 1)))
  :hints (("Goal" :in-theory (e/d (fn-hcc-lens adt-starts-l)
                                    (adt-cap)))))

(defthm fn-hcc-pages-refines-canonical-placement
  (implies (and (natp count) (natp pool)
                (equal column-cap (adt-cap (* 8 count)))
                (equal pool-cap (adt-cap pool)))
           (equal (fn-hcc-pages column-cap pool-cap)
                  (adt-end-l (fn-hcc-lens count pool) 1)))
  :hints (("Goal" :in-theory (e/d (fn-hcc-lens adt-end-l)
                                    (adt-cap)))))

(in-theory (disable fn-hcc-cap-begin fn-hcc-cap-tick
                    fn-hcc-starts fn-hcc-pages))

(defthm fn-hcc-cap-begin-nonempty-denotation
  (implies (posp used)
           (equal (adt-pow2-at-least (mv-nth 0 (fn-hcc-cap-begin used))
                                    (mv-nth 1 (fn-hcc-cap-begin used)))
                  (adt-cap used)))
  :hints (("Goal" :in-theory (e/d (fn-hcc-cap-begin adt-cap)
                                     (adt-pow2-at-least)))))

(defthm fn-hcc-cap-tick-preserves-width
  (implies (and (natp need) (< need 1125899906842625)
                (natp cap) (< cap 2251799813685248))
           (and (natp (mv-nth 1 (fn-hcc-cap-tick need cap)))
                (< (mv-nth 1 (fn-hcc-cap-tick need cap)) 2251799813685248)))
  :hints (("Goal" :in-theory (enable fn-hcc-cap-tick))))
