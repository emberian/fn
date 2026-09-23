; fn: bounded cursor fragmentation and position-scanning reassembly.
;
; The reference in bp-fragment.lisp selects each cut byte with nth from the
; original payload.  The cutter threads the unconsumed suffix, traversing
; each emitted segment once for a prefix and once to advance the cursor.
; Reassembly checks the 64-fragment cap before scanning output positions.
; Across the conflict, gap and output/range scans it makes at most three
; cell probes per output position, each over at most 64 fragments, after
; input validation.  Conflict and gap paths avoid allocating a full canvas;
; the successful path still builds one.  The certified equality below is a
; value argument, not a native performance claim.

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

; Reassembly scans positions without first constructing a complete canvas.
; The fragment count is capped at 64, so each position probes at most 64
; fragments.  Conflicts take precedence over gaps, just as in the reference.
(defun fn-bpf-first-cell (fs from n marker)
  (declare (xargs :guard (and (fn-bpf-fragment-listp fs)
                              (natp from) (natp n) (symbolp marker))
                  :measure (nfix n)))
  (if (zp n)
      nil
    (if (eq (fn-bpf-cell-at fs from) marker)
        from
      (fn-bpf-first-cell fs (+ 1 from) (1- n) marker))))

(defun fn-bpf-run-cell (fs from n marker)
  (declare (xargs :guard (and (fn-bpf-fragment-listp fs)
                              (natp from) (natp n) (symbolp marker))
                  :measure (nfix n)))
  (if (or (zp n) (not (eq (fn-bpf-cell-at fs from) marker)))
      from
    (fn-bpf-run-cell fs (+ 1 from) (1- n) marker)))

(defun fn-bpf-reassemble-fast (fs total)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-bpf-inputsp fs total))
      (list :invalid :bounds)
    (let ((conflict (fn-bpf-first-cell fs 0 total :conflict)))
      (if conflict
          (list :conflict conflict)
        (let ((gap (fn-bpf-first-cell fs 0 total :gap)))
          (if gap
              (list :missing gap
                    (fn-bpf-run-cell fs gap (- total gap) :gap))
            (list :ok (fn-bpf-canvas fs 0 total))))))))

(verify-guards fn-bpf-first-cell)
(verify-guards fn-bpf-run-cell)

(defthm fn-bpf-first-cell-is-first-index
  (implies (and (natp from) (natp n) (symbolp marker))
           (equal (fn-bpf-first-cell fs from n marker)
                  (fn-bpf-first-index (fn-bpf-canvas fs from n)
                                      from marker)))
  :hints (("Goal" :induct (fn-bpf-first-cell fs from n marker)
           :expand ((fn-bpf-canvas fs from n))
           :in-theory (disable fn-bpf-cell-at))))

(defthm fn-bpf-run-cell-is-run-end
  (implies (and (natp from) (natp n) (symbolp marker))
           (equal (fn-bpf-run-cell fs from n marker)
                  (fn-bpf-run-end (fn-bpf-canvas fs from n)
                                      from marker)))
  :hints (("Goal" :induct (fn-bpf-run-cell fs from n marker)
           :expand ((fn-bpf-canvas fs from n))
           :in-theory (disable fn-bpf-cell-at))))

(local
 (defun fn-bpf-canvas-suffix-induction (from n k)
   (declare (xargs :measure (nfix k)))
   (if (zp k)
       (list from n k)
     (fn-bpf-canvas-suffix-induction (+ 1 from) (1- n) (1- k)))))

(defthm fn-bpf-nthcdr-canvas
  (implies (and (natp from) (natp n) (natp k) (<= k n))
           (equal (nthcdr k (fn-bpf-canvas fs from n))
                  (fn-bpf-canvas fs (+ from k) (- n k))))
  :hints (("Goal" :induct (fn-bpf-canvas-suffix-induction from n k)
           :in-theory (disable fn-bpf-cell-at
                               mod-x-y-=-x+y-for-rationals))))

(defthm fn-bpf-first-cell-in-range
  (implies (and (natp from) (natp n)
                (fn-bpf-first-cell fs from n marker))
           (and (natp (fn-bpf-first-cell fs from n marker))
                (<= from (fn-bpf-first-cell fs from n marker))
                (< (fn-bpf-first-cell fs from n marker) (+ from n))))
  :hints (("Goal" :induct (fn-bpf-first-cell fs from n marker)
           :in-theory (disable fn-bpf-cell-at))))

(defthm fn-bpf-first-index-of-canvas-less-than-end
  (implies (and (natp from) (natp n) (symbolp marker)
                (fn-bpf-first-index (fn-bpf-canvas fs from n)
                                    from marker))
           (< (fn-bpf-first-index (fn-bpf-canvas fs from n)
                                  from marker)
              (+ from n)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bpf-first-cell-in-range))
           :in-theory (disable fn-bpf-first-cell-in-range fn-bpf-canvas))))

(defthm fn-bpf-reassemble-fast-is-reassemble
  (equal (fn-bpf-reassemble-fast fs total)
         (fn-bpf-reassemble fs total))
  :hints (("Goal"
           :use ((:instance fn-bpf-nthcdr-canvas
                            (from 0) (n total)
                            (k (fn-bpf-first-cell fs 0 total :gap)))
                 (:instance fn-bpf-run-cell-is-run-end
                            (from (fn-bpf-first-cell fs 0 total :gap))
                            (n (- total (fn-bpf-first-cell fs 0 total :gap)))
                            (marker :gap))
                 (:instance fn-bpf-first-cell-in-range
                            (from 0) (n total) (marker :gap)))
           :in-theory (disable fn-bpf-nthcdr-canvas
                               fn-bpf-run-cell-is-run-end
                               fn-bpf-first-cell-in-range
                               fn-bpf-canvas fn-bpf-cell-at
                               fn-bpf-first-cell fn-bpf-run-cell))))

(verify-guards fn-bpf-reassemble-fast
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpf-first-cell-in-range
                            (from 0) (n total) (marker :gap)))
           :in-theory (disable fn-bpf-first-cell-in-range
                               fn-bpf-first-index-of-canvas-less-than-end
                               fn-bpf-first-cell-is-first-index
                               fn-bpf-first-cell fn-bpf-cell-at fn-bpf-canvas
                               mod-x-y-=-x+y-for-rationals))))
