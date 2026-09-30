; Fuel-bounded normalization of immutable NOV field spans. A pending CR
; crosses quanta without losing a possible CRLF pair. No field is copied.
(in-package "ACL2")
(include-book "payload-arena")
(include-book "nov-fields")

(defun fn-nsw-step-aux (h at left pending fuel acc fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena))
                              (natp at) (natp left)
                              (<= (+ at left) (fn-arena-payload-len h fn-arena))
                              (natp fuel) (true-listp acc))
                  :verify-guards nil :measure (nfix fuel)))
  (cond
   ((zp fuel) (mv (revappend acc nil) at left pending 0))
   (pending
    (if (and (not (zp left)) (equal (fn-arena-get h at fn-arena) 10))
        (mv-let (out next rest carry used)
          (fn-nsw-step-aux h (+ 1 at) (- left 1) nil (- fuel 1) acc fn-arena)
          (mv out next rest carry (+ 1 used)))
      ; The pending CR was not paired. Emit its scrubbed SP first; the
      ; unread byte is revisited on the next fuel unit, never swallowed.
      (mv-let (out next rest carry used)
        (fn-nsw-step-aux h at left nil (- fuel 1) (cons 32 acc) fn-arena)
        (mv out next rest carry (+ 1 used)))))
   ((zp left) (mv (revappend acc nil) at left nil 0))
   (t
    (let ((byte (fn-arena-get h at fn-arena)))
      (mv-let (out next rest carry used)
        (fn-nsw-step-aux h (+ 1 at) (- left 1) (equal byte 13) (- fuel 1)
                         (if (equal byte 13) acc
                           (cons (fn-nov-scrub-byte byte) acc)) fn-arena)
        (mv out next rest carry (+ 1 used)))))))

(defthm fn-nsw-step-used-natural
  (natp (mv-nth 4 (fn-nsw-step-aux h at left pending fuel acc fn-arena)))
  :rule-classes :type-prescription)

(verify-guards fn-nsw-step-aux
  :hints (("Goal" :in-theory (disable fn-arena-get fn-arena-payload-len fn-arena-count))))

(defun fn-nsw-step (h at left pending fuel fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena))
                              (natp at) (natp left)
                              (<= (+ at left) (fn-arena-payload-len h fn-arena))
                              (natp fuel))))
  (fn-nsw-step-aux h at left pending fuel nil fn-arena))

(defun-nx fn-nsw-source (h at left fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil :measure (nfix left)))
  (if (zp left) nil
    (cons (fn-arena-get h at fn-arena)
          (fn-nsw-source h (+ 1 at) (- left 1) fn-arena))))

(defun-nx fn-nsw-remaining (h at left pending fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-nov-scrub (if pending (cons 13 (fn-nsw-source h at left fn-arena))
                 (fn-nsw-source h at left fn-arena))))

(local
 (defthm fn-nsw-append-revappend
   (equal (append (revappend a b) c) (revappend a (append b c)))))
(local
 (defthm fn-nsw-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))
(local
 (defthm fn-nsw-source-consp
   (equal (consp (fn-nsw-source h at left fn-arena)) (not (zp left)))))
(local
 (defthm fn-nsw-source-car
   (equal (car (fn-nsw-source h at left fn-arena))
          (if (zp left) nil (fn-arena-get h at fn-arena)))))
(local
 (defthm fn-nsw-source-cdr
   (equal (cdr (fn-nsw-source h at left fn-arena))
          (if (zp left) nil (fn-nsw-source h (+ 1 at) (- left 1) fn-arena)))))
(local
 (defthm fn-nsw-revappend-cons
   (equal (revappend (cons x a) b) (revappend a (cons x b)))))

; The exact remaining value is logical vocabulary. The executable step
; reads only its quantum and never materializes this whole residual.
(defthm fn-nsw-step-residual
  (let ((r (fn-nsw-step-aux h at left pending fuel acc fn-arena)))
    (equal (append (mv-nth 0 r)
                   (fn-nsw-remaining h (mv-nth 1 r) (mv-nth 2 r)
                                     (mv-nth 3 r) fn-arena))
           (append (revappend acc nil)
                   (fn-nsw-remaining h at left pending fn-arena))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-nsw-step-aux h at left pending fuel acc fn-arena)
                  :in-theory
                  (e/d (fn-nsw-remaining fn-nsw-source fn-nov-scrub fn-ag-car fn-ag-cdr)
                       (revappend revappend-removal fn-nov-scrub-byte
                        fn-arena-get fn-arena-get-is-nth)))))

(defthm fn-nsw-work-bounded
  (<= (mv-nth 4 (fn-nsw-step-aux h at left pending fuel acc fn-arena))
      (nfix fuel))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-nsw-step-aux h at left pending fuel acc fn-arena)
                  :in-theory (disable fn-arena-get fn-arena-get-is-nth
                                      fn-nov-scrub-byte revappend revappend-removal))))

(defthm fn-nsw-position-preserved
  (implies (and (natp at) (natp left))
           (let ((r (fn-nsw-step-aux h at left pending fuel acc fn-arena)))
             (and (natp (mv-nth 1 r)) (natp (mv-nth 2 r))
                  (<= (mv-nth 2 r) left)
                  (equal (+ (mv-nth 1 r) (mv-nth 2 r)) (+ at left))
                  (<= (- left (mv-nth 2 r)) (nfix fuel)))))
  :hints (("Goal" :induct (fn-nsw-step-aux h at left pending fuel acc fn-arena)
                  :in-theory (disable fn-arena-get fn-arena-get-is-nth
                                      fn-nov-scrub-byte revappend revappend-removal))))

(local
 (defthm fn-nsw-len-revappend
   (equal (len (revappend a b)) (+ (len a) (len b)))
   :hints (("Goal" :induct (revappend a b)
                   :in-theory (disable revappend-removal)))))

(defthm fn-nsw-output-bounded
  (<= (len (mv-nth 0 (fn-nsw-step-aux h at left pending fuel acc fn-arena)))
      (+ (len acc) (nfix fuel)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-nsw-step-aux h at left pending fuel acc fn-arena)
                  :in-theory (disable fn-arena-get fn-arena-get-is-nth
                                      fn-nov-scrub-byte revappend revappend-removal))))

(defthm fn-nsw-progress
  (implies (and (natp left) (posp fuel) (or (< 0 left) pending))
           (let ((r (fn-nsw-step-aux h at left pending fuel acc fn-arena)))
             (< (+ (* 2 (mv-nth 2 r)) (if (mv-nth 3 r) 1 0))
                (+ (* 2 left) (if pending 1 0)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-nsw-step-aux h at left pending fuel acc fn-arena)
                  :in-theory (disable fn-arena-get fn-arena-get-is-nth
                                      fn-nov-scrub-byte revappend revappend-removal))))

(local
 (defthm fn-nsw-nthcdr-step
   (implies (natp at) (equal (nthcdr (+ 1 at) xs) (cdr (nthcdr at xs))))
   :hints (("Goal" :induct (nthcdr at xs)))))
(local
 (defthm fn-nsw-nthcdr-car
   (implies (natp at) (equal (car (nthcdr at xs)) (nth at xs)))
   :hints (("Goal" :induct (nthcdr at xs)))))

(defthm fn-nsw-source-is-slice
  (implies (natp at)
           (equal (fn-nsw-source h at left fn-arena)
                  (take left (nthcdr at (nth h fn-arena)))))
  :hints (("Goal" :induct (fn-nsw-source h at left fn-arena)
                  :in-theory (e/d (fn-arena-get-is-nth) (nthcdr nth)))))

(local
 (defthm fn-nsw-scrub-byte-octet
   (fn-octetp (fn-nov-scrub-byte b))
   :hints (("Goal" :in-theory (enable fn-octetp fn-nov-scrub-byte)))))
(local
 (defthm fn-nsw-revappend-octets
   (implies (and (fn-octet-listp a) (fn-octet-listp b))
            (fn-octet-listp (revappend a b)))
   :hints (("Goal" :induct (revappend a b)
                   :in-theory (e/d (fn-octet-listp) (revappend-removal))))))
(defthm fn-nsw-output-octets
  (implies (fn-octet-listp acc)
           (fn-octet-listp (mv-nth 0 (fn-nsw-step-aux h at left pending fuel acc fn-arena)))))
