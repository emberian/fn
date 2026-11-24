; Moving the first remaining row to the stored prefix preserves admission,
; sorting and the per-source entry bound.
(in-package "ACL2")
(include-book "range-seek-scan-proof")
(include-book "ordered")

(local
 (defthm fn2-ov-list-prefix-layout
   (implies (true-listp a)
            (equal (fn2-run-entries-layoutp layout (append a b))
                   (and (fn2-run-entries-layoutp layout a) (fn2-run-entries-layoutp layout b))))
   :hints (("Goal" :induct (len a) :in-theory (disable fn2-run-values-layoutp)))))

(local
 (defthm fn2-ov-first-of-appended-list
   (equal (car (append a b)) (if (consp a) (car a) (car b)))))

(local
 (defthm fn2-ov-list-prefix-order
   (implies (and (consp tail) (fn2-run-sorted-spec key (append rows tail)))
            (fn2-run-sorted-spec key (append rows (list (car tail)))))
   :hints (("Goal" :induct (len rows) :in-theory (disable fn2-run-key-order-spec)))))

(defthmd fn2-ov-list-shift-prefix
   (equal (append (append rows (list e)) rest) (append rows (cons e rest))))

(local
 (defthm fn2-ov-list-length-append
   (equal (len (append rows tail)) (+ (len rows) (len tail)))))

(defthmd fn2-ov-append-empty-tail
   (implies (true-listp rows) (equal (append rows nil) rows)))

(defun-nx fn2-ov-source-segment-p (rows tail)
   (and (true-listp rows) (true-listp tail)
        (fn2-run-entries-layoutp *fn2-overview-entry* rows) (fn2-run-entries-layoutp *fn2-overview-entry* tail)
        (fn2-run-sorted-spec *fn2-overview-range-key* (append rows tail)) (<= (len (append rows tail)) 48)))

(defthmd fn2-ov-source-segment-advances
   (implies (and (fn2-ov-source-segment-p rows tail) (consp tail))
            (and (fn2-ov-source-segment-p (append rows (list (car tail))) (cdr tail))
                 (fn2-run-entries-layoutp *fn2-overview-entry* rows)
                 (fn2-run-values-layoutp *fn2-overview-entry* (car tail))
                 (fn2-run-sorted-spec *fn2-overview-range-key* (append rows (list (car tail)))) (< (len rows) 48)))
   :hints (("Goal" :use ((:instance fn2-ov-list-prefix-order (key *fn2-overview-range-key*)))
            :expand ((fn2-run-entries-layoutp *fn2-overview-entry* tail) (len tail) (true-listp tail))
            :in-theory (e/d (fn2-ov-list-shift-prefix) (fn2-run-values-layoutp fn2-run-sorted-spec fn2-ov-list-prefix-order)))))
