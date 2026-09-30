; Logical retained-prefix bound only. Host arguments, temporary decoder
; results/appends, streams/buffers, compiler frames and GC are separate.
(in-package "ACL2")
(include-book "operator-report-reader")

(local
 (defthm fn-oru-space-at-mostp-is-length
   (implies (natp bound)
            (equal (fn-cbor-at-mostp xs bound) (<= (len xs) bound)))
   :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
            :in-theory (enable fn-cbor-at-mostp)))))

(defun fn-oru-reader-prefix-cells (cursor)
  (declare (xargs :guard (fn-oru-ready-p cursor) :verify-guards nil))
  (+ 3 (len (cadr cursor))))

(local
 (defthm fn-oru-space-octet-list-is-proper
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :hints (("Goal" :induct (len xs) :in-theory (enable fn-cbor-octet-listp)))))

(verify-guards fn-oru-reader-prefix-cells
  :hints (("Goal" :in-theory (enable fn-oru-ready-p fn-wildmat-octet-listp))))

(defthm fn-oru-ready-prefix-has-at-most-seven-cells
  (implies (fn-oru-ready-p cursor)
           (<= (fn-oru-reader-prefix-cells cursor) 7))
  :hints (("Goal" :in-theory (enable fn-oru-ready-p fn-oru-reader-prefix-cells
                                    fn-wildmat-at-mostp))))

(defthm fn-oru-reader-step-output-is-one-octet
  (implies (fn-wildmat-octetp byte)
           (and (fn-wildmat-octet-listp
                 (mv-nth 2 (fn-oru-reader-step cursor phase byte eofp io-okp)))
                (<= (len (mv-nth 2 (fn-oru-reader-step cursor phase byte eofp io-okp))) 1)))
  :hints (("Goal" :in-theory (enable fn-oru-reader-step fn-wildmat-octet-listp
                                    fn-wildmat-octetp fn-cbor-octet-listp))))


(local
 (defthm fn-oru-space-length-append-one
   (equal (len (append xs (list byte))) (+ 1 (len xs)))
   :hints (("Goal" :induct (len xs)))))

(local
 (defthm fn-oru-space-step-adds-at-most-one-pending-cell
   (<= (len (cadr (mv-nth 0 (fn-oru-reader-step cursor phase byte eofp io-okp))))
       (+ 1 (len (cadr cursor))))
   :hints (("Goal" :in-theory (e/d (fn-oru-reader-step fn-oru-step
                                   fn-oru-cursor fn-oru-start)
                                  (fn-wildmat-utf8-next fn-oru-lead-width))))))

(local
 (defthm fn-oru-space-output-length-at-most-one-by-definition
   (<= (len (mv-nth 2 (fn-oru-reader-step cursor phase byte eofp io-okp))) 1)
   :hints (("Goal" :in-theory (enable fn-oru-reader-step)))))

; Two adopted cursors plus this turn's emitted octet are a component of the
; live roster. This is NOT an envelope for all temporary allocations/work.
(defthm fn-oru-reader-adopted-cursors-and-output-at-most-fifteen-cells
  (implies (fn-oru-ready-p cursor)
           (<= (+ (fn-oru-reader-prefix-cells cursor)
                  (fn-oru-reader-prefix-cells
                   (mv-nth 0 (fn-oru-reader-step cursor phase byte eofp io-okp)))
                  (len (mv-nth 2 (fn-oru-reader-step cursor phase byte eofp io-okp))))
               15))
  :hints (("Goal" :cases ((consp (mv-nth 2 (fn-oru-reader-step cursor phase byte eofp io-okp))))
           :use ((:instance fn-oru-ready-prefix-has-at-most-seven-cells)
                 (:instance fn-oru-space-step-adds-at-most-one-pending-cell))
           :in-theory (e/d (fn-oru-reader-prefix-cells)
                           (fn-oru-ready-p fn-oru-reader-step
                            fn-oru-space-step-adds-at-most-one-pending-cell)))
          ("Subgoal 1" :in-theory (enable fn-oru-reader-step fn-oru-reader-prefix-cells))))
