; Actual residual full-range reply. This is proof vocabulary, never a locator.
(in-package "ACL2")
(include-book "over-byte-cursor")
(include-book "served-range-source")
(include-book "over-reply-source")

(defun-nx fn-obc-old-range-reply (range fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if range
      (fn-ovw-reply
       (fn-ovw-lines (nth 0 range) (nfix (nth 1 range))
                     (nfix (nth 2 range)) (nth 3 range) fn-arena fn-cat)
       (nth 4 range) (nth 5 range))
    nil))

(defun-nx fn-obc-actual-old-residual (s fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (equal (nth 2 s) :emit)
      (append (fn-npw-remaining (nth 4 s) (nth 5 s) fn-arena)
              (fn-obc-old-range-reply (nth 0 s) fn-arena fn-cat))
    (fn-obc-old-range-reply (nth 0 s) fn-arena fn-cat)))

(local
 (defthm fn-obr-append-associative
  (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-obr-empty-piece-residual
  (implies (not (consp pieces))
           (equal (fn-npw-remaining pieces pos fn-arena) nil))
  :hints (("Goal" :in-theory (enable fn-npw-remaining)))))

(local
 (defthm fn-obr-empty-range-reply
  (equal (fn-obc-old-range-reply nil fn-arena fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-obc-old-range-reply)))))

(local
 (defthm fn-obr-empty-pieces-valid
  (fn-npw-piecesp nil fn-arena)
  :hints (("Goal" :in-theory (enable fn-npw-piecesp)))))

(defthm fn-obc-one-emit-preserves-actual-full-old-residual
 (implies (and (equal (nth 2 s) :emit)
               (fn-npw-piecesp (nth 4 s) fn-arena)
               (natp (nth 5 s)))
  (let ((r (fn-obc-one s fn-arena fn-cat)))
   (and (fn-npw-piecesp (nth 4 (mv-nth 1 r)) fn-arena)
   (equal (append (mv-nth 0 r)
                  (fn-obc-actual-old-residual (mv-nth 1 r) fn-arena fn-cat))
          (fn-obc-actual-old-residual s fn-arena fn-cat)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-npw-one-keeps-pieces
                         (pieces (nth 4 s)) (pos (nth 5 s)))
                        (:instance fn-npw-one-residual
                         (pieces (nth 4 s)) (pos (nth 5 s))))
  :in-theory (e/d (fn-obc-one fn-obc-actual-old-residual fn-obc-make
                   fn-obc-begin)
                  (fn-npw-one fn-npw-remaining fn-npw-piecesp
                   fn-obc-old-range-reply fn-ovw-lines fn-ovw-reply)))))

(defthm fn-obc-one-exhaustion-preserves-actual-full-old-residual
 (implies (and (equal (nth 2 s) :seek)
               (< (nfix (nth 2 (nth 0 s))) (nfix (nth 1 (nth 0 s)))))
  (let ((r (fn-obc-one s fn-arena fn-cat)))
   (equal (append (mv-nth 0 r)
                  (fn-obc-actual-old-residual (mv-nth 1 r) fn-arena fn-cat))
          (fn-obc-actual-old-residual s fn-arena fn-cat))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-obc-one fn-obc-actual-old-residual fn-obc-old-range-reply
        fn-obc-make fn-ovw-lines fn-cnx-range-aux fn-scat-range-keep
        fn-nov-lines-for-numbers-cat fn-ovw-reply fn-npw-remaining
        fn-npw-part-bytes fn-ovw-status fn-ovw-empty-text)
       (fn-npw-one fn-npw-piecesp)))))
