; Maintained row domain, including the parser's actual source-span bounds.
; This predicate is proof/caller guard vocabulary and is not run by ONE.
(in-package "ACL2")
(include-book "over-held-row")
(include-book "over-row-piece-shape")

(defun fn-ohr-carried-p (s fn-arena)
 (declare (xargs :stobjs fn-arena :guard t))
 (and (true-listp s) (true-listp (nth 0 s)) (natp (nth 5 s))
  (case (nth 2 s)
   (:parse (and (fn-lpc-ready-p (nth 3 s) fn-arena)
                (fn-lpc-cursor-bounds-p (nth 3 s))))
   (:emit (fn-npw-piecesp (nth 4 s) fn-arena))
   (:seek t)
   (otherwise nil))))

(defthm fn-ohr-carried-active-is-active
 (implies (and (fn-ohr-carried-p s fn-arena)
               (member-eq (nth 2 s) '(:parse :emit)))
          (fn-ohr-active-p s fn-arena))
 :hints (("Goal" :in-theory (enable fn-ohr-carried-p fn-ohr-active-p))))

(defthm fn-ohr-active-one-preserves-carried-row-domain
 (implies (and (fn-ohr-carried-p s fn-arena)
               (member-eq (nth 2 s) '(:parse :emit)))
  (let ((next (mv-nth 1 (fn-ohr-active-one s fn-arena))))
   (or (not next) (fn-ohr-carried-p next fn-arena))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lpc-tick-preserves-ready (s (nth 3 s)) (fuel 1))
        (:instance fn-lpc-tick-preserves-bounds (s (nth 3 s)) (fuel 1))
        (:instance fn-npw-one-keeps-pieces (pieces (nth 4 s)) (pos (nth 5 s)))
        (:instance fn-npw-one-position-natural (pieces (nth 4 s)) (pos (nth 5 s)))
        (:instance fn-obc-parser-pieces-have-shape
          (parser (mv-nth 0 (fn-lpc-tick (nth 3 s) 1 fn-arena)))
          (number (nth 1 (nth 0 s)))))
  :in-theory
  (e/d (fn-ohr-carried-p fn-ohr-active-one fn-obc-make fn-obc-begin
        fn-obc-next-range fn-ovw-cursor fn-obc-row-ready fn-npw-piecesp fn-npw-partp
        fn-ovw-status)
       (fn-npw-one fn-lpc-tick fn-obc-parser-pieces fn-lpc-ready-p
        fn-lpc-cursor-bounds-p fn-lpc-at fn-lpc-tombstonep
        fn-arena-count-is-len fn-arena-payload-len-is-len-nth)))))
