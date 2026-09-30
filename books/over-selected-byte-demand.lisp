; Internal selected-cell projection; registry/source authorization belongs to
; the RH/MIO caller. No supplied host handle/offset becomes authority here.
(in-package "ACL2")
(include-book "over-selected-source-carry")

(defun fn-osh-byte-demand (cell)
 (declare (xargs :guard t))
 (if (not (eq (fn-hmid-at 4 cell) :row)) (mv :none nil nil nil)
  (let ((active (fn-hmid-at 5 cell)))
   (case (fn-hmid-at 2 active)
    (:parse
     (let ((parser (fn-hmid-at 3 active)))
      ; LPC reads at POS even when its accumulated syntax verdict is bad.
      (if (< (nfix (fn-lpc-at 3 parser)) (nfix (fn-lpc-at 1 parser)))
          (mv :payload (fn-lpc-at 0 parser) (fn-lpc-at 3 parser)
                       (fn-lpc-at 2 parser))
        (mv :none nil nil nil))))
    (:emit
     (let ((piece (fn-ag-car (fn-hmid-at 4 active))))
      ; Pending CR still peeks at AT whenever LEFT is positive.
      (if (and (consp piece) (eq (car piece) :span)
               (< 0 (nfix (fn-hmid-at 3 piece))))
          (mv :payload (fn-hmid-at 1 piece) (fn-hmid-at 2 piece)
                       (fn-hmid-at 5 piece))
        (mv :none nil nil nil))))
    (otherwise (mv :none nil nil nil))))))

(defthm fn-osh-byte-demand-retains-selected-source
 (implies (fn-osh-selected-source-p cell)
  (let ((demand (fn-osh-byte-demand cell)))
   (implies (eq (mv-nth 0 demand) :payload)
    (and (equal (mv-nth 1 demand) (fn-record-payload (fn-hmid-at 3 cell)))
         (equal (mv-nth 3 demand) (fn-hmid-at 2 cell))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (enable fn-osh-byte-demand fn-osh-selected-source-p fn-osh-row-source-p
          fn-osh-pieces-source-p fn-osh-piece-source-p fn-hmid-at
          fn-lpc-at fn-ag-car fn-ag-cdr))))

(local
 (defthm fn-osbd-hmid-at-is-nth
  (equal (fn-hmid-at i x) (nth (nfix i) x))
  :hints (("Goal" :in-theory (enable fn-hmid-at fn-ag-car fn-ag-cdr nth)))))
(local
 (defthm fn-osbd-lpc-at-is-nth
  (equal (fn-lpc-at i x) (nth (nfix i) x))
  :hints (("Goal" :in-theory (enable fn-lpc-at fn-ag-car fn-ag-cdr nth)))))

(defthm fn-osh-byte-demand-is-in-current-payload
 (implies (fn-osh-ready-p cell fn-arena)
  (let ((demand (fn-osh-byte-demand cell)))
   (implies (eq (mv-nth 0 demand) :payload)
    (and (natp (mv-nth 1 demand)) (natp (mv-nth 2 demand))
         (< (mv-nth 1 demand) (fn-arena-count fn-arena))
         (< (mv-nth 2 demand)
            (fn-arena-payload-len (mv-nth 1 demand) fn-arena))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :expand ((fn-npw-piecesp (nth 4 (nth 5 cell)) fn-arena))
  :in-theory
  (e/d (fn-osh-byte-demand fn-osh-ready-p fn-ohr-carried-p
        fn-lpc-ready-p fn-npw-piecesp fn-npw-partp fn-ag-car)
       (fn-hmid-at fn-lpc-at nth fn-ag-cdr
        fn-arena-count-is-len fn-arena-payload-len-is-len-nth
        fn-lpc-cursor-bounds-p fn-record-payload fn-held-facts fn-hf-nov
        fn-hnov-p fn-hmid-ready-p fn-record-msgid fn-obc-next-range)))))
