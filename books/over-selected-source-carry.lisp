; Prospective proof vocabulary for SAME-row payload authority, not a hot scan.
(in-package "ACL2")
(include-book "over-selected-held-cell")

(defun fn-osh-piece-source-p (part handle origin)
 (declare (xargs :guard t))
 (implies (and (consp part) (eq (car part) :span))
          (and (equal (fn-hmid-at 1 part) handle)
               (equal (fn-hmid-at 5 part) origin))))
(defun fn-osh-pieces-source-p (pieces handle origin)
 (declare (xargs :guard t))
 (if (consp pieces)
     (and (fn-osh-piece-source-p (car pieces) handle origin)
          (fn-osh-pieces-source-p (cdr pieces) handle origin))
   t))
(defun fn-osh-row-source-p (active handle origin)
 (declare (xargs :guard t))
 (case (fn-hmid-at 2 active)
  (:parse (and (equal (fn-lpc-at 0 (fn-hmid-at 3 active)) handle)
               (equal (fn-lpc-at 2 (fn-hmid-at 3 active)) origin)))
  (:emit (fn-osh-pieces-source-p (fn-hmid-at 4 active) handle origin))
  (otherwise t)))
(defun fn-osh-selected-source-p (cell)
 (declare (xargs :guard t))
 (implies (equal (fn-hmid-at 4 cell) :row)
  (fn-osh-row-source-p (fn-hmid-at 5 cell)
                        (fn-record-payload (fn-hmid-at 3 cell))
                        (fn-hmid-at 2 cell))))

(local
 (defthm fn-osh-span-piece-source
  (implies (fn-lpc-span-bound-p span handle origin bound)
           (fn-osh-piece-source-p (fn-obc-span-piece span) handle origin))
  :hints (("Goal" :in-theory
   (enable fn-lpc-span-bound-p fn-obc-span-piece fn-osh-piece-source-p
           fn-hmid-at fn-lpc-at fn-ag-car fn-ag-cdr)))))

(local
 (defthm fn-osh-number-piece-source
  (fn-osh-piece-source-p (fn-nntp-decimal-field number) handle origin)
  :hints (("Goal" :in-theory
    (enable fn-osh-piece-source-p fn-nntp-decimal-field
            fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)))))

(local
 (defthm fn-osh-nonspan-piece-source
  (implies (not (equal (car part) :span))
           (fn-osh-piece-source-p part handle origin))
  :hints (("Goal" :in-theory (enable fn-osh-piece-source-p)))))

(defthm fn-osh-parser-pieces-retain-source
 (implies (fn-lpc-cursor-bounds-p parser)
  (fn-osh-pieces-source-p (fn-obc-parser-pieces number parser)
                          (fn-lpc-at 0 parser) (fn-lpc-at 2 parser)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lpc-field-retains-pinned-source (s parser) (k 0))
        (:instance fn-lpc-field-retains-pinned-source (s parser) (k 1))
        (:instance fn-lpc-field-retains-pinned-source (s parser) (k 2))
        (:instance fn-lpc-field-retains-pinned-source (s parser) (k 3))
        (:instance fn-lpc-field-retains-pinned-source (s parser) (k 4))
        (:instance fn-osh-span-piece-source (span (fn-lpc-field parser 0)) (handle (fn-lpc-at 0 parser)) (origin (fn-lpc-at 2 parser)) (bound (fn-lpc-at 3 parser)))
        (:instance fn-osh-span-piece-source (span (fn-lpc-field parser 1)) (handle (fn-lpc-at 0 parser)) (origin (fn-lpc-at 2 parser)) (bound (fn-lpc-at 3 parser)))
        (:instance fn-osh-span-piece-source (span (fn-lpc-field parser 2)) (handle (fn-lpc-at 0 parser)) (origin (fn-lpc-at 2 parser)) (bound (fn-lpc-at 3 parser)))
        (:instance fn-osh-span-piece-source (span (fn-lpc-field parser 3)) (handle (fn-lpc-at 0 parser)) (origin (fn-lpc-at 2 parser)) (bound (fn-lpc-at 3 parser)))
        (:instance fn-osh-span-piece-source (span (fn-lpc-field parser 4)) (handle (fn-lpc-at 0 parser)) (origin (fn-lpc-at 2 parser)) (bound (fn-lpc-at 3 parser))))
  :in-theory
  (e/d (fn-obc-parser-pieces fn-osh-pieces-source-p
         fn-hmid-at fn-ag-car fn-ag-cdr)
       (fn-osh-piece-source-p fn-obc-span-piece fn-lpc-field fn-lpc-at fn-lpc-cursor-bounds-p
        fn-lpc-span-bound-p fn-nntp-decimal-field fn-lpc-body-lines)))))
