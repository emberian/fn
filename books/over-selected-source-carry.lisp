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

(local
 (defthm fn-osh-at-is-nth
  (equal (fn-hmid-at i x) (nth (nfix i) x))
  :hints (("Goal" :in-theory (enable fn-hmid-at fn-ag-car fn-ag-cdr nth)))))

; A plain octet tail cannot become a span tag after one emitted octet.
(local
 (defthm fn-osh-octet-tail-source
  (implies (fn-cbor-octet-listp part)
           (fn-osh-piece-source-p (cdr part) handle origin))
  :hints (("Goal" :in-theory
   (enable fn-cbor-octet-listp fn-cbor-octetp fn-osh-piece-source-p)))))

(defthm fn-osh-piece-one-preserves-source
 (implies (and (fn-npw-piecesp pieces fn-arena)
               (fn-osh-pieces-source-p pieces handle origin))
  (fn-osh-pieces-source-p
     (mv-nth 1 (fn-npw-one pieces pos fn-arena)) handle origin))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory
   (e/d (fn-npw-one fn-npw-piecesp fn-npw-partp
         fn-osh-pieces-source-p fn-osh-piece-source-p fn-hmid-at)
        (fn-nsw-step fn-nbw-decimal-tick fn-arena-count
         fn-arena-payload-len)))))

(defthm fn-osh-active-row-one-preserves-source
 (implies (and (fn-ohr-carried-p active fn-arena)
               (fn-osh-row-source-p active handle origin))
  (fn-osh-row-source-p
     (mv-nth 1 (fn-ohr-active-one active fn-arena)) handle origin))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lpc-tick-preserves-source (s (nth 3 active)) (fuel 1))
        (:instance fn-lpc-tick-preserves-bounds (s (nth 3 active)) (fuel 1))
        (:instance fn-osh-parser-pieces-retain-source
          (parser (mv-nth 0 (fn-lpc-tick (nth 3 active) 1 fn-arena)))
          (number (nth 1 (nth 0 active))))
        (:instance fn-osh-piece-one-preserves-source
          (pieces (nth 4 active)) (pos (nth 5 active))))
  :in-theory
   (e/d (fn-ohr-carried-p fn-osh-row-source-p fn-ohr-active-one
         fn-obc-make fn-obc-row-ready fn-obc-begin fn-obc-next-range
         fn-ovw-cursor fn-hmid-at fn-osh-pieces-source-p)
        (nth mv-nth fn-lpc-tick-preserves-source fn-lpc-tick fn-lpc-at fn-lpc-ready-p fn-lpc-cursor-bounds-p
         fn-npw-one fn-npw-piecesp fn-obc-parser-pieces
         fn-lpc-tombstonep fn-arena-count fn-arena-payload-len)))))

(local
 (defthm fn-osh-cached-pieces-source
  (implies (fn-hnov-p (fn-hf-nov facts))
   (fn-osh-pieces-source-p (fn-npw-column-pieces number facts octets) handle origin))
  :hints (("Goal" :in-theory
   (enable fn-npw-column-pieces fn-osh-pieces-source-p fn-osh-piece-source-p
           fn-hnov-p fn-hnov-shapep fn-hnov-subject fn-hnov-from fn-hnov-date
           fn-hnov-msgid fn-hnov-references fn-hf-nov fn-hf-body-lines
           fn-nntp-decimal-field fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)))))

(defthm fn-osh-held-row-begin-establishes-source
 (implies (or (not (fn-hf-nov (fn-held-facts row)))
              (fn-hnov-p (fn-hf-nov (fn-held-facts row))))
  (fn-osh-row-source-p (fn-ohr-selected-row-begin range origin row fn-arena)
                       (fn-record-payload row) origin))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory
   (e/d (fn-ohr-selected-row-begin fn-osh-row-source-p fn-obc-row-ready
         fn-obc-make fn-obc-begin fn-obc-next-range fn-ovw-cursor
         fn-lpc-begin fn-hmid-at fn-lpc-at fn-osh-pieces-source-p)
        (fn-npw-column-pieces fn-hnov-p fn-lpc-header-begin
         fn-lpc-header-bad fn-arena-count fn-arena-payload-len)))))

(defthm fn-osh-one-preserves-selected-source
 (implies (and (fn-osh-ready-p cell fn-arena)
               (fn-osh-selected-source-p cell))
  (fn-osh-selected-source-p (mv-nth 1 (fn-osh-one cell fn-arena))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-osh-active-row-one-preserves-source
          (active (nth 5 cell)) (handle (fn-record-payload (nth 3 cell)))
          (origin (nth 2 cell)))
        (:instance fn-osh-held-row-begin-establishes-source
          (range (nth 1 cell)) (row (nth 3 cell)) (origin (nth 2 cell))))
  :in-theory
   (e/d (fn-osh-one fn-osh-make fn-osh-ready-p fn-osh-selected-source-p
         fn-hmid-at fn-obc-begin fn-obc-next-range fn-ovw-cursor
         fn-osh-row-source-p)
        (nth mv-nth fn-ohr-active-one fn-ohr-selected-row-begin
         fn-ohr-carried-p fn-hmid-one fn-hmid-status fn-hmid-ready-p
         fn-osh-pieces-source-p fn-record-payload fn-held-facts fn-hf-nov
         fn-hnov-p fn-lpc-at fn-arena-count fn-arena-payload-len)))))
