(in-package "ACL2")
(include-book "../../books/over-selected-source-carry")

(defun-nx oshst-parser ()
 (let* ((bytes '(83 117 98 106 101 99 116 58 32 120 13 10 13 10))
        (fn-arena (list bytes)))
  (mv-nth 0 (fn-lpc-tick (fn-lpc-begin 0 14 '(:source 17)) 14 fn-arena))))

(defthm oshst-parser-pieces-source-positive
 (let ((parser (oshst-parser)))
  (and (equal (fn-lpc-verdict parser) :valid)
       (fn-lpc-cursor-bounds-p parser)
       (fn-osh-pieces-source-p (fn-obc-parser-pieces 1 parser)
                               (fn-lpc-at 0 parser) (fn-lpc-at 2 parser))))
 :rule-classes nil)

; Corrupted-state hypothesis removal: replace one actual completed field
; with a foreign payload handle; original parser/source remain unchanged.
(defthm oshst-parser-pieces-source-without-bounds
 (let* ((parser (oshst-parser))
        (header (fn-lpc-at 4 parser))
        (bad (fn-lpc-put 4
               (fn-lpc-put 8 (cons '(1 9 1 (:source 17))
                                  (cdr (fn-lpc-at 8 header))) header) parser)))
  (and (equal (fn-lpc-verdict bad) :valid)
       (not (fn-lpc-cursor-bounds-p bad))
       (not (fn-osh-pieces-source-p (fn-obc-parser-pieces 1 bad)
                                  (fn-lpc-at 0 bad) (fn-lpc-at 2 bad)))))
 :rule-classes nil)

(defun-nx oshst-piece-conclusion (pieces handle origin fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (fn-osh-pieces-source-p (mv-nth 1 (fn-npw-one pieces 0 fn-arena)) handle origin))

(defthm oshst-piece-one-positive
 (let* ((fn-arena '((65 66 67)))
        (pieces '((:span 0 0 3 nil (:source 17)))))
  (and (fn-npw-piecesp pieces fn-arena)
       (fn-osh-pieces-source-p pieces 0 '(:source 17))
       (oshst-piece-conclusion pieces 0 '(:source 17) fn-arena)))
 :rule-classes nil)

(defthm oshst-piece-one-without-source
 (let* ((fn-arena '((65 66 67)))
        (pieces '((:span 0 0 3 nil (:source 17)))))
  (and (fn-npw-piecesp pieces fn-arena)
       (not (fn-osh-pieces-source-p pieces 1 '(:source 17)))
       (not (oshst-piece-conclusion pieces 1 '(:source 17) fn-arena))))
 :rule-classes nil)

; Corrupted plain piece becomes a foreign span after its first octet.
(defthm oshst-piece-one-without-shape
 (let* ((fn-arena '((65 66 67)))
        (pieces '((1 :span 1 0 1 nil (:source 17)))))
  (and (not (fn-npw-piecesp pieces fn-arena))
       (fn-osh-pieces-source-p pieces 0 '(:source 17))
       (not (oshst-piece-conclusion pieces 0 '(:source 17) fn-arena))))
 :rule-classes nil)

(defun-nx oshst-row-conclusion (active handle origin fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (fn-osh-row-source-p (mv-nth 1 (fn-ohr-active-one active fn-arena)) handle origin))

(defthm oshst-row-one-positive
 (let* ((fn-arena '((83 117 98 106 101 99 116 58 32 120 13 10 13 10)))
        (active (fn-obc-make '("g" 1 3 7 nil t) '(:source 17)
                            :parse (oshst-parser) nil 0)))
  (and (fn-ohr-carried-p active fn-arena)
       (fn-osh-row-source-p active 0 '(:source 17))
       (oshst-row-conclusion active 0 '(:source 17) fn-arena)))
 :rule-classes nil)

(defthm oshst-row-one-without-source
 (let* ((fn-arena '((83 117 98 106 101 99 116 58 32 120 13 10 13 10)))
        (active (fn-obc-make '("g" 1 3 7 nil t) '(:source 17)
                            :parse (oshst-parser) nil 0)))
  (and (fn-ohr-carried-p active fn-arena)
       (not (fn-osh-row-source-p active 1 '(:source 17)))
       (not (oshst-row-conclusion active 1 '(:source 17) fn-arena))))
 :rule-classes nil)

(defthm oshst-row-one-without-carry
 (let* ((fn-arena '((65 66 67)))
        (active (fn-obc-make '("g" 1 3 7 nil t) '(:source 17)
                      :emit nil '((1 :span 1 0 1 nil (:source 17))) 0)))
  (and (not (fn-ohr-carried-p active fn-arena))
       (fn-osh-row-source-p active 0 '(:source 17))
       (not (oshst-row-conclusion active 0 '(:source 17) fn-arena))))
 :rule-classes nil)

; Logical fixture uses historical held15 shape only; no native held16 claim.
(defun oshst-row (facts)
 (fn-held-make 0 1 0 "<e@x>" 0 '("g") "o" "s" "e" 1 5 facts
  (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) '(("g" . 1)) nil))

(defthm oshst-held-begin-source-positive
 (let* ((fn-arena '((65 66 67))) (row (oshst-row (fn-hf-make 3 nil 0 nil))))
  (and (not (fn-hf-nov (fn-held-facts row)))
       (fn-osh-row-source-p
        (fn-ohr-selected-row-begin '("g" 1 3 7 nil t) '(:source 17) row fn-arena)
        (fn-record-payload row) '(:source 17))))
 :rule-classes nil)

(defthm oshst-held-begin-source-without-nov-shape
 (let* ((fn-arena '((65 66 67)))
        (facts (fn-hf-make 3 nil 0
          (list nil nil nil (fn-hnov-make nil t '(:span 1 0 1 nil (:source 17))
                                              "f" "d" "<e@x>" ""))))
        (row (oshst-row facts)))
  (and (fn-hf-nov (fn-held-facts row))
       (not (fn-hnov-p (fn-hf-nov (fn-held-facts row))))
       (not (fn-osh-row-source-p
        (fn-ohr-selected-row-begin '("g" 1 3 7 nil t) '(:source 17) row fn-arena)
        (fn-record-payload row) '(:source 17)))))
 :rule-classes nil)

(defun-nx oshst-cell-conclusion (cell fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (fn-osh-selected-source-p (mv-nth 1 (fn-osh-one cell fn-arena))))

(defthm oshst-cell-one-source-positive
 (let* ((fn-arena '((65 66 67))) (row (oshst-row (fn-hf-make 3 nil 0 nil)))
        (range '("g" 1 3 7 nil t))
        (cell (fn-osh-make range '(:source 17) row :row
                 (fn-ohr-selected-row-begin range '(:source 17) row fn-arena))))
  (and (fn-osh-ready-p cell fn-arena) (fn-osh-selected-source-p cell)
       (oshst-cell-conclusion cell fn-arena)))
 :rule-classes nil)

(defthm oshst-cell-one-without-source
 (let* ((fn-arena '((65 66 67) (65 66 67)))
        (row (oshst-row (fn-hf-make 3 nil 0 nil))) (range '("g" 1 3 7 nil t))
        (cell (fn-osh-make range '(:source 17) row :row
                (fn-obc-make range '(:source 17) :parse
                    (fn-lpc-begin 1 3 '(:source 17)) nil 0))))
  (and (fn-osh-ready-p cell fn-arena) (not (fn-osh-selected-source-p cell))
       (not (oshst-cell-conclusion cell fn-arena))))
 :rule-classes nil)

(defthm oshst-cell-one-without-ready
 (let* ((fn-arena '((65 66 67))) (row (oshst-row (fn-hf-make 3 nil 0 nil)))
        (range '("g" 1 3 7 nil t))
        (cell (fn-osh-make range '(:source 17) row :row
                (fn-obc-make (fn-obc-next-range range nil) '(:source 17) :emit nil
                       '((1 :span 1 0 1 nil (:source 17))) 0))))
  (and (not (fn-osh-ready-p cell fn-arena)) (fn-osh-selected-source-p cell)
       (not (oshst-cell-conclusion cell fn-arena))))
 :rule-classes nil)
