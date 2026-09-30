(in-package "ACL2")
(include-book "../../books/over-selected-held-cell")

(defun osht-row (msgid h facts)
 (declare (xargs :guard t :verify-guards nil))
 (fn-held-make 0 1 0 msgid h '("g") "o" "s" "e" 1 5 facts
   (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) '(("g" . 1)) nil))
(defun-nx osht-conclusion (cell fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((next (mv-nth 1 (fn-osh-one cell fn-arena))))
  (or (not next) (fn-osh-ready-p next fn-arena))))
(defun-nx osht-tick (n cell fn-arena)
 (declare (xargs :stobjs fn-arena :measure (nfix n) :verify-guards nil))
 (if (zp n) cell
  (osht-tick (- n 1) (mv-nth 1 (fn-osh-one cell fn-arena)) fn-arena)))

(defthm osht-positive-msgid-before-actual-cached-row
 (let* ((fn-arena '((120 13 10))) (range '("g" 1 3 7 nil t))
        (origin '(:query-source 17))
        (facts (fn-hf-make 3 nil 0
          (list nil nil nil (fn-hnov-make nil t "s" "f" "d" "<e@x>" ""))))
        (row (osht-row "<e@x>" 0 facts))
        (begin (fn-osh-begin range origin row))
        (almost (osht-tick 4 begin fn-arena))
        (next (mv-nth 1 (fn-osh-one almost fn-arena))))
  (and (fn-osh-ready-p begin fn-arena) (fn-osh-ready-p almost fn-arena)
       (osht-conclusion almost fn-arena) (fn-osh-ready-p next fn-arena)
       (equal (nth 4 almost) :msgid) (equal (nth 4 next) :row)
       (equal (nth 2 (nth 5 next)) :emit)
       (equal (nth 0 (nth 5 next)) '("g" 2 3 7 nil nil))
       (equal (nth 1 next) range) (equal (nth 2 next) origin)
       (equal (nth 3 next) row)))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (cell arena) (osht-tick 5 cell arena))
                           (:free (cell arena) (osht-tick 4 cell arena))
                           (:free (cell arena) (osht-tick 3 cell arena))
                           (:free (cell arena) (osht-tick 2 cell arena))
                           (:free (cell arena) (osht-tick 1 cell arena))
                           (:free (cell arena) (osht-tick 0 cell arena))))))

(defthm osht-positive-invalid-msgid-skips-actual-owed-state
 (let* ((fn-arena '((120 13 10))) (range '("g" 1 3 7 nil nil))
        (row (osht-row "a@b" 0 (fn-hf-make 3 nil 0 nil)))
        (begin (fn-osh-begin range '(:query-source 17) row))
        (almost (osht-tick 2 begin fn-arena))
        (next (mv-nth 1 (fn-osh-one almost fn-arena))))
  (and (fn-osh-ready-p almost fn-arena) (osht-conclusion almost fn-arena)
       (fn-osh-ready-p next fn-arena) (equal (nth 4 next) :skip)
       (equal (nth 0 (nth 5 next)) '("g" 2 3 7 nil nil))
       (equal (nth 3 next) row)))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (cell arena) (osht-tick 5 cell arena))
                           (:free (cell arena) (osht-tick 4 cell arena))
                           (:free (cell arena) (osht-tick 3 cell arena))
                           (:free (cell arena) (osht-tick 2 cell arena))
                           (:free (cell arena) (osht-tick 1 cell arena))
                           (:free (cell arena) (osht-tick 0 cell arena))))))

(defthm osht-positive-uncached-and-emission-continuations
 (let* ((fn-arena '((120 13 10))) (range '("g" 1 3 7 nil t))
        (row (osht-row "<e@x>" 0 (fn-hf-make 3 nil 0 nil)))
        (begin (fn-osh-begin range '(:query-source 17) row))
        (parsed (osht-tick 5 begin fn-arena)))
  (and (fn-osh-ready-p parsed fn-arena) (equal (nth 4 parsed) :row)
       (equal (nth 2 (nth 5 parsed)) :parse)
       (osht-conclusion parsed fn-arena)))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (cell arena) (osht-tick 5 cell arena))
                           (:free (cell arena) (osht-tick 4 cell arena))
                           (:free (cell arena) (osht-tick 3 cell arena))
                           (:free (cell arena) (osht-tick 2 cell arena))
                           (:free (cell arena) (osht-tick 1 cell arena))
                           (:free (cell arena) (osht-tick 0 cell arena))))))

; Corrupted-state literal removal of the sole carried-domain premise.
(defthm osht-removal-carried-domain
 (let* ((fn-arena '((120 13 10)))
        (row (osht-row "<e@x>" :bad (fn-hf-make 3 nil 0 nil)))
        (cell (fn-osh-begin '("g" 1 3 7 nil t) '(:query-source 17) row)))
  (and (not (fn-osh-ready-p cell fn-arena))
       (not (osht-conclusion cell fn-arena))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (cell arena) (osht-tick 5 cell arena))
                           (:free (cell arena) (osht-tick 4 cell arena))
                           (:free (cell arena) (osht-tick 3 cell arena))
                           (:free (cell arena) (osht-tick 2 cell arena))
                           (:free (cell arena) (osht-tick 1 cell arena))
                           (:free (cell arena) (osht-tick 0 cell arena))))))

(defun-nx osht-begin-conclusion (range row fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (fn-osh-ready-p (fn-osh-begin range '(:query-source 17) row) fn-arena))

(defthm osht-positive-actual-begin-antecedent-and-conclusion
 (let* ((fn-arena '((120 13 10))) (range '("g" 1 3 7 nil t))
        (row (osht-row "<e@x>" 0 (fn-hf-make 3 nil 0 nil))))
  (and (true-listp range) (natp (fn-record-payload row))
       (< (fn-record-payload row) (fn-arena-count fn-arena))
       (or (not (fn-hf-nov (fn-held-facts row)))
           (fn-hnov-p (fn-hf-nov (fn-held-facts row))))
       (osht-begin-conclusion range row fn-arena)))
 :rule-classes nil)

; Corrupted states remove each constructor premise, retaining the other three.
(defthm osht-begin-removal-range-shape
 (let* ((fn-arena '((120 13 10))) (range :bad)
        (row (osht-row "<e@x>" 0 (fn-hf-make 3 nil 0 nil))))
  (and (not (true-listp range)) (natp (fn-record-payload row))
       (< (fn-record-payload row) (fn-arena-count fn-arena))
       (or (not (fn-hf-nov (fn-held-facts row)))
           (fn-hnov-p (fn-hf-nov (fn-held-facts row))))
       (not (osht-begin-conclusion range row fn-arena))))
 :rule-classes nil)
(defthm osht-begin-removal-payload-kind
 (let* ((fn-arena '((120 13 10))) (range '("g" 1 3 7 nil t))
        (row (osht-row "<e@x>" :bad (fn-hf-make 3 nil 0 nil))))
  (and (true-listp range) (not (natp (fn-record-payload row)))
       (< (fn-record-payload row) (fn-arena-count fn-arena))
       (or (not (fn-hf-nov (fn-held-facts row)))
           (fn-hnov-p (fn-hf-nov (fn-held-facts row))))
       (not (osht-begin-conclusion range row fn-arena))))
 :rule-classes nil)
(defthm osht-begin-removal-payload-bound
 (let* ((fn-arena nil) (range '("g" 1 3 7 nil t))
        (row (osht-row "<e@x>" 0 (fn-hf-make 3 nil 0 nil))))
  (and (true-listp range) (natp (fn-record-payload row))
       (not (< (fn-record-payload row) (fn-arena-count fn-arena)))
       (or (not (fn-hf-nov (fn-held-facts row)))
           (fn-hnov-p (fn-hf-nov (fn-held-facts row))))
       (not (osht-begin-conclusion range row fn-arena))))
 :rule-classes nil)
(defthm osht-begin-removal-cached-shape
 (let* ((fn-arena '((120 13 10))) (range '("g" 1 3 7 nil t))
        (facts (fn-hf-make 3 nil 0 (list nil nil nil '(nil t 300 "" "" "" ""))))
        (row (osht-row "<e@x>" 0 facts)))
  (and (true-listp range) (natp (fn-record-payload row))
       (< (fn-record-payload row) (fn-arena-count fn-arena))
       (not (or (not (fn-hf-nov (fn-held-facts row)))
                (fn-hnov-p (fn-hf-nov (fn-held-facts row)))))
       (not (osht-begin-conclusion range row fn-arena))))
 :rule-classes nil)

(defthm osht-positive-actual-row-install-original-msgid
 (let* ((fn-arena '((120 13 10))) (range '("g" 1 3 7 nil t))
        (row (osht-row "<e@x>" 0 (fn-hf-make 3 nil 0 nil)))
        (cell (osht-tick 4 (fn-osh-begin range '(:query-source 17) row) fn-arena)))
  (and (fn-osh-ready-p cell fn-arena) (equal (nth 4 cell) :msgid)
       (equal (nth 4 (mv-nth 1 (fn-osh-one cell fn-arena))) :row)
       (fn-scat-msgid-idp (fn-record-msgid (nth 3 cell)))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (cell arena) (osht-tick 4 cell arena))
                           (:free (cell arena) (osht-tick 3 cell arena))
                           (:free (cell arena) (osht-tick 2 cell arena))
                           (:free (cell arena) (osht-tick 1 cell arena))
                           (:free (cell arena) (osht-tick 0 cell arena))))))

; Literal corrupted-state removals of the row-install predicate boundary.
(defthm osht-install-removal-semantic-carry
 (let* ((fn-arena '((120 13 10)))
        (row (osht-row "bad" 0 (fn-hf-make 3 nil 0 nil)))
        (cell (fn-osh-make '("g" 1 3 7 nil t) '(:query-source 17) row :msgid
                           '(:held-msgid "bad" 3 3 t))))
  (and (not (fn-osh-ready-p cell fn-arena))
       (equal (nth 4 cell) :msgid)
       (equal (nth 4 (mv-nth 1 (fn-osh-one cell fn-arena))) :row)
       (not (fn-scat-msgid-idp (fn-record-msgid (nth 3 cell))))))
 :rule-classes nil)
(defthm osht-install-removal-msgid-phase
 (let* ((fn-arena '((120 13 10))) (range '("g" 1 3 7 nil t))
        (row (osht-row "bad" 0 (fn-hf-make 3 nil 0 nil)))
        (cell (fn-osh-make range '(:query-source 17) row :row
                  (fn-ohr-selected-row-begin range '(:query-source 17) row fn-arena))))
  (and (fn-osh-ready-p cell fn-arena) (not (equal (nth 4 cell) :msgid))
       (equal (nth 4 (mv-nth 1 (fn-osh-one cell fn-arena))) :row)
       (not (fn-scat-msgid-idp (fn-record-msgid (nth 3 cell))))))
 :rule-classes nil)
(defthm osht-install-removal-actual-row-install
 (let* ((fn-arena '((120 13 10)))
        (row (osht-row "bad" 0 (fn-hf-make 3 nil 0 nil)))
        (cell (fn-osh-begin '("g" 1 3 7 nil t) '(:query-source 17) row)))
  (and (fn-osh-ready-p cell fn-arena) (equal (nth 4 cell) :msgid)
       (not (equal (nth 4 (mv-nth 1 (fn-osh-one cell fn-arena))) :row))
       (not (fn-scat-msgid-idp (fn-record-msgid (nth 3 cell))))))
 :rule-classes nil)
