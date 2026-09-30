(in-package "ACL2")
(include-book "../../books/over-selected-byte-demand")
(defun osbdt-held ()
 (fn-held-make 0 1 0 "<e@x>" 0 '("g") "o" "s" "e" 1 5
  (fn-hf-make 3 nil 0 nil)
  (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) nil nil))
(defun osbdt-parser (h)
 (fn-osh-make '("g" 1 3 7 nil t) :origin (osbdt-held) :row
  (fn-obc-make '("g" 1 3 7 nil t) :origin :parse
   (list h 3 :origin 1 nil nil nil t) nil 0)))
(defun-nx osbdt-conclusion (cell)
 (declare (xargs :verify-guards nil))
 (let ((demand (fn-osh-byte-demand cell)))
  (or (not (eq (mv-nth 0 demand) :payload))
   (and (equal (mv-nth 1 demand) (fn-record-payload (fn-hmid-at 3 cell)))
        (equal (mv-nth 3 demand) (fn-hmid-at 2 cell))))))
(defthm osbdt-parser-source-positive
 (let ((cell (osbdt-parser 0)))
  (and (fn-osh-selected-source-p cell) (osbdt-conclusion cell)
       (equal (mv-nth 0 (fn-osh-byte-demand cell)) :payload)
       (equal (mv-nth 2 (fn-osh-byte-demand cell)) 1)))
 :rule-classes nil)
(defthm osbdt-without-source-corrupted-state
 (let ((cell (osbdt-parser 1)))
  (and (not (fn-osh-selected-source-p cell))
       (equal (mv-nth 0 (fn-osh-byte-demand cell)) :payload)
       (not (osbdt-conclusion cell))))
 :rule-classes nil)
(defthm osbdt-pending-cr-peek-keeps-demand
 (let ((cell (fn-osh-make '("g" 1 3 7 nil t) :origin (osbdt-held) :row
              (fn-obc-make '("g" 2 3 7 nil nil) :origin :emit nil
                '((:span 0 1 2 t :origin)) 0))))
  (and (fn-osh-selected-source-p cell) (osbdt-conclusion cell)
       (equal (mv-nth 0 (fn-osh-byte-demand cell)) :payload)
       (equal (mv-nth 1 (fn-osh-byte-demand cell)) 0)
       (equal (mv-nth 2 (fn-osh-byte-demand cell)) 1)))
 :rule-classes nil)
(defthm osbdt-zero-left-pending-cr-has-no-read
 (let ((cell (fn-osh-make '("g" 1 3 7 nil t) :origin (osbdt-held) :row
              (fn-obc-make '("g" 2 3 7 nil nil) :origin :emit nil
                '((:span 0 3 0 t :origin)) 0))))
  (and (fn-osh-selected-source-p cell) (osbdt-conclusion cell)
       (equal (mv-nth 0 (fn-osh-byte-demand cell)) :none)))
 :rule-classes nil)
(defun osbdt-span (at left)
 (fn-osh-make '("g" 1 3 7 nil t) :origin (osbdt-held) :row
   (fn-obc-make '("g" 2 3 7 nil nil) :origin :emit nil
     (list (list :span 0 at left t :origin)) 0)))
(defun-nx osbdt-bounds-conclusion (cell fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((demand (fn-osh-byte-demand cell)))
  (or (not (eq (mv-nth 0 demand) :payload))
   (and (natp (mv-nth 1 demand)) (natp (mv-nth 2 demand))
        (< (mv-nth 1 demand) (fn-arena-count fn-arena))
        (< (mv-nth 2 demand)
           (fn-arena-payload-len (mv-nth 1 demand) fn-arena))))))
(defthm osbdt-bounds-positive-pending-peek
 (let ((cell (osbdt-span 1 2)) (fn-arena '((65 66 67))))
  (and (fn-osh-ready-p cell fn-arena)
       (equal (mv-nth 0 (fn-osh-byte-demand cell)) :payload)
       (osbdt-bounds-conclusion cell fn-arena)))
 :rule-classes nil)
(defthm osbdt-bounds-without-ready-corrupted-state
 (let ((cell (osbdt-span 9 1)) (fn-arena '((65 66 67))))
  (and (not (fn-osh-ready-p cell fn-arena))
       (equal (mv-nth 0 (fn-osh-byte-demand cell)) :payload)
       (not (osbdt-bounds-conclusion cell fn-arena))))
 :rule-classes nil)
