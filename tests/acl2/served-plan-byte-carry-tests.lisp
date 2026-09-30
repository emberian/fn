(in-package "ACL2")
(include-book "../../books/served-plan-byte-carry")

(defun spct-token ()
 (mv-let (owners pins status) (fn-rpin-step nil '(31 nil nil) '(:acquire 7))
  (declare (ignore pins status)) (fn-rpin-token 7 owners)))
(defun spct-row (h)
 (declare (xargs :guard t))
 (fn-held-with-numbers
  (fn-held-plain (fn-record-make 0 1 0 "<e@x>" '(65) '("fn.test") "o" "s" "e" 1 5) h)
  '(("fn.test" . 2))))
(defun spct-plan (number)
 (declare (xargs :guard t :verify-guards nil))
 (let ((pin (spct-token)))
  (mv-let (status plan) (fn-spbc-begin
   (fn-spp-begin (cons nil (list (list :over-cursor (fn-ovw-cursor "fn.test" number 2 1 nil t))))
                 pin :resource)
   pin 1) (declare (ignore status)) plan)))

(defthm spct-actual-begin-one-positive
 (let* ((fn-arena '((65))) (fn-cat (list (spct-row 0))) (p (spct-plan 1))
        (next (fn-spbc-one p fn-arena fn-cat)))
  (and (fn-spbc-ready-p p fn-arena fn-cat) (fn-cat-p fn-cat)
       (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (fn-scol-okp fn-arena fn-cat)
       (fn-spbc-ready-p next fn-arena fn-cat)
       (equal (fn-spbc-status p) :continue)
       (equal (nth 1 (fn-spbc-quantum next)) 0)
       (equal (nth 3 (fn-spbc-quantum next)) 1)
       (equal (fn-spp-origin next) (spct-token))
       (equal (fn-spp-resource next) :resource)))
 :rule-classes nil)

; Corrupted-state literal removals assert every retained hypothesis.
(defthm spct-without-ready-corrupted-state
 (let ((fn-arena '((65))) (fn-cat (list (spct-row 0))) (p nil))
  (and (not (fn-spbc-ready-p p fn-arena fn-cat)) (fn-cat-p fn-cat)
       (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (fn-scol-okp fn-arena fn-cat)
       (not (fn-spbc-ready-p (fn-spbc-one p fn-arena fn-cat) fn-arena fn-cat))))
 :rule-classes nil)

(defthm spct-without-catalog-shape-corrupted-state
 (let ((fn-arena '((65))) (fn-cat (list (spct-row -1))) (p (spct-plan 1)))
  (and (fn-spbc-ready-p p fn-arena fn-cat) (not (fn-cat-p fn-cat))
       (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (fn-scol-okp fn-arena fn-cat)
       (not (fn-spbc-ready-p (fn-spbc-one p fn-arena fn-cat) fn-arena fn-cat))))
 :rule-classes nil)

(defthm spct-without-source-bounds-corrupted-state
 (let ((fn-arena '((65))) (fn-cat (list (spct-row 2))) (p (spct-plan 1)))
  (and (fn-spbc-ready-p p fn-arena fn-cat) (fn-cat-p fn-cat)
       (not (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
       (fn-scol-okp fn-arena fn-cat)
       (not (fn-spbc-ready-p (fn-spbc-one p fn-arena fn-cat) fn-arena fn-cat))))
 :rule-classes nil)

(defthm spct-without-cached-source-relation-corrupted-state
 (let* ((fn-arena '((65)))
        (facts (fn-hf-make 1 nil 0
                 (list nil nil nil (fn-hnov-make nil t :bad "" "" "" ""))))
        (fn-cat (list (update-nth 11 facts (spct-row 0)))) (p (spct-plan 2)))
  (and (fn-spbc-ready-p p fn-arena fn-cat) (fn-cat-p fn-cat)
       (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (not (fn-scol-okp fn-arena fn-cat))
       (not (fn-spbc-ready-p (fn-spbc-one p fn-arena fn-cat) fn-arena fn-cat))))
 :rule-classes nil)
