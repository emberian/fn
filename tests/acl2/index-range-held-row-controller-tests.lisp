(in-package "ACL2")
(include-book "../../books/index-range-held-row-controller")

; Historical logical held15 fixture; actual sealed held16 authority is open.
(defun ibrhct-row (payload withdrawn)
 (fn-held-make 0 1 0 "<e@x>" payload '("g") "o" "s" "e" 1 5
  (fn-hf-make 3 nil 0 nil)
  (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) '(("g" . 1)) withdrawn))
(defun ibrhct-control ()
 (let* ((range '("g" 1 3 7 nil t))
        (publication (fn-ipub-make 7 nil nil 1 1 7 nil 0 11 nil 0 12 nil 13 nil nil 1 1))
        (plan (fn-spp-begin nil '(:source 17) '(:resource 18)))
        (number (fn-gns-number-step (fn-gns-number-begin 1 (cons '(:ordinal 0) nil) 1))))
  (fn-ibr-make 17 7 :row plan (list :publication-pin '(:generation 7) publication)
   (fn-gns-group-begin "g" nil) number (fn-ibr-work range publication nil nil))))
(defun-nx ibrhct-conclusion (control held fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let* ((result (fn-ibr-selected-held-row-install control held fn-arena))
        (cell (fn-spp-at 4 (fn-spp-at 8 (mv-nth 1 result)))))
  (or (not (eq (mv-nth 0 result) :held))
      (and (fn-osh-ready-p cell fn-arena) (fn-osh-selected-source-p cell)))))

(defthm ibrhct-install-positive-ordinal-zero
 (let* ((fn-arena '((65 66 67))) (control (ibrhct-control)) (held (ibrhct-row 0 nil)))
  (and (equal (fn-gns-number-result (fn-spp-at 7 control)) '(:ordinal 0))
       (fn-ibr-held-install-ready-p control held fn-arena)
       (equal (mv-nth 0 (fn-ibr-selected-held-row-install control held fn-arena)) :held)
       (ibrhct-conclusion control held fn-arena)))
 :rule-classes nil)

(defthm ibrhct-install-without-carried-domain
 (let* ((fn-arena '((65 66 67))) (control (ibrhct-control)) (held (ibrhct-row :bad nil)))
  (and (not (fn-ibr-held-install-ready-p control held fn-arena))
       (equal (mv-nth 0 (fn-ibr-selected-held-row-install control held fn-arena)) :held)
       (not (ibrhct-conclusion control held fn-arena))))
 :rule-classes nil)

(defthm ibrhct-withdrawn-row-skips-and-keeps-owed
 (let* ((fn-arena '((65 66 67))) (control (ibrhct-control)) (held (ibrhct-row 0 '(6 . 1)))
        (result (fn-ibr-selected-held-row-install control held fn-arena))
        (next (mv-nth 1 result)))
  (and (fn-ibr-held-install-ready-p control held fn-arena)
       (equal (mv-nth 0 result) :number)
       (equal (fn-spp-at 1 (fn-spp-at 1 (fn-spp-at 8 next))) 2)
       (equal (fn-spp-at 5 (fn-spp-at 1 (fn-spp-at 8 next))) t)
       (equal (fn-spp-at 4 next) (fn-spp-at 4 control))
       (equal (fn-spp-at 5 next) (fn-spp-at 5 control))))
 :rule-classes nil)

(defun-nx ibrhct-current-conclusion (control fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((result (fn-ibr-held-one control fn-arena)))
  (or (not (eq (mv-nth 1 result) :held))
      (fn-ibr-held-current-ready-p (mv-nth 2 result) fn-arena))))

(defthm ibrhct-current-one-positive
 (let* ((fn-arena '((65 66 67)))
        (control (mv-nth 1 (fn-ibr-selected-held-row-install
                      (ibrhct-control) (ibrhct-row 0 nil) fn-arena))))
  (and (fn-ibr-held-current-ready-p control fn-arena)
       (equal (mv-nth 1 (fn-ibr-held-one control fn-arena)) :held)
       (ibrhct-current-conclusion control fn-arena)))
 :rule-classes nil)

(defthm ibrhct-current-one-without-carry
 (let* ((fn-arena '((65 66 67)))
        (control (mv-nth 1 (fn-ibr-selected-held-row-install
                      (ibrhct-control) (ibrhct-row :bad nil) fn-arena))))
  (and (not (fn-ibr-held-current-ready-p control fn-arena))
       (equal (mv-nth 1 (fn-ibr-held-one control fn-arena)) :held)
       (not (ibrhct-current-conclusion control fn-arena))))
 :rule-classes nil)

(defun-nx ibrhct-three (control fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (mv-nth 2 (fn-ibr-held-one
  (mv-nth 2 (fn-ibr-held-one
   (mv-nth 2 (fn-ibr-held-one control fn-arena)) fn-arena)) fn-arena)))

(defthm ibrhct-invalid-msgid-retains-actual-owed
 (let* ((fn-arena '((65 66 67))) (original (ibrhct-control))
        (held (fn-held-make 0 1 0 "bad" 0 '("g") "o" "s" "e" 1 5
          (fn-hf-make 3 nil 0 nil)
          (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) '(("g" . 1)) nil))
        (control (mv-nth 1 (fn-ibr-selected-held-row-install original held fn-arena)))
        (next (ibrhct-three control fn-arena)))
  (and (fn-ibr-held-current-ready-p control fn-arena)
       (equal (fn-spp-at 3 next) :number)
       (equal (fn-spp-at 1 (fn-spp-at 1 (fn-spp-at 8 next))) 2)
       (equal (fn-spp-at 5 (fn-spp-at 1 (fn-spp-at 8 next))) t)
       (equal (fn-spp-at 4 next) (fn-spp-at 4 original))
       (equal (fn-spp-at 5 next) (fn-spp-at 5 original))))
 :rule-classes nil)
