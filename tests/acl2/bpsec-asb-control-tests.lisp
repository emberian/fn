(in-package "ACL2")
(include-book "../../books/bpsec-asb-control")

(defconst *fn-bpsct-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bpsct-bib*
  (fn-bps-asb-make 11 '(0 1) 1 0 '(:ipn 10 0) nil
                   (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65))))
                         (list (list 1 (cons :bytes (make-list 48 :initial-element 66)))))))
(defconst *fn-bpsct-wire* (fn-bps-asb-encode *fn-bpsct-bib*))
(defconst *fn-bpsct-start* (fn-bps-asb-start 11 :control 0 (len *fn-bpsct-wire*) *fn-bpsct-limits*))

(assert-event
 (and (eq (symbol-class 'fn-bps-asb-stagep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-controlp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-step (w state)) :common-lisp-compliant)))

(defun fn-bpsct-run (cursor remaining fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))))
  (if (zp (nfix fuel)) :test-fuel
    (let* ((step (fn-bps-asb-step cursor (fn-bps-window-make :control (fn-bps-get :offset cursor)
                                      (if (consp remaining) (list (car remaining)) nil)) 1))
           (next (fn-bps-field 2 step)))
      (if (not (and (fn-bps-asb-controlp cursor) (fn-bps-asb-controlp next))) :broken-control
        (if (or (eq (fn-bps-field 0 step) :more) (eq (fn-bps-field 0 step) :need-input))
            (fn-bpsct-run next (if (and (consp remaining) (equal (fn-bps-field 3 step) 1))
                                  (cdr remaining) remaining) (1- (nfix fuel)))
          (list (fn-bps-field 0 step) next))))))

; The sole control premise and complete conclusion hold at each exercised
; byte/metadata transition. This is not the full mutable grammar invariant.
(assert-event
 (let* ((run (fn-bpsct-run *fn-bpsct-start* *fn-bpsct-wire* 1024)) (cursor (fn-bps-field 1 run)))
   (and (fn-bps-asb-controlp *fn-bpsct-start*)
        (eq (fn-bps-field 0 run) :parsed) (fn-bps-asb-controlp cursor)
        (equal (fn-bps-get :stage cursor) :done)
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result cursor)
                                     (list (cons :control *fn-bpsct-wire*))) *fn-bpsct-bib*))))
(assert-event
 (and (fn-bps-asb-stagep :targets-array) (fn-bps-asb-stagep :body-finish)
      (not (fn-bps-asb-stagep nil)) (not (fn-bps-asb-stagep :unknown))))
(assert-event
 (let ((drive (fn-bps-asb-drive *fn-bpsct-start* *fn-bpsct-wire* 592)))
   (and (fn-bps-asb-controlp *fn-bpsct-start*) (fn-bps-asb-controlp (car drive))
        (eq (fn-bps-get :status (car drive)) :parsed))))
(assert-event
 (let ((cursor (fn-bps-asb-start 99 :control 0 100 *fn-bpsct-limits*)))
   (and (fn-bps-asb-controlp cursor) (eq (fn-bps-get :status cursor) :refused))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpsct-start* (fn-bps-window-make :foreign 0 *fn-bpsct-wire*) 17)))
   (and (fn-bps-asb-controlp *fn-bpsct-start*) (fn-bps-asb-controlp (fn-bps-field 2 step))
        (eq (fn-bps-field 0 step) :refused))))
; Affirmative omission tooth: corrupt only the real stage field, then make
; coordinate refusal preserve that invalid field. No other premise exists.
(assert-event
 (let* ((corrupted (fn-bps-put :stage :unknown *fn-bpsct-start*))
        (drive (fn-bps-asb-drive corrupted *fn-bpsct-wire* 17))
        (step (fn-bps-asb-step corrupted (fn-bps-window-make :foreign 0 *fn-bpsct-wire*) 17)))
   (and (not (fn-bps-asb-controlp corrupted))
        (not (fn-bps-asb-controlp (car drive)))
        (not (fn-bps-asb-controlp (fn-bps-field 2 step))))))
