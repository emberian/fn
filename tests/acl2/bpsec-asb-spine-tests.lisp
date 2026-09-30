; Fixed cursor spine is a carried invariant, not served revalidation.
(in-package "ACL2")
(include-book "../../books/bpsec-asb-spine")

(defconst *fn-bpsst-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bpsst-bib*
  (fn-bps-asb-make 11 '(0 1) 1 0 '(:ipn 10 0) nil
                   (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65))))
                         (list (list 1 (cons :bytes (make-list 48 :initial-element 66)))))))
(defconst *fn-bpsst-wire* (fn-bps-asb-encode *fn-bpsst-bib*))
(defconst *fn-bpsst-start*
  (fn-bps-asb-start 11 :spine 0 (len *fn-bpsst-wire*) *fn-bpsst-limits*))

(assert-event
 (and (eq (symbol-class 'fn-bps-cursor-spinep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-start (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-step (w state)) :common-lisp-compliant)))

(defun fn-bpsst-run (cursor remaining fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))))
  (if (zp (nfix fuel)) :test-fuel
    (let* ((step (fn-bps-asb-step cursor (fn-bps-window-make :spine (fn-bps-get :offset cursor)
                                       (if (consp remaining) (list (car remaining)) nil)) 1))
           (next (fn-bps-field 2 step)))
      (if (not (and (fn-bps-cursor-spinep *fn-bps-asb-spine* cursor)
                    (fn-bps-cursor-spinep *fn-bps-asb-spine* next))) :broken-spine
        (if (or (eq (fn-bps-field 0 step) :more) (eq (fn-bps-field 0 step) :need-input))
            (fn-bpsst-run next (if (and (consp remaining) (equal (fn-bps-field 3 step) 1))
                                  (cdr remaining) remaining) (1- (nfix fuel)))
          (list (fn-bps-field 0 step) next))))))

; Complete start/step invariant antecedents and conclusions through every
; exercised grammar, duplicate-scan, reversal and nonempty body transition.
(assert-event
 (let* ((run (fn-bpsst-run *fn-bpsst-start* *fn-bpsst-wire* 1024))
        (cursor (fn-bps-field 1 run)))
   (and (fn-bps-cursor-spinep *fn-bps-asb-spine* *fn-bpsst-start*)
        (equal (len *fn-bps-asb-spine*) 34)
        (eq (fn-bps-field 0 run) :parsed)
        (fn-bps-cursor-spinep *fn-bps-asb-spine* cursor)
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result cursor)
                                     (list (cons :spine *fn-bpsst-wire*))) *fn-bpsst-bib*))))
(assert-event
 (let ((drive (fn-bps-asb-drive *fn-bpsst-start* *fn-bpsst-wire* 592)))
   (and (fn-bps-cursor-spinep *fn-bps-asb-spine* *fn-bpsst-start*)
        (fn-bps-cursor-spinep *fn-bps-asb-spine* (car drive))
        (eq (fn-bps-get :status (fn-bps-field 0 drive)) :parsed))))
(assert-event
 (let ((refused (fn-bps-asb-start 99 :spine 0 100 *fn-bpsst-limits*)))
   (and (fn-bps-cursor-spinep *fn-bps-asb-spine* refused)
        (eq (fn-bps-get :status refused) :refused))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpsst-start* (fn-bps-window-make :foreign 0 *fn-bpsst-wire*) 17)))
   (and (fn-bps-cursor-spinep *fn-bps-asb-spine* *fn-bpsst-start*)
        (fn-bps-cursor-spinep *fn-bps-asb-spine* (fn-bps-field 2 step))
        (eq (fn-bps-field 0 step) :refused))))
; Hypothesis-removal witness for drive/step preservation: corrupt the actual
; cursor spine by dropping its first key. All other inputs remain literal.
(assert-event
 (let* ((corrupted (cdr *fn-bpsst-start*))
        (drive (fn-bps-asb-drive corrupted *fn-bpsst-wire* 17))
        (step (fn-bps-asb-step corrupted (fn-bps-window-make :spine 0 *fn-bpsst-wire*) 17)))
   (and (not (fn-bps-cursor-spinep *fn-bps-asb-spine* corrupted))
        (not (fn-bps-cursor-spinep *fn-bps-asb-spine* (car drive)))
        (not (fn-bps-cursor-spinep *fn-bps-asb-spine* (fn-bps-field 2 step))))))
