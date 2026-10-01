(in-package "ACL2")
(include-book "../../books/bpsec-asb-body")

(defconst *fn-bpsbt-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bpsbt-bib*
  (fn-bps-asb-make 11 '(0 1) 1 0 '(:ipn 10 0) nil
                   (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65))))
                         (list (list 1 (cons :bytes (make-list 48 :initial-element 66)))))))
(defconst *fn-bpsbt-wire* (fn-bps-asb-encode *fn-bpsbt-bib*))
(defconst *fn-bpsbt-start* (fn-bps-asb-start 11 :body 100 (len *fn-bpsbt-wire*) *fn-bpsbt-limits*))
(defconst *fn-bpsbt-bcb*
  (fn-bps-asb-make 12 '(1) 2 1 '(:dtn 47 47 110 111 100 101 47 115 101 114 118 105 99 101)
                   (list (list 1 (cons :bytes (make-list 12 :initial-element 67)))) (list nil)))
(defconst *fn-bpsbt-bcb-wire* (fn-bps-asb-encode *fn-bpsbt-bcb*))
(defconst *fn-bpsbt-bcb-start*
  (fn-bps-asb-start 12 :body 100 (len *fn-bpsbt-bcb-wire*) *fn-bpsbt-limits*))
(defconst *fn-bpsbt-span* (fn-bps-span-make :bytes-span :body 100 1))

(assert-event
 (and (eq (symbol-class 'fn-bps-asb-extentp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-span-in-sourcep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-body-boundedp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-body-contextp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-body-inputp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-step (w state)) :common-lisp-compliant)))
(assert-event (fn-bps-asb-body-contextp *fn-bpsbt-start*))
(assert-event (fn-bps-span-in-sourcep *fn-bpsbt-span* *fn-bpsbt-start*))

(defun fn-bpsbt-run (cursor remaining fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get fn-bps-asb-body-contextp)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get fn-bps-asb-body-contextp)))))
  (if (zp (nfix fuel)) :test-fuel
    (let* ((step (fn-bps-asb-step cursor (fn-bps-window-make :body (fn-bps-get :offset cursor)
                                      (if (consp remaining) (list (car remaining)) nil)) 1))
           (next (fn-bps-field 2 step)))
      (if (not (and (fn-bps-asb-body-contextp cursor) (fn-bps-asb-body-contextp next))) :broken-body-span
        (if (or (eq (fn-bps-field 0 step) :more) (eq (fn-bps-field 0 step) :need-input))
            (fn-bpsbt-run next (if (and (consp remaining) (equal (fn-bps-field 3 step) 1))
                                  (cdr remaining) remaining) (1- (nfix fuel)))
          (list (fn-bps-field 0 step) next))))))

; Full composite antecedent/conclusion at every byte and metadata transition.
; The retained nonempty last result span has literal source offset/length and
; bytes; neither its identity nor these bounds establish a physical provider.
(assert-event
 (let* ((run (fn-bpsbt-run *fn-bpsbt-start* *fn-bpsbt-wire* 2048))
        (next (fn-bps-field 1 run))
        (backings (list (cons :body (append (make-list 100 :initial-element 0) *fn-bpsbt-wire*)))))
   (and (fn-bps-uintp 100) (fn-bps-uintp (len *fn-bpsbt-wire*))
        (<= (+ 100 (len *fn-bpsbt-wire*)) *fn-bpc-max-uint*)
        (fn-bps-asb-body-contextp *fn-bpsbt-start*) (eq (fn-bps-field 0 run) :parsed)
        (fn-bps-asb-body-contextp next) (not (null (fn-bps-get :body next)))
        (equal (fn-bps-get :body next) (fn-bps-span-make :bytes-span :body 169 48))
        (fn-bps-span-in-sourcep (fn-bps-get :body next) next)
        (equal (fn-bps-span-octets (fn-bps-get :body next) backings) (make-list 48 :initial-element 66))
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result next) backings) *fn-bpsbt-bib*))))
(assert-event
 (let* ((run (fn-bpsbt-run *fn-bpsbt-bcb-start* *fn-bpsbt-bcb-wire* 2048)) (next (fn-bps-field 1 run)))
   (and (fn-bps-asbp *fn-bpsbt-bcb*) (consp *fn-bpsbt-bcb-wire*)
        (fn-bps-asb-body-contextp *fn-bpsbt-bcb-start*) (eq (fn-bps-field 0 run) :parsed)
        (fn-bps-asb-body-contextp next) (fn-bps-span-in-sourcep (fn-bps-get :body next) next)
        (equal (fn-bps-field 3 (fn-bps-get :body next)) 12)
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result next)
                   (list (cons :body (append (make-list 100 :initial-element 0) *fn-bpsbt-bcb-wire*))))
               *fn-bpsbt-bcb*))))
(assert-event
 (let ((drive (fn-bps-asb-drive *fn-bpsbt-start* *fn-bpsbt-wire* 592)))
   (and (fn-bps-asb-body-contextp *fn-bpsbt-start*)
        (fn-bps-asb-body-contextp (car drive)) (eq (fn-bps-get :status (car drive)) :parsed))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpsbt-start* (fn-bps-window-make :body 100 nil) 17)))
   (and (fn-bps-asb-body-contextp *fn-bpsbt-start*) (eq (fn-bps-field 0 step) :need-input)
        (fn-bps-asb-body-contextp (fn-bps-field 2 step)))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpsbt-start* (fn-bps-window-make :foreign 100 *fn-bpsbt-wire*) 17)))
   (and (fn-bps-asb-body-contextp *fn-bpsbt-start*) (eq (fn-bps-field 0 step) :refused)
        (fn-bps-asb-body-contextp (fn-bps-field 2 step)))))
; Each start omission affirmatively retains both other profile hypotheses.
(assert-event
 (and (not (fn-bps-uintp -1)) (fn-bps-uintp 3) (<= (+ -1 3) *fn-bpc-max-uint*)
      (not (fn-bps-asb-body-contextp (fn-bps-asb-start 11 :body -1 3 *fn-bpsbt-limits*)))))
(assert-event
 (and (fn-bps-uintp 100) (not (fn-bps-uintp -1)) (<= (+ 100 -1) *fn-bpc-max-uint*)
      (not (fn-bps-asb-body-contextp (fn-bps-asb-start 11 :body 100 -1 *fn-bpsbt-limits*)))))
(assert-event
 (and (fn-bps-uintp *fn-bpc-max-uint*) (fn-bps-uintp 1)
      (not (<= (+ *fn-bpc-max-uint* 1) *fn-bpc-max-uint*))
      (not (fn-bps-asb-body-contextp
            (fn-bps-asb-start 11 :body *fn-bpc-max-uint* 1 *fn-bpsbt-limits*)))))
; Corrupted-state omission mutates only the body descriptor. Scalar range and
; nested head remain valid, but a body outside declared extent fails the sole
; composite invariant and both unchanged zero-quantum output conclusions.
(assert-event
 (let* ((corrupted (fn-bps-put :body (fn-bps-span-make :bytes-span :body 99 1) *fn-bpsbt-start*))
        (drive (fn-bps-asb-drive corrupted *fn-bpsbt-wire* 0))
        (step (fn-bps-asb-step corrupted (fn-bps-window-make :body 100 *fn-bpsbt-wire*) 0)))
   (and (fn-bps-asb-extentp corrupted) (fn-bps-asb-positionp corrupted)
        (fn-bps-asb-head-profilep corrupted) (not (fn-bps-asb-body-boundedp corrupted))
        (not (fn-bps-asb-body-contextp corrupted))
        (not (fn-bps-asb-body-contextp (car drive)))
        (not (fn-bps-asb-body-contextp (fn-bps-field 2 step))))))
(assert-event
 (and (not (fn-bps-span-in-sourcep (fn-bps-span-make :bytes-span :foreign 100 1) *fn-bpsbt-start*))
      (not (fn-bps-span-in-sourcep (fn-bps-span-make :bytes-span :body 100 118) *fn-bpsbt-start*))))
