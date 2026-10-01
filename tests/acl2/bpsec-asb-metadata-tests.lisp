(in-package "ACL2")
(include-book "../../books/bpsec-asb-metadata")

(defconst *fn-bpsmt-bib*
  (fn-bps-asb-make 11 '(0 1) 1 0 '(:ipn 10 0) nil
                   (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65))))
                         (list (list 1 (cons :bytes (make-list 48 :initial-element 66)))))))
(defconst *fn-bpsmt-wire* (fn-bps-asb-encode *fn-bpsmt-bib*))
(defconst *fn-bpsmt-limits8* (fn-bps-limits-make 4096 128 16 16 2048 8))
(defconst *fn-bpsmt-start* (fn-bps-asb-start 11 :metadata 0 (len *fn-bpsmt-wire*) *fn-bpsmt-limits8*))
(assert-event
 (and (eq (symbol-class 'fn-bps-asb-metadatap (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-step (w state)) :common-lisp-compliant)))
(assert-event (fn-bps-asb-metadatap *fn-bpsmt-start*))

(defun fn-bpsmt-run (cursor remaining fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))))
  (if (zp (nfix fuel)) :test-fuel
    (let* ((step (fn-bps-asb-step cursor (fn-bps-window-make :metadata (fn-bps-get :offset cursor)
                                      (if (consp remaining) (list (car remaining)) nil)) 1))
           (next (fn-bps-field 2 step)))
      (if (not (and (fn-bps-asb-metadatap cursor) (fn-bps-asb-metadatap next))) :broken-charge
        (if (or (eq (fn-bps-field 0 step) :more) (eq (fn-bps-field 0 step) :need-input))
            (fn-bpsmt-run next (if (and (consp remaining) (equal (fn-bps-field 3 step) 1))
                                  (cdr remaining) remaining) (1- (nfix fuel)))
          (list (fn-bps-field 0 step) next))))))

; Literal charge boundary: two targets + two result arrays + two result
; pairs charge exactly eight. Every byte/metadata transition carries the
; complete tracked-budget antecedent/conclusion, distinct from memory cost.
(assert-event
 (let* ((run (fn-bpsmt-run *fn-bpsmt-start* *fn-bpsmt-wire* 1024)) (next (fn-bps-field 1 run)))
   (and (fn-bps-asb-metadatap *fn-bpsmt-start*) (eq (fn-bps-field 0 run) :parsed)
        (fn-bps-asb-metadatap next) (equal (fn-bps-get :charge next) 8)
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result next)
                                     (list (cons :metadata *fn-bpsmt-wire*))) *fn-bpsmt-bib*))))
(assert-event
 (let* ((limits (fn-bps-limits-make 4096 128 16 16 2048 7))
        (start (fn-bps-asb-start 11 :metadata 0 (len *fn-bpsmt-wire*) limits))
        (run (fn-bpsmt-run start *fn-bpsmt-wire* 1024)) (next (fn-bps-field 1 run)))
   (and (fn-bps-limitsp limits) (fn-bps-asb-metadatap start)
        (eq (fn-bps-field 0 run) :refused) (eq (fn-bps-get :reason next) :metadata-limit)
        (fn-bps-asb-metadatap next) (equal (fn-bps-get :charge next) 6))))
(assert-event
 (let* ((limits (fn-bps-limits-make 4096 128 16 16 2048 0))
        (start (fn-bps-asb-start 11 :metadata 0 (len *fn-bpsmt-wire*) limits))
        (run (fn-bpsmt-run start *fn-bpsmt-wire* 1024)) (next (fn-bps-field 1 run)))
   (and (fn-bps-limitsp limits) (fn-bps-asb-metadatap start)
        (eq (fn-bps-field 0 run) :refused) (eq (fn-bps-get :reason next) :metadata-limit)
        (fn-bps-asb-metadatap next) (equal (fn-bps-get :charge next) 0))))
(assert-event
 (let ((drive (fn-bps-asb-drive *fn-bpsmt-start* *fn-bpsmt-wire* 592)))
   (and (fn-bps-asb-metadatap *fn-bpsmt-start*) (fn-bps-asb-metadatap (car drive))
        (eq (fn-bps-get :status (car drive)) :parsed) (equal (fn-bps-get :charge (car drive)) 8))))
; Large operator budget is not replaced by a private implementation ceiling.
(assert-event
 (let* ((limits (fn-bps-limits-make 4096 128 16 16 2048 1099511627776))
        (start (fn-bps-asb-start 11 :metadata 0 (len *fn-bpsmt-wire*) limits))
        (step (fn-bps-asb-step start (fn-bps-window-make :metadata 0 *fn-bpsmt-wire*) 592)))
   (and (fn-bps-limitsp limits) (fn-bps-asb-metadatap start)
        (eq (fn-bps-field 0 step) :parsed) (fn-bps-asb-metadatap (fn-bps-field 2 step))
        (equal (fn-bps-get :charge (fn-bps-field 2 step)) 8))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpsmt-start* (fn-bps-window-make :foreign 0 *fn-bpsmt-wire*) 17)))
   (and (fn-bps-asb-metadatap *fn-bpsmt-start*) (eq (fn-bps-field 0 step) :refused)
        (fn-bps-asb-metadatap (fn-bps-field 2 step)) (equal (fn-bps-get :charge (fn-bps-field 2 step)) 0))))
; Start establishes a zero tracked charge even for a refused invalid profile;
; this says nothing about admission or operator profile validity.
(assert-event (fn-bps-asb-metadatap (fn-bps-asb-start 99 :metadata -1 -1 nil)))
; Corrupted-state omission: mutate only charge above the real carried cap,
; then quantum zero preserves the failed invariant in drive and step.
(assert-event
 (let* ((corrupted (fn-bps-put :charge 9 *fn-bpsmt-start*))
        (drive (fn-bps-asb-drive corrupted *fn-bpsmt-wire* 0))
        (step (fn-bps-asb-step corrupted (fn-bps-window-make :metadata 0 *fn-bpsmt-wire*) 0)))
   (and (not (fn-bps-asb-metadatap corrupted))
        (not (fn-bps-asb-metadatap (car drive)))
        (not (fn-bps-asb-metadatap (fn-bps-field 2 step))))))
