(in-package "ACL2")
(include-book "../../books/bpsec-asb-position")

(defconst *fn-bpspt-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bpspt-bib*
  (fn-bps-asb-make 11 '(0 1) 1 0 '(:ipn 10 0) nil
                   (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65))))
                         (list (list 1 (cons :bytes (make-list 48 :initial-element 66)))))))
(defconst *fn-bpspt-wire* (fn-bps-asb-encode *fn-bpspt-bib*))
(defconst *fn-bpspt-start* (fn-bps-asb-start 11 :position 100 (len *fn-bpspt-wire*) *fn-bpspt-limits*))

(assert-event
 (and (eq (symbol-class 'fn-bps-asb-readonly-keyp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-coordinate (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-step (w state)) :common-lisp-compliant)))

(defun fn-bpspt-run (cursor remaining fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get)))))
  (if (zp (nfix fuel)) :test-fuel
    (let* ((step (fn-bps-asb-step cursor (fn-bps-window-make :position (fn-bps-get :offset cursor)
                                      (if (consp remaining) (list (car remaining)) nil)) 1))
           (next (fn-bps-field 2 step)))
      (if (not (and (natp (fn-bps-get :offset cursor))
                    (natp (fn-bps-field 3 step))
                    (equal (fn-bps-asb-coordinate next) (fn-bps-asb-coordinate cursor))
                    (equal (fn-bps-get :offset next)
                           (+ (fn-bps-get :offset cursor) (fn-bps-field 3 step))))) :broken-position
        (if (or (eq (fn-bps-field 0 step) :more) (eq (fn-bps-field 0 step) :need-input))
            (fn-bpspt-run next (if (and (consp remaining) (equal (fn-bps-field 3 step) 1))
                                  (cdr remaining) remaining) (1- (nfix fuel)))
          (list (fn-bps-field 0 step) next))))))

; Complete offset premise/conclusion and unconditional source-coordinate
; conclusion at every exercised byte or internal metadata transition.
(assert-event
 (let* ((run (fn-bpspt-run *fn-bpspt-start* *fn-bpspt-wire* 1024)) (cursor (fn-bps-field 1 run)))
   (and (natp (fn-bps-get :offset *fn-bpspt-start*))
        (eq (fn-bps-field 0 run) :parsed)
        (equal (fn-bps-asb-coordinate cursor) (fn-bps-asb-coordinate *fn-bpspt-start*))
        (equal (fn-bps-get :offset cursor) (+ 100 (len *fn-bpspt-wire*)))
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result cursor)
                    (list (cons :position (append (make-list 100 :initial-element 0) *fn-bpspt-wire*))))
               *fn-bpspt-bib*))))
(assert-event
 (let ((drive (fn-bps-asb-drive *fn-bpspt-start* *fn-bpspt-wire* 592)))
   (and (fn-bps-asb-readonly-keyp :backing)
        (equal (fn-bps-get :backing (car drive)) (fn-bps-get :backing *fn-bpspt-start*))
        (natp (fn-bps-get :offset *fn-bpspt-start*))
        (equal (fn-bps-get :offset (car drive))
               (+ (fn-bps-get :offset *fn-bpspt-start*) (fn-bps-field 1 drive)))
        (eq (fn-bps-get :status (car drive)) :parsed))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpspt-start* (fn-bps-window-make :position 100 nil) 17)))
   (and (natp (fn-bps-get :offset *fn-bpspt-start*)) (eq (fn-bps-field 0 step) :need-input)
        (equal (fn-bps-asb-coordinate (fn-bps-field 2 step)) (fn-bps-asb-coordinate *fn-bpspt-start*))
        (equal (fn-bps-get :offset (fn-bps-field 2 step))
               (+ (fn-bps-get :offset *fn-bpspt-start*) (fn-bps-field 3 step))))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpspt-start* (fn-bps-window-make :position 100 *fn-bpspt-wire*) 0)))
   (and (natp (fn-bps-get :offset *fn-bpspt-start*)) (equal (fn-bps-field 3 step) 0)
        (equal (fn-bps-asb-coordinate (fn-bps-field 2 step)) (fn-bps-asb-coordinate *fn-bpspt-start*))
        (equal (fn-bps-get :offset (fn-bps-field 2 step))
               (+ (fn-bps-get :offset *fn-bpspt-start*) (fn-bps-field 3 step))))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpspt-start* (fn-bps-window-make :foreign 100 *fn-bpspt-wire*) 17)))
   (and (natp (fn-bps-get :offset *fn-bpspt-start*)) (eq (fn-bps-field 0 step) :refused)
        (equal (fn-bps-asb-coordinate (fn-bps-field 2 step)) (fn-bps-asb-coordinate *fn-bpspt-start*))
        (equal (fn-bps-get :offset (fn-bps-field 2 step))
               (+ (fn-bps-get :offset *fn-bpspt-start*) (fn-bps-field 3 step))))))
; Hypothesis removal, not a mutation: :offset is an ordinary mutable key.
(assert-event
 (let ((drive (fn-bps-asb-drive *fn-bpspt-start* *fn-bpspt-wire* 17)))
   (and (not (fn-bps-asb-readonly-keyp :offset))
        (not (equal (fn-bps-get :offset (car drive)) (fn-bps-get :offset *fn-bpspt-start*))))))
; Corrupted-state omission: absent offset fails the sole numeric premise and
; both exact equations. No claimed theorem assumes this cursor is reachable.
(assert-event
 (let* ((corrupted (remove-assoc-equal :offset *fn-bpspt-start*))
        (drive (fn-bps-asb-drive corrupted *fn-bpspt-wire* 17))
        (step (fn-bps-asb-step corrupted (fn-bps-window-make :foreign 100 *fn-bpspt-wire*) 17)))
   (and (not (natp (fn-bps-get :offset corrupted)))
        (not (equal (fn-bps-get :offset (car drive))
                    (+ (fix (fn-bps-get :offset corrupted)) (fn-bps-field 1 drive))))
        (not (equal (fn-bps-get :offset (fn-bps-field 2 step))
                    (+ (fix (fn-bps-get :offset corrupted)) (fn-bps-field 3 step)))))))
