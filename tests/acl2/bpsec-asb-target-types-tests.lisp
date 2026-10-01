(in-package "ACL2")
(include-book "../../books/bpsec-asb-target-types")
(defconst *fn-bpstt-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
; Literal unwrapped RFC9172 section3.6 sequence, targets 0 and uint64 maximum.
; Ordered two target-result arrays contain real 48-octet BIB values.
(defconst *fn-bpstt-wire*
 (append '(130 0 27 255 255 255 255 255 255 255 255 1 0 130 2 130 10 0 130 129 130 1 88 48)
         (make-list 48 :initial-element 65) '(129 130 1 88 48)
         (make-list 48 :initial-element 66)))
(defconst *fn-bpstt-start* (fn-bps-asb-start 11 :targets 300 (len *fn-bpstt-wire*) *fn-bpstt-limits*))
(defconst *fn-bpstt-final* (fn-bps-field 2 (fn-bps-asb-step *fn-bpstt-start*
                          (fn-bps-window-make :targets 300 *fn-bpstt-wire*) 1024)))
(assert-event
 (and (eq (symbol-class 'fn-bps-asb-target-typesp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-target-type-contextp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-step (w state)) :common-lisp-compliant)))
(assert-event (fn-bps-uint-listp '(0 18446744073709551615)))
(assert-event (fn-bps-asb-target-typesp *fn-bpstt-start*))
(assert-event (fn-bps-asb-target-type-contextp *fn-bpstt-start*))
(defun fn-bpstt-run (cursor remaining fuel)
 (declare (xargs :guard t :measure (nfix fuel)
                 :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get fn-bps-asb-target-type-contextp)))
                 :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get fn-bps-asb-target-type-contextp)))))
 (if (zp (nfix fuel)) :test-fuel
   (let* ((step (fn-bps-asb-step cursor (fn-bps-window-make :targets (fn-bps-get :offset cursor)
                                (if (consp remaining) (list (car remaining)) nil)) 1))
          (next (fn-bps-field 2 step)))
    (if (not (and (fn-bps-asb-target-type-contextp cursor) (fn-bps-asb-target-type-contextp next))) :broken-type
      (if (or (eq (fn-bps-field 0 step) :more) (eq (fn-bps-field 0 step) :need-input))
       (fn-bpstt-run next (if (and (consp remaining) (equal (fn-bps-field 3 step) 1))
                            (cdr remaining) remaining) (1- (nfix fuel)))
       (list (fn-bps-field 0 step) next))))))
; Full antecedent and conclusion of START/DRIVE/STEP at reachable uint64
; duplicate-scanning and reversal transitions, using one-byte windows/q1.
(assert-event
 (let* ((run (fn-bpstt-run *fn-bpstt-start* *fn-bpstt-wire* 2048)) (next (fn-bps-field 1 run)))
  (and (equal (len *fn-bpstt-wire*) 125) (fn-bps-asb-target-type-contextp *fn-bpstt-start*)
       (eq (fn-bps-field 0 run) :parsed) (fn-bps-asb-target-type-contextp next)
       (equal (fn-bps-get :targets next) '(0 18446744073709551615)))))
(assert-event
 (let ((drive (fn-bps-asb-drive *fn-bpstt-start* *fn-bpstt-wire* 1024)))
  (and (fn-bps-asb-target-type-contextp *fn-bpstt-start*)
       (eq (fn-bps-get :status (car drive)) :parsed) (fn-bps-asb-target-type-contextp (car drive))
       (equal (fn-bps-get :targets (car drive)) '(0 18446744073709551615)))))
(assert-event
 (let* ((wire '(130 1 1)) (start (fn-bps-asb-start 11 :targets 300 63 *fn-bpstt-limits*))
        (step (fn-bps-asb-step start (fn-bps-window-make :targets 300 wire) 128)))
  (and (fn-bps-asb-target-type-contextp start) (eq (fn-bps-field 0 step) :refused)
       (eq (fn-bps-field 1 step) :duplicate-target) (fn-bps-asb-target-type-contextp (fn-bps-field 2 step)))))
(assert-event
 (let* ((wire '(129 64)) (start (fn-bps-asb-start 11 :targets 300 63 *fn-bpstt-limits*))
        (step (fn-bps-asb-step start (fn-bps-window-make :targets 300 wire) 128)))
  (and (fn-bps-asb-target-type-contextp start) (eq (fn-bps-field 0 step) :refused)
       (eq (fn-bps-field 1 step) :target-type) (fn-bps-asb-target-type-contextp (fn-bps-field 2 step)))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpstt-start* (fn-bps-window-make :targets 300 nil) 17)))
  (and (fn-bps-asb-target-type-contextp *fn-bpstt-start*) (eq (fn-bps-field 0 step) :need-input)
       (fn-bps-asb-target-type-contextp (fn-bps-field 2 step)) (equal (fn-bps-field 3 step) 0))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpstt-start* (fn-bps-window-make :foreign 300 *fn-bpstt-wire*) 17)))
  (and (fn-bps-asb-target-type-contextp *fn-bpstt-start*) (eq (fn-bps-field 0 step) :refused)
       (fn-bps-asb-target-type-contextp (fn-bps-field 2 step)) (equal (fn-bps-field 3 step) 0))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpstt-start* (fn-bps-window-make :targets 300 *fn-bpstt-wire*) 0)))
  (and (fn-bps-asb-target-type-contextp *fn-bpstt-start*) (eq (fn-bps-field 0 step) :more)
       (fn-bps-asb-target-type-contextp (fn-bps-field 2 step)) (equal (fn-bps-field 3 step) 0))))
; Corrupted states: retain typed head and exact spine, omit only the
; target-type compound premise. Quantum zero does not repair invented state.
(assert-event
 (let* ((bad (fn-bps-put :targets '(18446744073709551616) *fn-bpstt-start*)) (drive (fn-bps-asb-drive bad nil 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :targets 300 nil) 0)))
  (and (fn-bps-asb-target-type-contextp *fn-bpstt-start*) (fn-bps-asb-head-profilep bad)
       (fn-bps-cursor-spinep *fn-bps-asb-spine* bad) (not (fn-bps-asb-target-typesp bad))
       (not (fn-bps-asb-target-type-contextp bad))
       (not (fn-bps-asb-target-type-contextp (car drive)))
       (not (fn-bps-asb-target-type-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :pending -1 *fn-bpstt-start*)) (drive (fn-bps-asb-drive bad nil 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :targets 300 nil) 0)))
  (and (fn-bps-asb-target-type-contextp *fn-bpstt-start*) (fn-bps-asb-head-profilep bad)
       (fn-bps-cursor-spinep *fn-bps-asb-spine* bad) (not (fn-bps-asb-target-typesp bad))
       (not (fn-bps-asb-target-type-contextp bad))
       (not (fn-bps-asb-target-type-contextp (car drive)))
       (not (fn-bps-asb-target-type-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :scan '(-1) (fn-bps-put :pending 1 (fn-bps-put :stage :target-duplicate *fn-bpstt-start*)))) (drive (fn-bps-asb-drive bad nil 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :targets 300 nil) 0)))
  (and (fn-bps-asb-target-type-contextp *fn-bpstt-start*) (fn-bps-asb-head-profilep bad)
       (fn-bps-cursor-spinep *fn-bps-asb-spine* bad) (not (fn-bps-asb-target-typesp bad))
       (not (fn-bps-asb-target-type-contextp bad))
       (not (fn-bps-asb-target-type-contextp (car drive)))
       (not (fn-bps-asb-target-type-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :reverse '(-1) (fn-bps-put :after :targets-done (fn-bps-put :stage :reverse *fn-bpstt-start*)))) (drive (fn-bps-asb-drive bad nil 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :targets 300 nil) 0)))
  (and (fn-bps-asb-target-type-contextp *fn-bpstt-start*) (fn-bps-asb-head-profilep bad)
       (fn-bps-cursor-spinep *fn-bps-asb-spine* bad) (not (fn-bps-asb-target-typesp bad))
       (not (fn-bps-asb-target-type-contextp bad))
       (not (fn-bps-asb-target-type-contextp (car drive)))
       (not (fn-bps-asb-target-type-contextp (fn-bps-field 2 step))))))
; Actual representation-omission tooth. The weak target/head invariants
; hold, but absent pending slot cannot be inserted by FN-BPS-PUT. This is
; corrupted state, not a reachable wire or evidence of an executable fault.
(assert-event
 (let* ((bad '((:status . :more) (:stage . :target) (:start . 0) (:length . 1)
              (:offset . 0) (:targets) (:head :bps-head :initial 0 0 0 0)))
        (next (car (fn-bps-asb-drive bad '(5) 1))))
  (and (fn-bps-asb-target-typesp bad) (fn-bps-asb-head-profilep bad)
       (not (fn-bps-cursor-spinep *fn-bps-asb-spine* bad))
       (not (fn-bps-asb-target-type-contextp bad))
       (eq (fn-bps-get :stage next) :target-duplicate) (equal (fn-bps-get :pending next) nil)
       (not (fn-bps-asb-target-typesp next)) (not (fn-bps-asb-target-type-contextp next)))))
(assert-event
 (let ((start (fn-bps-asb-start 0 :targets -1 -1 nil)))
  (and (eq (fn-bps-get :status start) :refused) (fn-bps-asb-target-type-contextp start))))
