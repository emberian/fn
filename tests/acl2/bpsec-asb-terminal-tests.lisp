(in-package "ACL2")
(include-book "../../books/bpsec-asb-terminal")

(defconst *fn-bpste-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
; Literal unwrapped RFC9172 ASB sequence: target 1, context 1, no parameters,
; source ipn:10.0, one result ID1 with 48 actual octets. No encoder oracle.
(defconst *fn-bpste-wire*
  (append '(129 1 1 0 130 2 130 10 0 129 129 130 1 88 48)
          (make-list 48 :initial-element 65)))
(defconst *fn-bpste-start* (fn-bps-asb-start 11 :terminal 200 63 *fn-bpste-limits*))
(defconst *fn-bpste-final*
  (fn-bps-field 2 (fn-bps-asb-step *fn-bpste-start*
                    (fn-bps-window-make :terminal 200 *fn-bpste-wire*) 592)))

(assert-event
 (and (eq (symbol-class 'fn-bps-asb-terminalp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-step (w state)) :common-lisp-compliant)))
(assert-event (fn-bps-asb-terminalp *fn-bpste-start*))
(assert-event (fn-bps-asb-terminalp *fn-bpste-final*))

(defun fn-bpste-run (cursor remaining fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get fn-bps-asb-terminalp)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get fn-bps-asb-terminalp)))))
  (if (zp (nfix fuel)) :test-fuel
    (let* ((step (fn-bps-asb-step cursor (fn-bps-window-make :terminal (fn-bps-get :offset cursor)
                                      (if (consp remaining) (list (car remaining)) nil)) 1))
           (next (fn-bps-field 2 step)))
      (if (not (and (fn-bps-asb-terminalp cursor) (fn-bps-asb-terminalp next))) :broken-terminal
        (if (or (eq (fn-bps-field 0 step) :more) (eq (fn-bps-field 0 step) :need-input))
            (fn-bpste-run next (if (and (consp remaining) (equal (fn-bps-field 3 step) 1))
                                  (cdr remaining) remaining) (1- (nfix fuel)))
          (list (fn-bps-field 0 step) next))))))

; Reachable full antecedent/conclusion, including PARSED rather than the
; vacuous active-state implication, at every byte and metadata transition.
(assert-event
 (let* ((run (fn-bpste-run *fn-bpste-start* *fn-bpste-wire* 2048)) (next (fn-bps-field 1 run)))
   (and (equal (len *fn-bpste-wire*) 63) (fn-bps-asb-terminalp *fn-bpste-start*)
        (eq (fn-bps-field 0 run) :parsed) (fn-bps-asb-terminalp next)
        (eq (fn-bps-get :status next) :parsed) (eq (fn-bps-get :stage next) :done)
        (equal (fn-bps-get :offset next) 263)
        (equal (fn-bps-get :offset next)
               (+ (nfix (fn-bps-get :start next)) (nfix (fn-bps-get :length next)))))))
(assert-event
 (let ((drive (fn-bps-asb-drive *fn-bpste-start* *fn-bpste-wire* 592)))
   (and (fn-bps-asb-terminalp *fn-bpste-start*) (fn-bps-asb-terminalp (car drive))
        (eq (fn-bps-get :status (car drive)) :parsed) (eq (fn-bps-get :stage (car drive)) :done)
        (equal (fn-bps-get :offset (car drive)) 263)
        (equal (fn-bps-field 1 drive) 63) (equal (fn-bps-field 2 drive) nil))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpste-start* (fn-bps-window-make :terminal 200 nil) 17)))
   (and (fn-bps-asb-terminalp *fn-bpste-start*) (eq (fn-bps-field 0 step) :need-input)
        (fn-bps-asb-terminalp (fn-bps-field 2 step)) (equal (fn-bps-field 3 step) 0))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpste-start* (fn-bps-window-make :foreign 200 *fn-bpste-wire*) 17)))
   (and (fn-bps-asb-terminalp *fn-bpste-start*) (eq (fn-bps-field 0 step) :refused)
        (fn-bps-asb-terminalp (fn-bps-field 2 step)) (equal (fn-bps-field 3 step) 0))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpste-start* (fn-bps-window-make :terminal 200 *fn-bpste-wire*) 0)))
   (and (fn-bps-asb-terminalp *fn-bpste-start*) (eq (fn-bps-field 0 step) :more)
        (fn-bps-asb-terminalp (fn-bps-field 2 step)) (equal (fn-bps-field 3 step) 0))))
(assert-event
 (let* ((short (fn-bps-asb-start 11 :terminal 200 62 *fn-bpste-limits*))
        (step (fn-bps-asb-step short (fn-bps-window-make :terminal 200 *fn-bpste-wire*) 592)))
   (and (fn-bps-asb-terminalp short) (eq (fn-bps-field 0 step) :refused)
        (eq (fn-bps-field 1 step) :truncated) (fn-bps-asb-terminalp (fn-bps-field 2 step)))))
(assert-event
 (let* ((first (fn-bps-asb-step *fn-bpste-start* (fn-bps-window-make :terminal 200 (take 62 *fn-bpste-wire*)) 592))
        (held (fn-bps-field 2 first))
        (second (fn-bps-asb-step held (fn-bps-window-make :terminal 262 '(65)) 17)))
   (and (fn-bps-asb-terminalp *fn-bpste-start*) (eq (fn-bps-field 0 first) :need-input)
        (equal (fn-bps-field 3 first) 62) (fn-bps-asb-terminalp held)
        (eq (fn-bps-field 0 second) :parsed) (fn-bps-asb-terminalp (fn-bps-field 2 second))
        (eq (fn-bps-get :stage (fn-bps-field 2 second)) :done)
        (equal (fn-bps-get :offset (fn-bps-field 2 second)) 263))))
(assert-event
 (let* ((long (fn-bps-asb-start 11 :terminal 200 64 *fn-bpste-limits*))
        (step (fn-bps-asb-step long (fn-bps-window-make :terminal 200 (append *fn-bpste-wire* '(0))) 592)))
   (and (fn-bps-asb-terminalp long) (eq (fn-bps-field 0 step) :refused)
        (eq (fn-bps-field 1 step) :trailing-data) (equal (fn-bps-field 3 step) 63)
        (equal (fn-bps-field 4 step) '(0)) (fn-bps-asb-terminalp (fn-bps-field 2 step)))))
; Corrupted-state omissions preserve the other terminal conjunct. The sole
; terminal invariant and zero-quantum drive/step conclusions both fail.
(assert-event
 (let* ((bad (fn-bps-put :stage :flags *fn-bpste-final*))
        (drive (fn-bps-asb-drive bad nil 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :terminal 263 nil) 0)))
   (and (fn-bps-asb-terminalp *fn-bpste-final*) (eq (fn-bps-get :status bad) :parsed)
        (equal (fn-bps-get :offset bad) (+ (nfix (fn-bps-get :start bad)) (nfix (fn-bps-get :length bad))))
        (not (eq (fn-bps-get :stage bad) :done)) (not (fn-bps-asb-terminalp bad))
        (not (fn-bps-asb-terminalp (car drive))) (not (fn-bps-asb-terminalp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :offset 262 *fn-bpste-final*))
        (drive (fn-bps-asb-drive bad nil 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :terminal 262 nil) 0)))
   (and (fn-bps-asb-terminalp *fn-bpste-final*) (eq (fn-bps-get :status bad) :parsed)
        (eq (fn-bps-get :stage bad) :done)
        (not (equal (fn-bps-get :offset bad) (+ (nfix (fn-bps-get :start bad)) (nfix (fn-bps-get :length bad)))))
        (not (fn-bps-asb-terminalp bad))
        (not (fn-bps-asb-terminalp (car drive))) (not (fn-bps-asb-terminalp (fn-bps-field 2 step))))))
; Start boundary is unconditional, including a refused profile.
(assert-event
 (let ((bad-profile (fn-bps-asb-start 0 :terminal -1 63 *fn-bpste-limits*)))
   (and (eq (fn-bps-get :status bad-profile) :refused) (fn-bps-asb-terminalp bad-profile))))
