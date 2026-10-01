(in-package "ACL2")
(include-book "../../books/bpsec-asb-aggregate")

(defconst *fn-bpsat-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bpsat-bib*
  (fn-bps-asb-make 11 '(0 1) 1 0 '(:ipn 10 0) nil
                   (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65))))
                         (list (list 1 (cons :bytes (make-list 48 :initial-element 66)))))))
(defconst *fn-bpsat-wire* (fn-bps-asb-encode *fn-bpsat-bib*))
(defconst *fn-bpsat-start* (fn-bps-asb-start 11 :body 100 (len *fn-bpsat-wire*) *fn-bpsat-limits*))
(defconst *fn-bpsat-bcb*
  (fn-bps-asb-make 12 '(1) 2 1 '(:dtn 47 47 110 111 100 101 47 115 101 114 118 105 99 101)
                   (list (list 1 (cons :bytes (make-list 12 :initial-element 67)))) (list nil)))
(defconst *fn-bpsat-bcb-wire* (fn-bps-asb-encode *fn-bpsat-bcb*))
(defconst *fn-bpsat-bcb-start*
  (fn-bps-asb-start 12 :body 100 (len *fn-bpsat-bcb-wire*) *fn-bpsat-limits*))
(defconst *fn-bpsat-span* (fn-bps-span-make :bytes-span :body 100 1))

(assert-event
 (and (eq (symbol-class 'fn-bps-tree-boundedp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-values-boundedp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-aggregatep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-extentp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-span-in-sourcep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-body-boundedp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-aggregate-contextp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-body-inputp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-step (w state)) :common-lisp-compliant)))
(assert-event (fn-bps-asb-aggregate-contextp *fn-bpsat-start*))
(assert-event (fn-bps-span-in-sourcep *fn-bpsat-span* *fn-bpsat-start*))

(defun fn-bpsat-run (cursor remaining fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get fn-bps-asb-aggregate-contextp)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field fn-bps-get fn-bps-asb-aggregate-contextp)))))
  (if (zp (nfix fuel)) :test-fuel
    (let* ((step (fn-bps-asb-step cursor (fn-bps-window-make :body (fn-bps-get :offset cursor)
                                      (if (consp remaining) (list (car remaining)) nil)) 1))
           (next (fn-bps-field 2 step)))
      (if (not (and (fn-bps-asb-aggregate-contextp cursor) (fn-bps-asb-aggregate-contextp next))) :broken-body-span
        (if (or (eq (fn-bps-field 0 step) :more) (eq (fn-bps-field 0 step) :need-input))
            (fn-bpsat-run next (if (and (consp remaining) (equal (fn-bps-field 3 step) 1))
                                  (cdr remaining) remaining) (1- (nfix fuel)))
          (list (fn-bps-field 0 step) next))))))

; Full composite antecedent/conclusion at every byte and metadata transition.
; The retained nonempty last result span has literal source offset/length and
; bytes; neither its identity nor these bounds establish a physical provider.
(assert-event
 (let* ((run (fn-bpsat-run *fn-bpsat-start* *fn-bpsat-wire* 2048))
        (next (fn-bps-field 1 run))
        (backings (list (cons :body (append (make-list 100 :initial-element 0) *fn-bpsat-wire*)))))
   (and (fn-bps-uintp 100) (fn-bps-uintp (len *fn-bpsat-wire*))
        (<= (+ 100 (len *fn-bpsat-wire*)) *fn-bpc-max-uint*)
        (fn-bps-asb-aggregate-contextp *fn-bpsat-start*) (eq (fn-bps-field 0 run) :parsed)
        (fn-bps-asb-aggregate-contextp next) (not (null (fn-bps-get :body next)))
        (equal (fn-bps-get :body next) (fn-bps-span-make :bytes-span :body 169 48))
        (fn-bps-span-in-sourcep (fn-bps-get :body next) next)
        (equal (fn-bps-span-octets (fn-bps-get :body next) backings) (make-list 48 :initial-element 66))
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result next) backings) *fn-bpsat-bib*))))
(assert-event
 (let* ((run (fn-bpsat-run *fn-bpsat-bcb-start* *fn-bpsat-bcb-wire* 2048)) (next (fn-bps-field 1 run)))
   (and (fn-bps-asbp *fn-bpsat-bcb*) (consp *fn-bpsat-bcb-wire*)
        (fn-bps-asb-aggregate-contextp *fn-bpsat-bcb-start*) (eq (fn-bps-field 0 run) :parsed)
        (fn-bps-asb-aggregate-contextp next) (fn-bps-span-in-sourcep (fn-bps-get :body next) next)
        (equal (fn-bps-field 3 (fn-bps-get :body next)) 12)
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result next)
                   (list (cons :body (append (make-list 100 :initial-element 0) *fn-bpsat-bcb-wire*))))
               *fn-bpsat-bcb*))))
(assert-event
 (let ((drive (fn-bps-asb-drive *fn-bpsat-start* *fn-bpsat-wire* 592)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*)
        (fn-bps-asb-aggregate-contextp (car drive)) (eq (fn-bps-get :status (car drive)) :parsed))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpsat-start* (fn-bps-window-make :body 100 nil) 17)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*) (eq (fn-bps-field 0 step) :need-input)
        (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step)))))
(assert-event
 (let ((step (fn-bps-asb-step *fn-bpsat-start* (fn-bps-window-make :foreign 100 *fn-bpsat-wire*) 17)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*) (eq (fn-bps-field 0 step) :refused)
        (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step)))))
; Each start omission affirmatively retains both other profile hypotheses.
(assert-event
 (and (not (fn-bps-uintp -1)) (fn-bps-uintp 3) (<= (+ -1 3) *fn-bpc-max-uint*)
      (not (fn-bps-asb-aggregate-contextp (fn-bps-asb-start 11 :body -1 3 *fn-bpsat-limits*)))))
(assert-event
 (and (fn-bps-uintp 100) (not (fn-bps-uintp -1)) (<= (+ 100 -1) *fn-bpc-max-uint*)
      (not (fn-bps-asb-aggregate-contextp (fn-bps-asb-start 11 :body 100 -1 *fn-bpsat-limits*)))))
(assert-event
 (and (fn-bps-uintp *fn-bpc-max-uint*) (fn-bps-uintp 1)
      (not (<= (+ *fn-bpc-max-uint* 1) *fn-bpc-max-uint*))
      (not (fn-bps-asb-aggregate-contextp
            (fn-bps-asb-start 11 :body *fn-bpc-max-uint* 1 *fn-bpsat-limits*)))))
; Corrupted-state omission mutates only the body descriptor. Scalar range and
; nested head remain valid, but a body outside declared extent fails the sole
; composite invariant and both unchanged zero-quantum output conclusions.
(assert-event
 (let* ((corrupted (fn-bps-put :body (fn-bps-span-make :bytes-span :body 99 1) *fn-bpsat-start*))
        (drive (fn-bps-asb-drive corrupted *fn-bpsat-wire* 0))
        (step (fn-bps-asb-step corrupted (fn-bps-window-make :body 100 *fn-bpsat-wire*) 0)))
   (and (fn-bps-asb-extentp corrupted) (fn-bps-asb-positionp corrupted)
        (fn-bps-asb-head-profilep corrupted) (not (fn-bps-asb-body-boundedp corrupted))
        (not (fn-bps-asb-aggregate-contextp corrupted))
        (not (fn-bps-asb-aggregate-contextp (car drive)))
        (not (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step))))))
(assert-event
 (and (not (fn-bps-span-in-sourcep (fn-bps-span-make :bytes-span :foreign 100 1) *fn-bpsat-start*))
      (not (fn-bps-span-in-sourcep (fn-bps-span-make :bytes-span :body 100 118) *fn-bpsat-start*))))

(defconst *fn-bpsat-parameter-bib*
  (fn-bps-asb-make 11 '(0 1) 1 1 '(:ipn 10 0)
    (list (list 1 '(:uint . 7))
          (list 2 (cons :bytes (make-list 32 :initial-element 68)))
          (list 3 '(:uint . 65535)))
    (list (list (list 1 (cons :bytes (make-list 64 :initial-element 69))))
          (list (list 1 (cons :bytes (make-list 64 :initial-element 70)))))))
(defconst *fn-bpsat-parameter-wire* (fn-bps-asb-encode *fn-bpsat-parameter-bib*))
(defconst *fn-bpsat-parameter-start*
  (fn-bps-asb-start 11 :body 100 (len *fn-bpsat-parameter-wire*) *fn-bpsat-limits*))
; Saved wrapped-key/result spans survive all scheduled scans and reversals.
(assert-event
 (let* ((run (fn-bpsat-run *fn-bpsat-parameter-start* *fn-bpsat-parameter-wire* 2048))
        (next (fn-bps-field 1 run)))
   (and (fn-bps-asbp *fn-bpsat-parameter-bib*) (consp *fn-bpsat-parameter-wire*)
        (fn-bps-uintp 100) (fn-bps-uintp (len *fn-bpsat-parameter-wire*))
        (<= (+ 100 (len *fn-bpsat-parameter-wire*)) *fn-bpc-max-uint*)
        (fn-bps-asb-aggregate-contextp *fn-bpsat-parameter-start*)
        (eq (fn-bps-field 0 run) :parsed) (fn-bps-asb-aggregate-contextp next)
        (consp (fn-bps-get :params next)) (consp (fn-bps-get :results next))
        (fn-bps-values-boundedp (fn-bps-get :params next) next)
        (fn-bps-values-boundedp (fn-bps-get :results next) next)
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result next)
                   (list (cons :body (append (make-list 100 :initial-element 0) *fn-bpsat-parameter-wire*))))
               *fn-bpsat-parameter-bib*))))
; Corrupted-state omission: mutate exactly one saved field, retain the
; complete body/source/head context, fail the sole compound invariant and
; both zero-quantum output conclusions. These are not reachable wire cases.
(assert-event
 (let* ((bad (fn-bps-put :source (fn-bps-span-make :bytes-span :body 99 1) *fn-bpsat-start*))
        (drive (fn-bps-asb-drive bad *fn-bpsat-wire* 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :body 100 *fn-bpsat-wire*) 0)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*)
        (fn-bps-asb-body-contextp bad) (not (fn-bps-asb-aggregatep bad))
        (not (fn-bps-asb-aggregate-contextp bad))
        (not (fn-bps-asb-aggregate-contextp (car drive)))
        (not (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :pending (fn-bps-span-make :bytes-span :body 99 1) *fn-bpsat-start*))
        (drive (fn-bps-asb-drive bad *fn-bpsat-wire* 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :body 100 *fn-bpsat-wire*) 0)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*)
        (fn-bps-asb-body-contextp bad) (not (fn-bps-asb-aggregatep bad))
        (not (fn-bps-asb-aggregate-contextp bad))
        (not (fn-bps-asb-aggregate-contextp (car drive)))
        (not (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :id (fn-bps-span-make :bytes-span :body 99 1) *fn-bpsat-start*))
        (drive (fn-bps-asb-drive bad *fn-bpsat-wire* 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :body 100 *fn-bpsat-wire*) 0)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*)
        (fn-bps-asb-body-contextp bad) (not (fn-bps-asb-aggregatep bad))
        (not (fn-bps-asb-aggregate-contextp bad))
        (not (fn-bps-asb-aggregate-contextp (car drive)))
        (not (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :targets (list (list 1 (fn-bps-span-make :bytes-span :body 99 1))) *fn-bpsat-start*))
        (drive (fn-bps-asb-drive bad *fn-bpsat-wire* 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :body 100 *fn-bpsat-wire*) 0)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*)
        (fn-bps-asb-body-contextp bad) (not (fn-bps-asb-aggregatep bad))
        (not (fn-bps-asb-aggregate-contextp bad))
        (not (fn-bps-asb-aggregate-contextp (car drive)))
        (not (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :params (list (list 1 (fn-bps-span-make :bytes-span :body 99 1))) *fn-bpsat-start*))
        (drive (fn-bps-asb-drive bad *fn-bpsat-wire* 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :body 100 *fn-bpsat-wire*) 0)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*)
        (fn-bps-asb-body-contextp bad) (not (fn-bps-asb-aggregatep bad))
        (not (fn-bps-asb-aggregate-contextp bad))
        (not (fn-bps-asb-aggregate-contextp (car drive)))
        (not (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :pairs (list (list 1 (fn-bps-span-make :bytes-span :body 99 1))) *fn-bpsat-start*))
        (drive (fn-bps-asb-drive bad *fn-bpsat-wire* 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :body 100 *fn-bpsat-wire*) 0)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*)
        (fn-bps-asb-body-contextp bad) (not (fn-bps-asb-aggregatep bad))
        (not (fn-bps-asb-aggregate-contextp bad))
        (not (fn-bps-asb-aggregate-contextp (car drive)))
        (not (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :results (list (list 1 (fn-bps-span-make :bytes-span :body 99 1))) *fn-bpsat-start*))
        (drive (fn-bps-asb-drive bad *fn-bpsat-wire* 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :body 100 *fn-bpsat-wire*) 0)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*)
        (fn-bps-asb-body-contextp bad) (not (fn-bps-asb-aggregatep bad))
        (not (fn-bps-asb-aggregate-contextp bad))
        (not (fn-bps-asb-aggregate-contextp (car drive)))
        (not (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :scan (list (list 1 (fn-bps-span-make :bytes-span :body 99 1))) *fn-bpsat-start*))
        (drive (fn-bps-asb-drive bad *fn-bpsat-wire* 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :body 100 *fn-bpsat-wire*) 0)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*)
        (fn-bps-asb-body-contextp bad) (not (fn-bps-asb-aggregatep bad))
        (not (fn-bps-asb-aggregate-contextp bad))
        (not (fn-bps-asb-aggregate-contextp (car drive)))
        (not (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step))))))
(assert-event
 (let* ((bad (fn-bps-put :reverse (list (list 1 (fn-bps-span-make :bytes-span :body 99 1))) *fn-bpsat-start*))
        (drive (fn-bps-asb-drive bad *fn-bpsat-wire* 0))
        (step (fn-bps-asb-step bad (fn-bps-window-make :body 100 *fn-bpsat-wire*) 0)))
   (and (fn-bps-asb-aggregate-contextp *fn-bpsat-start*)
        (fn-bps-asb-body-contextp bad) (not (fn-bps-asb-aggregatep bad))
        (not (fn-bps-asb-aggregate-contextp bad))
        (not (fn-bps-asb-aggregate-contextp (car drive)))
        (not (fn-bps-asb-aggregate-contextp (fn-bps-field 2 step))))))

(assert-event
 (and (not (fn-bps-tree-boundedp '(:bytes-span :foreign 100 1) *fn-bpsat-start*))
      (not (fn-bps-values-boundedp '((:bytes-span :body 100 118)) *fn-bpsat-start*))
      (not (fn-bps-values-boundedp '(1 . 2) *fn-bpsat-start*))
      (fn-bps-tree-boundedp '(:uint . 65535) *fn-bpsat-start*)
      (fn-bps-tree-boundedp '(:text-span :body 100 4) *fn-bpsat-start*)))

; Explicit positive recognizer anchor, separate from transition witnesses.
(defconst *fn-bpsat-values* '((1 (:bytes-span :body 100 1))))
(assert-event (fn-bps-values-boundedp *fn-bpsat-values* *fn-bpsat-start*))
