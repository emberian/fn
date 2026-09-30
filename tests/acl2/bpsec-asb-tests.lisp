(in-package "ACL2")
(include-book "../../books/bpsec-asb")

(defconst *fn-bps-test-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bps-test-bib*
  (fn-bps-asb-make 11 '(0 1) 1 0 '(:ipn 10 0) nil
                   (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65))))
                         (list (list 1 (cons :bytes (make-list 48 :initial-element 66)))))))
(defconst *fn-bps-test-wire* (fn-bps-asb-encode *fn-bps-test-bib*))

; This driver supplies genuine slices of the same immutable backing. Quantum
; one forces head, duplicate scan, reverse and body steps across invocations.
(defun fn-bps-test-run (cursor remaining quantum fuel)
  (declare (xargs :guard t :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field
                                                     fn-bps-get fn-bps-window-make)))
                  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-field
                                                           fn-bps-get fn-bps-window-make)))))
  (if (zp (nfix fuel)) (list :test-fuel cursor)
    (let* ((window (fn-bps-window-make :test (fn-bps-get :offset cursor)
                                      (if (consp remaining) (list (car remaining)) nil)))
           (step (fn-bps-asb-step cursor window quantum))
           (status (fn-bps-field 0 step)) (next (fn-bps-field 2 step)))
      (if (member-equal status '(:more :need-input))
          (fn-bps-test-run next (if (and (consp remaining) (equal (fn-bps-field 3 step) 1))
                                   (cdr remaining) remaining)
                           quantum (1- (nfix fuel)))
        (list status next)))))

(assert-event (fn-bps-asbp *fn-bps-test-bib*))
(assert-event (equal (fn-bps-asb-decode 11 *fn-bps-test-wire* *fn-bps-test-limits*)
                     (list :parsed *fn-bps-test-bib*)))
(assert-event
 (let* ((run (fn-bps-test-run (fn-bps-asb-start 11 :test 0 (len *fn-bps-test-wire*) *fn-bps-test-limits*)
                             *fn-bps-test-wire* 1 1024))
        (cursor (fn-bps-field 1 run)))
   (and (equal (fn-bps-field 0 run) :parsed)
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result cursor)
                                     (list (cons :test *fn-bps-test-wire*))) *fn-bps-test-bib*))))

; The ASB is a sequence: the first item is the targets array, not a wrapper.
(assert-event (equal (take 3 *fn-bps-test-wire*) '(130 0 1)))
(assert-event (equal (fn-bps-field 1 (fn-bps-asb-decode 11 '(128) *fn-bps-test-limits*))
                     :empty-or-invalid-targets))
(assert-event (equal (fn-bps-field 1 (fn-bps-asb-decode 11 '(130 1 1) *fn-bps-test-limits*))
                     :duplicate-target))
(assert-event (equal (fn-bps-field 0 (fn-bps-asb-decode 11 '(129 1 99) *fn-bps-test-limits*))
                     :unsupported))
(assert-event (equal (fn-bps-field 1 (fn-bps-asb-decode 11 (append *fn-bps-test-wire* '(0)) *fn-bps-test-limits*))
                     :trailing-data))
(assert-event (equal (fn-bps-field 1 (fn-bps-asb-decode 11 (take (1- (len *fn-bps-test-wire*)) *fn-bps-test-wire*)
                                                       *fn-bps-test-limits*)) :truncated))
(assert-event
 (let* ((start (fn-bps-asb-start 11 :test 0 (len *fn-bps-test-wire*) *fn-bps-test-limits*))
        (zero (fn-bps-asb-step start (fn-bps-window-make :test 0 *fn-bps-test-wire*) 0))
        (wrong (fn-bps-asb-step start (fn-bps-window-make :other 0 *fn-bps-test-wire*) 1))
        (missing (fn-bps-asb-step start (fn-bps-window-make :test 0 nil) 1)))
   (and (equal (fn-bps-field 0 zero) :more) (equal (fn-bps-field 3 zero) 0)
        (equal (fn-bps-field 2 zero) start)
        (equal (fn-bps-field 1 wrong) :window-coordinate)
        (equal (fn-bps-field 0 missing) :need-input))))
(assert-event (and (fn-bps-security-resultp :verified) (fn-bps-security-resultp :failed)
                   (fn-bps-security-resultp :unsupported) (not (fn-bps-security-resultp :uncertain))))

(assert-event
 (equal (fn-bps-asb-decode 11 (append (take 4 *fn-bps-test-wire*) '(8) (nthcdr 5 *fn-bps-test-wire*))
                          *fn-bps-test-limits*)
        (list :parsed (fn-bps-asb-make 11 '(0 1) 1 8 '(:ipn 10 0) nil (fn-bps-field 7 *fn-bps-test-bib*)))))
(assert-event
 (equal (fn-bps-field 1
          (fn-bps-asb-decode 11 (append (take 4 *fn-bps-test-wire*) '(1)
                                       (take 5 (nthcdr 5 *fn-bps-test-wire*)) '(128)
                                       (nthcdr 10 *fn-bps-test-wire*)) *fn-bps-test-limits*))
        :empty-parameters))
(defconst *fn-bps-test-bcb*
  (fn-bps-asb-make 12 '(1) 2 1 '(:dtn-none)
                   (list (list 1 (cons :bytes '(0 1 2 3 4 5 6 7 8 9 10 11)))) '(nil)))
(assert-event (equal (fn-bps-asb-decode 12 (fn-bps-asb-encode *fn-bps-test-bcb*) *fn-bps-test-limits*)
                     (list :parsed *fn-bps-test-bcb*)))
