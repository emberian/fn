; Literal teeth for exact complete cursor/consumed-prefix/suffix quantum cuts.
(in-package "ACL2")
(include-book "../../books/bpsec-asb-quanta")

(defconst *fn-bpsqt-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bpsqt-bib*
  (fn-bps-asb-make 11 '(0 1) 1 0 '(:ipn 10 0) nil
                   (list (list (list 1 (cons :bytes (make-list 48 :initial-element 65))))
                         (list (list 1 (cons :bytes (make-list 48 :initial-element 66)))))))
(defconst *fn-bpsqt-wire* (fn-bps-asb-encode *fn-bpsqt-bib*))
(defconst *fn-bpsqt-start*
  (fn-bps-asb-start 11 :quanta 0 (len *fn-bpsqt-wire*) *fn-bpsqt-limits*))

(assert-event
 (and (eq (symbol-class 'fn-bps-asb-drive (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bps-asb-step (w state)) :common-lisp-compliant)))

(defun fn-bpsqt-cut (cursor octets q1 q2)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-drive fn-bps-field fn-bps-get)))))
  (let* ((first (fn-bps-asb-drive cursor octets q1))
         (second (fn-bps-asb-drive (fn-bps-field 0 first) (fn-bps-field 2 first) q2)))
    (equal (fn-bps-asb-drive cursor octets (+ (nfix q1) (nfix q2)))
           (list (fn-bps-field 0 second) (+ (fn-bps-field 1 first) (fn-bps-field 1 second))
                 (fn-bps-field 2 second)))))

; Unconditional theorem, no omitted hypotheses. The positive examples traverse
; target duplicate scans, metadata reversal and nonempty per-target byte spans.
(assert-event
 (and (fn-bps-asbp *fn-bpsqt-bib*) (consp *fn-bpsqt-wire*)
      (fn-bpsqt-cut *fn-bpsqt-start* *fn-bpsqt-wire* 3 7)
      (fn-bpsqt-cut *fn-bpsqt-start* *fn-bpsqt-wire* 12 5)
      (fn-bpsqt-cut *fn-bpsqt-start* *fn-bpsqt-wire* 71 521)))
(assert-event
 (let* ((first (fn-bps-asb-drive *fn-bpsqt-start* *fn-bpsqt-wire* 71))
        (second (fn-bps-asb-drive (fn-bps-field 0 first) (fn-bps-field 2 first) 521))
        (cursor (fn-bps-field 0 second)))
   (and (eq (fn-bps-get :status cursor) :parsed)
        (equal (+ (fn-bps-field 1 first) (fn-bps-field 1 second)) (len *fn-bpsqt-wire*))
        (equal (fn-bps-field 2 second) nil)
        (equal (fn-bps-asb-span-alpha (fn-bps-asb-span-result cursor)
                                     (list (cons :quanta *fn-bpsqt-wire*))) *fn-bpsqt-bib*)
        (equal (fn-bps-asb-drive *fn-bpsqt-start* *fn-bpsqt-wire* 592)
               (list cursor (+ (fn-bps-field 1 first) (fn-bps-field 1 second)) nil)))))
(assert-event
 (let* ((cursor (fn-bps-asb-start 11 :quanta 0 3 *fn-bpsqt-limits*))
        (result (fn-bps-asb-drive cursor '(130 1 1) 24)))
   (and (fn-bpsqt-cut cursor '(130 1 1) 4 20)
        (eq (fn-bps-get :status (fn-bps-field 0 result)) :refused)
        (eq (fn-bps-get :reason (fn-bps-field 0 result)) :duplicate-target))))
(assert-event
 (let* ((cursor (fn-bps-asb-start 11 :quanta 0 99 *fn-bpsqt-limits*))
        (result (fn-bps-asb-drive cursor '(129 1) 20)))
   (and (fn-bpsqt-cut cursor '(129 1) 10 10)
        (eq (fn-bps-get :status (fn-bps-field 0 result)) :need-input)
        (equal (fn-bps-field 1 result) 2))))
(assert-event
 (let* ((cursor (fn-bps-asb-start 11 :quanta 0 2 *fn-bpsqt-limits*))
        (result (fn-bps-asb-drive cursor '(129 1) 20)))
   (and (fn-bpsqt-cut cursor '(129 1) 10 10)
        (eq (fn-bps-get :status (fn-bps-field 0 result)) :refused)
        (eq (fn-bps-get :reason (fn-bps-field 0 result)) :truncated))))
(assert-event
 (and (fn-bpsqt-cut *fn-bpsqt-start* *fn-bpsqt-wire* 0 31)
      (fn-bpsqt-cut *fn-bpsqt-start* *fn-bpsqt-wire* -7 31)
      (fn-bpsqt-cut *fn-bpsqt-start* *fn-bpsqt-wire* 3/2 31)))
; Corrupted-state witness, not a reachable parser-state example. The complete
; scheduling equation is deliberately unconditional and holds here too.
(assert-event
 (and (fn-bpsqt-cut '((:status . :refused)) '(1 2 3) 12 5)
      (equal (fn-bps-asb-drive '((:status . :refused)) '(1 2 3) 17)
             '(((:status . :refused)) 0 (1 2 3)))))
