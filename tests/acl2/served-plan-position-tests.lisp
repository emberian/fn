(in-package "ACL2")
(include-book "../../books/served-plan-position")

(defconst *sppt-plan*
 '(nil (:log accepted) (:retain source)
       (:over-cursor ("fn.test" 1 100000 7 nil t))
       (:reply (50 48 53 13 10)) (:close)))

(defthm sppt-actual-paid-positioning-positive
 (let* ((origin '(:response 11 29)) (resource '(:funded 31))
        (p (fn-spp-begin *sppt-plan* origin resource))
        (first (fn-spp-tick p 1)) (p1 (mv-nth 1 first))
        (second (fn-spp-tick p1 1)) (p2 (mv-nth 1 second)))
  (and (consp *sppt-plan*) (not (fn-spp-holderp *sppt-plan*))
       (equal (fn-spp-plan p) *sppt-plan*)
       (posp 1) (equal (fn-spp-status p) :position)
       (equal (mv-nth 0 first) :yield) (equal (mv-nth 2 first) 1)
       (equal (fn-spp-plan p1) *sppt-plan*)
       (equal (fn-spp-prefix p1) '((:log accepted)))
       (equal (fn-spp-origin p1) origin) (equal (fn-spp-resource p1) resource)
       (equal (fn-spp-status p1) :position)
       (equal (mv-nth 0 second) :cursor) (equal (mv-nth 2 second) 1)
       (equal (fn-spp-plan p2) *sppt-plan*)
       (equal (fn-spp-prefix p2) '((:retain source) (:log accepted)))
       (equal (fn-spp-origin p2) origin) (equal (fn-spp-resource p2) resource)
       (equal (+ (mv-nth 2 second) (len (fn-spp-rest p2))) (len (fn-spp-rest p1)))
       (equal (fn-spp-tick-conses p1 1) 13)
       (<= (fn-spp-tick-conses p1 1) (+ 3 (* 10 1)))
       (equal (fn-spp-rest p2) (cdddr *sppt-plan*))
       (equal (fn-spp-active-plan p2) (cons nil (cdddr *sppt-plan*)))))
 :rule-classes nil)

; Literal removal of positive fuel: every retained premise is affirmed.
(defthm sppt-progress-without-positive-fuel
 (let ((p (fn-spp-begin *sppt-plan* :origin :funded)))
  (and (not (posp 0)) (equal (fn-spp-status p) :position)
       (not (< 0 (mv-nth 2 (fn-spp-tick p 0))))))
 :rule-classes nil)

; Literal removal of positioning status: a completed cursor head does no scan.
(defthm sppt-progress-without-positioning-status
 (let* ((p (fn-spp-begin *sppt-plan* :origin :funded))
        (p2 (mv-nth 1 (fn-spp-tick p 2))))
  (and (posp 1) (not (equal (fn-spp-status p2) :position))
       (not (< 0 (mv-nth 2 (fn-spp-tick p2 1))))))
 :rule-classes nil)

(defthm sppt-begin-without-original-cons-corrupted-state
 (and (not (consp 7)) (not (fn-spp-holderp 7))
      (not (equal (fn-spp-plan (fn-spp-begin 7 :origin :funded)) 7)))
 :rule-classes nil)

(defthm sppt-begin-without-original-representation-corrupted-state
 (let ((p (fn-spp-begin *sppt-plan* :origin :funded)))
  (and (consp p) (fn-spp-holderp p)
       (not (equal (fn-spp-plan (fn-spp-begin p :origin :funded)) p))))
 :rule-classes nil)

; Mutations distinguish trace retention and resource ownership from mere
; octet-equivalent omission of nonreply effects.
(defthm sppt-prefix-loss-mutation
 (let* ((p (mv-nth 1 (fn-spp-tick (fn-spp-begin *sppt-plan* :origin :funded) 2)))
        (mutated (fn-spp-make (fn-spp-cur p) nil (fn-spp-rest p)
                              (fn-spp-origin p) (fn-spp-resource p))))
  (and (equal (fn-spp-plan p) *sppt-plan*)
       (not (equal (fn-spp-plan mutated) *sppt-plan*))))
 :rule-classes nil)

(defthm sppt-save-preserves-full-holder-positive
 (let* ((p (mv-nth 1 (fn-spp-tick (fn-spp-begin *sppt-plan* :origin :funded) 2)))
        (active '((49) (:reply (50)) (:over-cursor :remaining) (:close)))
        (saved (fn-spp-save-active p active)))
  (and (equal (fn-spp-prefix saved) (fn-spp-prefix p))
       (equal (fn-spp-origin saved) :origin)
       (equal (fn-spp-resource saved) :funded)
       (equal (fn-spp-active-plan saved) active)
       (equal (fn-spp-plan saved)
              '((49) (:log accepted) (:retain source)
                      (:reply (50)) (:over-cursor :remaining) (:close)))))
 :rule-classes nil)

(defthm sppt-resource-loss-mutation
 (let* ((p (fn-spp-begin *sppt-plan* :origin :funded))
        (mutated (fn-spp-make (fn-spp-cur p) (fn-spp-prefix p) (fn-spp-rest p)
                              (fn-spp-origin p) :other)))
  (and (equal (fn-spp-plan mutated) (fn-spp-plan p))
       (not (equal (fn-spp-resource mutated) (fn-spp-resource p)))))
 :rule-classes nil)
