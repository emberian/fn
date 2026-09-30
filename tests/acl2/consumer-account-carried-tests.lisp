(in-package "ACL2")
(include-book "../../books/consumer-account-carried")
(include-book "consumer-account-adoption-tests")

; Proof/fixture abstractions only. The served producer never calls these
; full-graph annotators; bootstrap/cold decode must establish equivalent data.
(defun fn-caact-row-list-annotation (rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (fn-caac-list-cons (fn-scs-summary (car rows))
                         (fn-caact-row-list-annotation (cdr rows)))
    nil))
(defun fn-caact-field-carries (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fields)
      (cons (fn-scs-summary (car fields)) (fn-caact-field-carries (cdr fields)))
    nil))
(defun fn-caact-prep-annotation (p)
  (declare (xargs :guard t :verify-guards nil))
  (if (null p) nil
    (let* ((prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep)))
      (list :prep-carries
            (fn-caact-row-list-annotation (fn-cp-nth 2 prep))
            (fn-caact-row-list-annotation (fn-cp-nth 3 prep))
            (fn-caact-row-list-annotation (fn-cp-nth 4 prep))
            (fn-cait-annotation (fn-cp-nth 2 root))
            (fn-scs-summary (fn-cp-nth 3 root))))))
(defun fn-caact-annotation (s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((a (fn-cp-nth 6 s)))
    (list :account-carries (fn-caact-field-carries s)
          (fn-caact-row-list-annotation (fn-cp-nth 4 a))
          (fn-caact-prep-annotation (fn-cp-nth 5 a)))))

(defconst *caact-initial*
  (list (list :ok *caat-initial* nil) (fn-caact-annotation *caat-initial*) nil))
(defun fn-caact-tick (previous txid op)
  (declare (xargs :guard t))
  (let* ((s (fn-cp-nth 1 (fn-cp-nth 0 previous)))
         (event (list :consumer-authority (fn-cp-nth 3 s) txid 0 op)))
    (mv-list 3 (fn-caac-step s event (fn-cp-nth 1 previous)))))
(defun fn-caact-final-op (previous kind)
  (declare (xargs :guard t))
  (let* ((s (fn-cp-nth 1 (fn-cp-nth 0 previous)))
         (p (fn-cp-nth 5 (fn-cp-nth 6 s))))
    (list kind (fn-cp-nth 1 p) (fn-cp-nth 2 p)
          (fn-cp-nth 3 p) (fn-cp-nth 7 p))))
(defun fn-caact-correctp (previous current txid op)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s (fn-cp-nth 1 (fn-cp-nth 0 previous)))
         (one (fn-cp-nth 0 current)) (next (fn-cp-nth 1 one)))
    (and (eq (fn-cp-nth 0 one) :ok)
         (equal one (fn-caa-step s (fn-caat-event s txid op)))
         (equal (fn-cp-nth 1 current) (fn-caact-annotation next))
         (equal (fn-caac-spine (fn-cp-nth 1 (fn-cp-nth 1 current)))
                (fn-scs-summary next))
         (if (fn-cp-nth 2 one)
             (equal (fn-cp-nth 2 current) (fn-scs-summary (fn-cp-nth 2 one)))
           (null (fn-cp-nth 2 current))))))

(defconst *caact-a* (fn-caact-tick *caact-initial* 1 '(:authority-begin (65) 0 1 7)))
(defconst *caact-b* (fn-caact-tick *caact-a* 2 (fn-caat-row-op '(65) 0 '(97) 2 *caat-32*)))
(defconst *caact-c* (fn-caact-tick *caact-b* 3 (fn-caact-final-op *caact-b* :authority-seal)))
(defconst *caact-d* (fn-caact-tick *caact-c* 4 '(:authority-prepare (65) 0)))
(defconst *caact-e* (fn-caact-tick *caact-d* 5 (fn-caact-final-op *caact-d* :authority-fence)))
; Complete producer prefix: no adopted authority before the exact ready fence;
; root carry and all seven CP carries agree after every actual transition.
;@positive fn-caac-step-is-logical-authority-step
(assert-event
 (and (fn-caact-correctp *caact-initial* *caact-a* 1 '(:authority-begin (65) 0 1 7))
      (fn-caact-correctp *caact-a* *caact-b* 2 (fn-caat-row-op '(65) 0 '(97) 2 *caat-32*))
      (fn-caact-correctp *caact-b* *caact-c* 3 (fn-caact-final-op *caact-b* :authority-seal))
      (fn-caact-correctp *caact-c* *caact-d* 4 '(:authority-prepare (65) 0))
      (fn-caact-correctp *caact-d* *caact-e* 5 (fn-caact-final-op *caact-d* :authority-fence))))

(defconst *caact-f* (fn-caact-tick *caact-e* 6 '(:authority-begin (66) 1 3 7)))
(defconst *caact-g* (fn-caact-tick *caact-f* 7 (fn-caat-row-op '(66) 1 '(97) 2 (make-list 32 :initial-element 10))))
(defconst *caact-h* (fn-caact-tick *caact-g* 8 (fn-caact-final-op *caact-g* :authority-seal)))
(defconst *caact-i* (fn-caact-tick *caact-h* 9 '(:authority-prepare (66) 1)))
(defconst *caact-j* (fn-caact-tick *caact-i* 10 (fn-caact-final-op *caact-i* :authority-fence)))
(assert-event
 (and (fn-caact-correctp *caact-e* *caact-f* 6 '(:authority-begin (66) 1 3 7))
      (fn-caact-correctp *caact-f* *caact-g* 7 (fn-caat-row-op '(66) 1 '(97) 2 (make-list 32 :initial-element 10)))
      (fn-caact-correctp *caact-g* *caact-h* 8 (fn-caact-final-op *caact-g* :authority-seal))
      (fn-caact-correctp *caact-h* *caact-i* 9 '(:authority-prepare (66) 1))
      (fn-caact-correctp *caact-i* *caact-j* 10 (fn-caact-final-op *caact-i* :authority-fence))))

(defconst *caact-k* (fn-caact-tick *caact-j* 11 '(:authority-begin (67) 2 8 7)))
(defconst *caact-l* (fn-caact-tick *caact-k* 12 '(:authority-tombstone (67) 2 (97) 2)))
(defconst *caact-m* (fn-caact-tick *caact-l* 13 (fn-caact-final-op *caact-l* :authority-seal)))
(defconst *caact-n* (fn-caact-tick *caact-m* 14 '(:authority-prepare (67) 2)))
(defconst *caact-o* (fn-caact-tick *caact-n* 15 (fn-caact-final-op *caact-n* :authority-fence)))
(assert-event
 (and (fn-caact-correctp *caact-j* *caact-k* 11 '(:authority-begin (67) 2 8 7))
      (fn-caact-correctp *caact-k* *caact-l* 12 '(:authority-tombstone (67) 2 (97) 2))
      (fn-caact-correctp *caact-l* *caact-m* 13 (fn-caact-final-op *caact-l* :authority-seal))
      (fn-caact-correctp *caact-m* *caact-n* 14 '(:authority-prepare (67) 2))
      (fn-caact-correctp *caact-n* *caact-o* 15 (fn-caact-final-op *caact-n* :authority-fence))))

(defconst *caact-p* (fn-caact-tick *caact-o* 16 '(:authority-begin (68) 3 13 7)))
(defconst *caact-q* (fn-caact-tick *caact-p* 17 (fn-caat-row-op '(68) 3 '(97) 17 *caat-32*)))
(defconst *caact-r* (fn-caact-tick *caact-q* 18 (fn-caact-final-op *caact-q* :authority-seal)))
(defconst *caact-s* (fn-caact-tick *caact-r* 19 '(:authority-prepare (68) 3)))
(defconst *caact-t* (fn-caact-tick *caact-s* 20 (fn-caact-final-op *caact-s* :authority-fence)))
(assert-event
 (and (fn-caact-correctp *caact-o* *caact-p* 16 '(:authority-begin (68) 3 13 7))
      (fn-caact-correctp *caact-p* *caact-q* 17 (fn-caat-row-op '(68) 3 '(97) 17 *caat-32*))
      (fn-caact-correctp *caact-q* *caact-r* 18 (fn-caact-final-op *caact-q* :authority-seal))
      (fn-caact-correctp *caact-r* *caact-s* 19 '(:authority-prepare (68) 3))
      (fn-caact-correctp *caact-s* *caact-t* 20 (fn-caact-final-op *caact-s* :authority-fence))))

; Multiple rows exercise old-list tail borrowing and one-cell reversal.
(defconst *caact-two-start*
  (list (list :ok *caat-two* nil) (fn-caact-annotation *caat-two*) nil))
(defconst *caact-u* (fn-caact-tick *caact-two-start* 8 '(:authority-begin (67) 1 4 7)))
(defconst *caact-v* (fn-caact-tick *caact-u* 9 '(:authority-tombstone (67) 1 (97) 2)))
(defconst *caact-w* (fn-caact-tick *caact-v* 10 (fn-caat-row-op '(67) 1 '(98) 3 *caat-32*)))
(defconst *caact-x* (fn-caact-tick *caact-w* 11 (fn-caat-row-op '(67) 1 '(99) 11 *caat-32*)))
(defconst *caact-y* (fn-caact-tick *caact-x* 12 (fn-caact-final-op *caact-x* :authority-seal)))
(defconst *caact-z* (fn-caact-tick *caact-y* 13 '(:authority-prepare (67) 1)))
(defconst *caact-z1* (fn-caact-tick *caact-z* 14 '(:authority-prepare (67) 1)))
(defconst *caact-z2* (fn-caact-tick *caact-z1* 15 '(:authority-prepare (67) 1)))
(defconst *caact-z3* (fn-caact-tick *caact-z2* 16 (fn-caact-final-op *caact-z2* :authority-fence)))
(assert-event
 (and (fn-caact-correctp *caact-two-start* *caact-u* 8 '(:authority-begin (67) 1 4 7))
      (fn-caact-correctp *caact-u* *caact-v* 9 '(:authority-tombstone (67) 1 (97) 2))
      (fn-caact-correctp *caact-v* *caact-w* 10 (fn-caat-row-op '(67) 1 '(98) 3 *caat-32*))
      (fn-caact-correctp *caact-w* *caact-x* 11 (fn-caat-row-op '(67) 1 '(99) 11 *caat-32*))
      (fn-caact-correctp *caact-x* *caact-y* 12 (fn-caact-final-op *caact-x* :authority-seal))
      (fn-caact-correctp *caact-y* *caact-z* 13 '(:authority-prepare (67) 1))
      (fn-caact-correctp *caact-z* *caact-z1* 14 '(:authority-prepare (67) 1))
      (fn-caact-correctp *caact-z1* *caact-z2* 15 '(:authority-prepare (67) 1))
      (fn-caact-correctp *caact-z2* *caact-z3* 16 (fn-caact-final-op *caact-z2* :authority-fence))))

; Discard and ordinary refusal cannot leave a half-ready publication sidecar.
(assert-event
 (let* ((s (fn-cp-nth 1 (fn-cp-nth 0 *caact-b*)))
        (metadata (fn-cp-nth 1 *caact-b*))
        (bad-event (fn-caat-event s 3 (fn-caact-final-op *caact-b* :authority-fence)))
        (bad (mv-list 3 (fn-caac-step s bad-event metadata)))
        (discard (fn-caact-tick *caact-b* 3 '(:authority-discard (65) 0))))
   (and (not (eq (fn-cp-nth 0 (fn-cp-nth 0 bad)) :ok))
        (equal (fn-cp-nth 1 bad) metadata) (null (fn-cp-nth 2 bad))
        (fn-caact-correctp *caact-b* discard 3 '(:authority-discard (65) 0)))))

; Corrupted-state witness: decision refinement holds even with bad carries,
; but carry readiness cannot be inferred from that equality or raw rows.
(assert-event
 (let* ((s (fn-cp-nth 1 (fn-cp-nth 0 *caact-a*)))
        (event (fn-caat-event s 2 (fn-caat-row-op '(65) 0 '(97) 2 *caat-32*)))
        (bad (mv-list 3 (fn-caac-step s event nil))))
   (and (equal (fn-cp-nth 0 bad) (fn-caa-step s event))
        (not (equal (fn-cp-nth 1 bad)
                    (fn-caact-annotation (fn-cp-nth 1 (fn-cp-nth 0 bad))))))))

;@positive fn-caac-stage-selected-is-logical-stage
(assert-event
 (let* ((s (fn-cp-nth 1 (fn-cp-nth 0 *caact-a*)))
        (a (fn-cp-nth 6 s)) (metadata (fn-cp-nth 1 *caact-a*))
        (event (fn-caat-event s 2 (fn-caat-row-op '(65) 0 '(97) 2 *caat-32*)))
        (plan (fn-caa-row-plan a event (fn-cp-nth 4 event))))
   (and (eq (fn-cp-nth 0 plan) :stage)
        (equal (fn-cp-nth 0 (mv-list 2 (fn-caac-stage-selected
                          s a event (fn-cp-nth 1 plan) (fn-cp-nth 2 plan)
                          (fn-cp-nth 3 plan) (fn-cp-nth 4 plan) metadata)))
               (fn-caa-stage-selected s a event (fn-cp-nth 1 plan)
                                      (fn-cp-nth 2 plan) (fn-cp-nth 3 plan))))))

;@positive fn-caac-spine-keeps-canonical-size
(assert-event
 (and (fn-scs-correspondsp (list (fn-scs-summary '(1 2)) (fn-scs-summary 3))
                          '((1 2) 3))
      (equal (fn-caac-spine (list (fn-scs-summary '(1 2)) (fn-scs-summary 3)))
             (fn-scs-summary '((1 2) 3)))))
;@hypothesis-removal fn-caac-spine-keeps-canonical-size correspondence
(assert-event
 (and (not (fn-scs-correspondsp (list (fn-scs-atom nil) (fn-scs-summary 3))
                               '((1 2) 3)))
      (not (equal (fn-caac-spine (list (fn-scs-atom nil) (fn-scs-summary 3)))
                   (fn-scs-summary '((1 2) 3))))))

;@positive fn-caac-list-cons-keeps-canonical-size
(assert-event
 (let ((m (fn-caact-row-list-annotation '((3 4)))))
   (and (equal (fn-scs-summary '(1 2)) (fn-scs-summary '(1 2)))
        (equal (fn-caac-list-carry m) (fn-scs-summary '((3 4))))
        (equal (fn-caac-list-carry (fn-caac-list-cons (fn-scs-summary '(1 2)) m))
               (fn-scs-summary '((1 2) (3 4)))))))
;@hypothesis-removal fn-caac-list-cons-keeps-canonical-size head-carry
(assert-event
 (let ((m (fn-caact-row-list-annotation '((3 4)))))
   (and (not (equal (fn-scs-atom nil) (fn-scs-summary '(1 2))))
        (equal (fn-caac-list-carry m) (fn-scs-summary '((3 4))))
        (not (equal (fn-caac-list-carry (fn-caac-list-cons (fn-scs-atom nil) m))
                    (fn-scs-summary '((1 2) (3 4))))))))
;@hypothesis-removal fn-caac-list-cons-keeps-canonical-size tail-carry
(assert-event
 (and (equal (fn-scs-summary '(1 2)) (fn-scs-summary '(1 2)))
      (not (equal (fn-caac-list-carry nil) (fn-scs-summary '((3 4)))))
      (not (equal (fn-caac-list-carry (fn-caac-list-cons (fn-scs-summary '(1 2)) nil))
                  (fn-scs-summary '((1 2) (3 4)))))))
