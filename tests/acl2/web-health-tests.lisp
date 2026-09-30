; Literal teeth for PRF-1100: real scheduler events and every answer class.
(in-package "ACL2")
(include-book "../../books/web-health")
(include-book "must-fail-checked")
(defun whlt-event (s kind now arg)
  (mv-let (word s2) (fn-otm-disk-event s kind now arg)
    (declare (ignore word)) s2))
(defconst *whlt-ready* (whlt-event (fn-otm-init) :space 100 '(10000 100)))
(defconst *whlt-full* (whlt-event *whlt-ready* :space 200 '(1 100)))
(defconst *whlt-pending* (whlt-event *whlt-ready* :issue 1000 '(5000 30000 1000)))
(defconst *whlt-slow* (whlt-event *whlt-pending* :clock 6000 nil))
(defconst *whlt-stalled* (whlt-event *whlt-pending* :clock 31000 nil))
; Complete success antecedent and all conclusion conjuncts, reached by
; the same :space event the host records.
(assert-event
 (and (equal (car (fn-whl-answer (fn-whl-observe *whlt-ready* nil))) 200)
      (fn-otm-sp-observedp (fn-otm-space *whlt-ready*))
      (not (equal (car (fn-otm-health-disk *whlt-ready*)) :held))
      (null nil)))
(assert-event (equal (fn-whl-answer (fn-whl-observe *whlt-ready* nil))
                     '(200 (114 101 97 100 121 10))))
(assert-event (and (equal (fn-otm-mode *whlt-slow*) :slow)
                   (equal (car (fn-whl-answer (fn-whl-observe *whlt-slow* nil))) 200)))
(assert-event (and (equal (fn-otm-mode *whlt-stalled*) :stalled)
                   (equal (car (fn-whl-answer (fn-whl-observe *whlt-stalled* nil))) 503)))
(assert-event (and (equal (fn-otm-mode *whlt-full*) :full)
                   (equal (car (fn-whl-answer (fn-whl-observe *whlt-full* nil))) 503)))
(assert-event (equal (fn-whl-answer (fn-whl-observe *whlt-ready* '(:deferred :budget 100 1)))
                     '(503 (117 110 97 118 97 105 108 97 98 108 101 32 99 104 101 99 107 112 111 105 110 116 10))))
; Remove the success antecedent: all retained hypotheses (none) hold;
; success fails and the clear-disk conclusion affirmatively fails.
(assert-event
 (and (not (equal (car (fn-whl-answer (fn-whl-observe *whlt-full* nil))) 200))
      (fn-otm-sp-observedp (fn-otm-space *whlt-full*))
      (null nil)
      (equal (car (fn-otm-health-disk *whlt-full*)) :held)))
(must-fail-checked
 (defthm whlt-without-success-antecedent
   (not (equal (car (fn-otm-health-disk *whlt-full*)) :held))
   :rule-classes nil))
; Observations not made remain unknown, including malformed mutation inputs.
(assert-event (equal (fn-whl-word (fn-whl-observe (fn-otm-init) nil)) :unobserved))
(assert-event (equal (car (fn-whl-answer (fn-whl-observe (fn-otm-init) nil))) 503))
(assert-event (equal (fn-whl-word (fn-whl-observe *whlt-ready* :malformed)) :unobserved))
(assert-event (equal (fn-whl-word '(:owner :ok nil :clear)) :unobserved))
(assert-event (equal (fn-whl-word '(:owner :unknown t :clear)) :unobserved))
(assert-event (equal (fn-whl-word '(:owner :ok t :clear extra)) :unobserved))
(assert-event (equal (fn-whl-word :malformed) :unobserved))
; The bound is attained by a nonempty checkpoint answer, not an empty body.
(assert-event
 (let ((answer (fn-whl-answer '(:owner :ok t :deferred))))
   (and (true-listp (cadr answer)) (equal (len (cadr answer)) 23)
        (<= (len (cadr answer)) 23) (member (car answer) '(200 503)))))
(assert-event
 (let ((answer (fn-whl-answer :malformed)))
   (and (true-listp (cadr answer)) (consp (cadr answer))
        (<= (len (cadr answer)) 23) (member (car answer) '(200 503)))))
