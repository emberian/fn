; Exact served-step vocabulary factored from served-plan.
(in-package "ACL2")
(include-book "cbor")

(defun fn-splan-step-make (effects closep starttlsp submittedp consumed refusal-lines
                                   exposure-close)
  (declare (xargs :guard t))
  (list :served-step effects (and closep t) (and starttlsp t) (and submittedp t)
        (nfix consumed) refusal-lines exposure-close))

(defun fn-splan-step-p (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 8) (eq (car x) :served-step)
       (true-listp (nth 1 x))
       (booleanp (nth 2 x)) (booleanp (nth 3 x)) (booleanp (nth 4 x))
       (natp (nth 5 x)) (true-listp (nth 6 x))
       (or (null (nth 7 x)) (fn-cbor-octet-listp (nth 7 x)))))

(defun fn-splan-step-effects (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 1 x))
(defun fn-splan-step-closep (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 2 x))
(defun fn-splan-step-starttlsp (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 3 x))
(defun fn-splan-step-submittedp (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 4 x))
(defun fn-splan-step-consumed (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 5 x))
(defun fn-splan-step-refusal-lines (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 6 x))
(defun fn-splan-step-exposure-close (x) (declare (xargs :guard (fn-splan-step-p x))) (nth 7 x))

(defthm fn-splan-step-make-is-a-step
  (implies (and (true-listp effects) (true-listp refusal-lines)
                (or (null exposure-close) (fn-cbor-octet-listp exposure-close)))
           (fn-splan-step-p (fn-splan-step-make effects closep starttlsp submittedp consumed
                                                refusal-lines exposure-close))))

(defthm fn-splan-step-accessors-of-make
  (and (equal (fn-splan-step-effects (fn-splan-step-make e c s u n r x)) e)
       (equal (fn-splan-step-closep (fn-splan-step-make e c s u n r x)) (and c t))
       (equal (fn-splan-step-starttlsp (fn-splan-step-make e c s u n r x)) (and s t))
       (equal (fn-splan-step-submittedp (fn-splan-step-make e c s u n r x)) (and u t))
       (equal (fn-splan-step-consumed (fn-splan-step-make e c s u n r x)) (nfix n))
       (equal (fn-splan-step-refusal-lines (fn-splan-step-make e c s u n r x)) r)
       (equal (fn-splan-step-exposure-close (fn-splan-step-make e c s u n r x)) x)))

