; Paired actual account/config result: one CP7 authority decision supplies
; complete metadata5, publication root and root carry together. Publication
; collectors must preserve this entire result from the same prepared source.
; Source qualification does not authorize durable acceptance, funds or serving.
(in-package "ACL2")
(include-book "consumer-progress-carried")

(defun fn-carfc-result (cp root fence-count metadata rootcarry)
 (declare (xargs :guard t))
 (list :ok cp root fence-count metadata rootcarry))

(defun fn-carfc-effect (cp metadata visibility-effect)
 (declare (xargs :guard t))
 (cond ((eq visibility-effect :preserved) (list :ok cp metadata))
       ((or (eq visibility-effect :changed)
            (not (fn-cp-nth 3 (fn-cp-nth 6 cp))))
        (fn-cpm-config-preflight cp metadata))
       (t '(:refused :visibility-effect-unproved))))

(defun fn-carfc-finish-effect (one visibility-effect)
 (declare (xargs :guard t))
 (if (not (eq (fn-cp-nth 0 one) :ok)) one
  (let ((semantic (fn-carfc-effect (fn-cp-nth 1 one) (fn-cp-nth 2 one) visibility-effect)))
   (if (not (eq (fn-cp-nth 0 semantic) :ok)) semantic
    (fn-carfc-result (fn-cp-nth 1 semantic) nil nil (fn-cp-nth 2 semantic) nil)))))

(defun fn-carfc-authority-step (cp event expected metadata)
 (declare (xargs :guard t))
 (if (or (not (fn-cp-uintp expected))
         (>= (nfix expected) *fn-cbor-max-uint*)
         (not (equal (fn-cp-nth 1 event) expected)))
     '(:refused :sequence)
  (mv-let (one nextmetadata rootcarry) (fn-cpm-authority-step cp event metadata)
   (if (not (eq (fn-cp-nth 0 one) :ok)) one
    (let ((root (fn-cp-nth 2 one)))
     (fn-carfc-result (fn-cp-nth 1 one) root (if root (1+ expected) nil)
                      nextmetadata rootcarry))))))

(defun fn-carfc-config-step (cp metadata)
 (declare (xargs :guard t))
 (let ((one (fn-cpm-config-preflight cp metadata)))
  (if (eq (fn-cp-nth 0 one) :ok)
      (fn-carfc-result (fn-cp-nth 1 one) nil nil (fn-cp-nth 2 one) nil)
    one)))

(in-theory (disable fn-carfc-result fn-carfc-effect fn-carfc-finish-effect fn-carfc-authority-step fn-carfc-config-step))
