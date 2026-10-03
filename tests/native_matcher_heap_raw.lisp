;;; Runs only inside an actual admitted ACL2 world. No matcher source twin.
(in-package "ACL2")
(load (concatenate 'string *fnmg-probe-root* "/tools/native_heap_graph.lisp"))
(load (concatenate 'string *fnmg-probe-root* "/host/native/trace.lisp"))

(defun fnmg-function (name &optional logical-observer)
  (let ((counterpart (find-symbol (symbol-name name) "ACL2_*1*_ACL2")))
    (unless (and (member (getpropc name 'symbol-class nil (w *the-live-state*))
                        (if logical-observer '(:common-lisp-compliant :ideal)
                          '(:common-lisp-compliant)))
                 counterpart (fboundp counterpart)
                 (compiled-function-p (symbol-function counterpart)))
      (error "normal guard-verified compiled counterpart unavailable: ~s" name))
    (symbol-function counterpart)))

(defparameter *fnmg-start* (fnmg-function 'fn-wmc-start))
(defparameter *fnmg-step* (fnmg-function 'fn-wmc-step))
(defparameter *fnmg-demand* (fnmg-function 'fn-wmc-demand))
(defparameter *fnmg-decided* (fnmg-function 'fn-wmc-decidedp))
(defparameter *fnmg-matched* (fnmg-function 'fn-wmc-matchedp))
;; Pure logical observers are explicitly :IDEAL, not guard-verified served
;; entries. Their admitted normal counterparts run only before measurement.
(defparameter *fnmg-remaining* (fnmg-function 'fn-wmc-remaining t))
(defparameter *fnmg-capacity* (fnmg-function 'fn-wml-owned-capacity))
(defparameter *fnmg-items* (fnmg-function 'fn-wm-total-items t))
(defparameter *fnmg-parse* (fnmg-function 'fn-wildmat-parse))
(defparameter *fnmg-result-ok* (fnmg-function 'fn-wildmat-result-okp))
(defparameter *fnmg-result-value* (fnmg-function 'fn-wildmat-result-value))
(defparameter *fnmg-octets* (fnmg-function 'fn-nntp-string-octets))

(defun fnmg-next (state)
  (funcall *fnmg-step* state 1 (funcall *fnmg-demand* state)))

(defun fnmg-drain (initial initial-fuel)
  ;; ACL2's proved remaining-work bound supplies this diagnostic termination
  ;; check; it is not a new protocol ceiling or production scheduling policy.
  (let ((state initial) (fuel initial-fuel))
    (loop until (funcall *fnmg-decided* state) do
      (unless (plusp fuel) (error "actual matcher exhausted its remaining-work bound"))
      (setf state (fnmg-next state)) (decf fuel))
    state))

(defun fnmg-case (id pattern-text input)
  (let* ((parsed (funcall *fnmg-parse* (funcall *fnmg-octets* pattern-text))))
    (unless (funcall *fnmg-result-ok* parsed) (error "probe pattern refused"))
    (let* ((patterns (funcall *fnmg-result-value* parsed))
           (p (length patterns)) (m (funcall *fnmg-items* patterns)) (n (length input))
           (capacity (funcall *fnmg-capacity* p m n))
           (borrowed (fnmg-graph (list patterns input)))
           (initial (funcall *fnmg-start* patterns input)) (state initial)
           (owned (fnmg-owned (fnmg-graph (list state)) borrowed))
           (initial-fuel (funcall *fnmg-remaining* initial))
           (fuel initial-fuel) (index 0))
      (format t "~%FN_MATCHER_GRAPH {\"type\":\"case\",\"case_id\":~d,\"patterns\":~d,\"tokens\":~d,\"input_octets\":~d,\"owned_cons_bound\":~d,\"allocation_replays\":32,\"borrowed\":~a}~%"
              id p m n capacity (fnmg-json-summary borrowed))
      (format t "FN_MATCHER_GRAPH {\"type\":\"state\",\"case_id\":~d,\"step\":0,\"owned\":~a,\"over_bound\":~a}~%"
              id (fnmg-json-summary owned) (if (> (getf (fnmg-summary owned) :conses) capacity) "true" "false"))
      (loop until (funcall *fnmg-decided* state) do
        (unless (plusp fuel) (error "actual matcher exhausted its remaining-work bound"))
        (let* ((next (fnmg-next state))
               (next-owned (fnmg-owned (fnmg-graph (list next)) borrowed))
               (overlap (fnmg-union owned next-owned)))
          (incf index) (decf fuel)
          (format t "FN_MATCHER_GRAPH {\"type\":\"state\",\"case_id\":~d,\"step\":~d,\"owned\":~a,\"old_new_union\":~a,\"over_bound\":~a,\"union_over_single_state_bound\":~a}~%"
                  id index (fnmg-json-summary next-owned) (fnmg-json-summary overlap)
                  (if (> (getf (fnmg-summary next-owned) :conses) capacity) "true" "false")
                  (if (> (getf (fnmg-summary overlap) :conses) capacity) "true" "false"))
          (setf state next owned next-owned)))
      (format t "FN_MATCHER_GRAPH {\"type\":\"done\",\"case_id\":~d,\"steps\":~d,\"matched\":~a}~%"
              id index (if (funcall *fnmg-matched* state) "true" "false"))
      ;; Observer graph allocations are outside the matched measurement.
      ;; Each replay starts from identical initial state; no snapshots retained.
      (dotimes (i 4) (fnmg-drain initial initial-fuel))
      (sb-ext:gc :full t)
      (fnn-trace-span (:matcher-round :operation id)
        (dotimes (i 32) (fnmg-drain initial initial-fuel))))))

(fnn-trace-start :capacity 16 :allocation :isolated-process)
(loop for (pattern input) in
      (list (list "*" "")
            (list "*ab*,*ccc,!*ddd" "abb")
            (list "fn.*,!fn.block,fn.block.good" "fn.block.good")
            (list "*a*a*a*b,*b*b*b*a" "aaaaaaaaaaaa")
            (list (coerce (mapcar #'code-char '(195 169)) 'string)
                  (coerce (mapcar #'code-char '(195 169)) 'string))
            (list "*" (coerce (mapcar #'code-char '(240 159 152 128)) 'string))
            (list "*" (coerce (list (code-char 128)) 'string))
            (list "*z,*" (make-string 460 :initial-element #\a))
            (list "*" (make-string 461 :initial-element #\a))
            (list "*" (make-string *fn-wildmat-max-octets* :initial-element #\a))
            (list "*" (make-string (1+ *fn-wildmat-max-octets*) :initial-element #\a)))
      for id from 1 do (fnmg-case id pattern input))
(fnn-trace-report *standard-output*)
(setf *fnn-trace-state* nil)
(format t "NATIVE_MATCHER_HEAP_PASS~%")
