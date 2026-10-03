;;; Incremental fixture in the loaned matcher world. Requires the existing
;;; native_matcher_heap_raw helpers and source-admitted constructor variants.
;;; No changed engine, source twin, saved image or certificate acquisition.
(in-package "ACL2")

(defparameter *fnmg-original-node* (symbol-function 'fn-wmc-node))
(defparameter *fnmg-original-state* (symbol-function 'fn-wmc-state))
(defparameter *fnmg-shared-node* (symbol-function 'fn-wmc-shared-node))
(defparameter *fnmg-shared-state* (symbol-function 'fn-wmc-shared-state))
(fnmg-function 'fn-wmc-shared-node)
(fnmg-function 'fn-wmc-shared-state)

(defmacro fnmg-with-constructor-route ((route) &body body)
  "Debug-only exact source leaf overlay, restored on throw/error/return."
  (let ((node (gensym "NODE")) (state (gensym "STATE")) (choice (gensym "ROUTE")))
    `(let ((,node (symbol-function 'fn-wmc-node))
           (,state (symbol-function 'fn-wmc-state)) (,choice ,route))
       (unwind-protect
            (progn
              (assert (member ,choice '(:legacy :shared)))
              (setf (symbol-function 'fn-wmc-node)
                    (if (eq ,choice :shared) *fnmg-shared-node* *fnmg-original-node*)
                    (symbol-function 'fn-wmc-state)
                    (if (eq ,choice :shared) *fnmg-shared-state* *fnmg-original-state*))
              ,@body)
         (setf (symbol-function 'fn-wmc-node) ,node
               (symbol-function 'fn-wmc-state) ,state)))))

;; Macro arguments are evaluated once, in order, without temporary capture.
(let ((counter 0) (fn-iml-arg-0 7))
  (assert (equal (fn-list/immutable (incf counter) (incf counter) (incf counter) nil)
                 '(1 2 3 nil)))
  (assert (= counter 3))
  (assert (equal (fn-list/immutable fn-iml-arg-0 (1+ fn-iml-arg-0) nil) '(7 8 nil))))
(assert (null (fn-list/immutable)))
(assert (equal (fn-list/immutable :one) '(:one)))
(assert (equal (multiple-value-list
                (fnmg-with-constructor-route (:shared) (values :a :b :c))) '(:a :b :c)))
(assert (eq (catch 'fnmg-leave
              (fnmg-with-constructor-route (:shared) (throw 'fnmg-leave :left))) :left))
(assert (handler-case (fnmg-with-constructor-route (:shared) (error "test exit"))
          (error () t)))
(assert (eq (symbol-function 'fn-wmc-node) *fnmg-original-node*))
(assert (eq (symbol-function 'fn-wmc-state) *fnmg-original-state*))

(defparameter *fnmg-product-constants*
  (fnmg-graph
   (list (cdr (fn-wmc-shared-node :tag nil nil nil nil))
         (cddr (fn-wmc-shared-node :tag :a nil nil nil))
         (cdddr (fn-wmc-shared-node :tag :a :b nil nil))
         (nthcdr 4 (fn-wmc-shared-node :tag :a :b :c nil))
         (cdr (fn-wmc-shared-state :task nil)))))
(format t "~%FN_MATCHER_OPT {\"type\":\"program-baseline\",\"constant_graph\":~a}~%"
        (fnmg-json-summary *fnmg-product-constants*))

(defun fnmg-compare-case (id pattern-text input)
  (let* ((parsed (funcall *fnmg-parse* (funcall *fnmg-octets* pattern-text))))
    (assert (funcall *fnmg-result-ok* parsed))
    (let* ((patterns (funcall *fnmg-result-value* parsed))
           (borrowed (fnmg-graph (list patterns input)))
           (old (fnmg-with-constructor-route (:legacy) (funcall *fnmg-start* patterns input)))
           (new (fnmg-with-constructor-route (:shared) (funcall *fnmg-start* patterns input)))
           (old-start old) (new-start new)
           (fuel (funcall *fnmg-remaining* old)) (initial-fuel fuel)
           (index 0) (old-peak 0) (new-peak 0))
      (loop
        (assert (equal old new))
        (assert (= (funcall *fnmg-demand* old) (funcall *fnmg-demand* new)))
        (setf old-peak (max old-peak (getf (fnmg-summary
                     (fnmg-owned (fnmg-graph (list old)) borrowed)) :direct-bytes))
              new-peak (max new-peak (getf (fnmg-summary
                     (fnmg-owned (fnmg-graph (list new)) borrowed *fnmg-product-constants*)) :direct-bytes)))
        (when (funcall *fnmg-decided* old) (return))
        (assert (plusp fuel))
        (setf old (fnmg-with-constructor-route (:legacy) (fnmg-next old))
              new (fnmg-with-constructor-route (:shared) (fnmg-next new)))
        (decf fuel) (incf index))
      (format t "FN_MATCHER_OPT {\"type\":\"case\",\"case_id\":~d,\"steps\":~d,\"equal_every_step\":true,\"legacy_owned_peak_bytes\":~d,\"shared_owned_peak_bytes\":~d,\"allocation_replays\":32}~%"
              id index old-peak new-peak)
      (dolist (route '(:legacy :shared))
        (fnmg-with-constructor-route (route)
          (let ((start (if (eq route :legacy) old-start new-start)))
            (dotimes (i 4) (fnmg-drain start initial-fuel))
            (sb-ext:gc :full t)
            (fnn-trace-span (route :operation id)
              (dotimes (i 32) (fnmg-drain start initial-fuel)))))))))

(fnn-trace-start :capacity 32 :allocation :isolated-process)
(unwind-protect
    (progn
      (loop for (pattern input) in
        (list (list "*" "") (list "*ab*,*ccc,!*ddd" "abb")
              (list "fn.*,!fn.block,fn.block.good" "fn.block.good")
              (list "*a*a*a*b,*b*b*b*a" "aaaaaaaaaaaa")
              (list "*" (coerce (mapcar #'code-char '(195 169)) 'string))
              (list "*" (coerce (mapcar #'code-char '(240 159 152 128)) 'string))
              (list "*" (coerce (list (code-char 128)) 'string))
              (list "*z,*" (make-string 460 :initial-element #\a))
              (list "*" (make-string *fn-wildmat-max-octets* :initial-element #\a))
              (list "*" (make-string (1+ *fn-wildmat-max-octets*) :initial-element #\a)))
        for id from 1 do (fnmg-compare-case id pattern input))
      (fnn-trace-report *standard-output*)
      (format t "NATIVE_IMMUTABLE_MATCHER_PASS~%"))
  (setf *fnn-trace-state* nil)
  (assert (eq (symbol-function 'fn-wmc-node) *fnmg-original-node*))
  (assert (eq (symbol-function 'fn-wmc-state) *fnmg-original-state*)))
