;;; Allocation observation of the actual guarded serializer and normal host
;;; dispatch. This raw probe is not an ACL2 proof or a whole-plan heap bound.
(in-package "ACL2")
(require :sb-posix)
(require :sb-bsd-sockets)

(defun fnalloc-load-host-forms (path wanted)
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval form)
                 (setf missing (remove (list (car form) (cadr form)) missing
                                       :test #'equal))))
    (when missing (error "allocation probe host forms missing: ~s" missing))))

(fnalloc-load-host-forms "host/native/io.lisp"
 '((define-condition fnn-store-error) (define-condition fnn-store-fault)
   (define-condition fnn-entry-guard-fault) (defun fnn-fault)
   (defun fnn-counterpart) (defun fnn-dispatch-function)
   (defun fnn-guard-conjuncts) (defun fnn-entry-guard-spec)
   (defun fnn-entry-guard-describe) (defun fnn-entry-guard) (defun fnn-call)))
(defvar *fnn-dispatch-counterpart* t)
(defvar *fnn-raw-dispatch* (make-hash-table :test 'eq))
(defvar *fnn-startup-creators* (make-hash-table :test 'eq))
(defvar *fnn-entry-guard-specs* (make-hash-table :test 'eq))
(defvar *fn-entry-guard-kinds* nil)

(unless (and (eq (symbol-class 'fn-sl-step (w *the-live-state*)) :common-lisp-compliant)
             (equal (fn-di-get :kinds
                      (cdr (assoc 'fn-sl-step (table-alist 'fn-interfaces (w *the-live-state*)))))
                    '((bytes natp))))
  (error "actual serializer declaration/guard class missing from loaded world"))

(format t "~%native_string_line_allocation_runtime: ~a ~a~%"
        (lisp-implementation-type) (lisp-implementation-version))

(defun fnalloc-check-result (result text bytes)
  (destructuring-bind (octets next) result
    (unless (and (= (length octets) bytes) (every (lambda (x) (= x 88)) octets)
                 (equal (second next) bytes) (eq (third next) :text)
                 (eq (first next) text))
      (error "actual serializer result or shared text custody changed"))))

;; Both strings exceed every quantum, so termination/output amount is matched.
;; Strings/cursor and the cold metadata cache are allocated before sampling.
(dolist (text-size '(16384 1048576))
  (let* ((text (make-string text-size :initial-element #\X))
         (cur (fn-sl-start text)))
    (dolist (bytes '(1 8 128 8192))
      (let* ((repetitions (max 32 (floor 32768 bytes)))
             (warm (fnn-call 'fn-sl-step cur bytes)))
        (fnalloc-check-result warm text bytes)
        (unless (eq (fnn-dispatch-function 'fn-sl-step) (fnn-counterpart 'fn-sl-step))
          (error "allocation probe did not use actual normal counterpart route"))
        (sb-ext:gc :full t)
        (let ((before (sb-ext:get-bytes-consed))
              (started (get-internal-real-time))
              (last nil))
          (dotimes (i repetitions)
            (setf last (fnn-call 'fn-sl-step cur bytes)))
          (let ((allocated (- (sb-ext:get-bytes-consed) before))
                (elapsed (- (get-internal-real-time) started)))
            (fnalloc-check-result last text bytes)
            (format t "native_string_line_allocation: text=~d quantum=~d repetitions=~d allocated=~d per_call=~,3f seconds=~,6f~%"
                    text-size bytes repetitions allocated (/ allocated repetitions 1.0d0)
                    (/ elapsed internal-time-units-per-second 1.0d0))))))))
(format t "native_string_line_allocation_raw: PASS actual normal dispatch; retained text reference and bounded output~%")
