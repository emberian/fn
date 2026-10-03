;;; Actual native counterpart/registered-creator discrimination. Not a proof
;;; or a whole-plan allocation tariff; source-loaded warnings stay in the log.
(in-package "ACL2")
(require :sb-posix)
(require :sb-bsd-sockets)

(defun fnout-load-host-forms (path wanted)
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof) until (eq form :eof)
            when (and (consp form)
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval form)
                 (setf missing (remove (list (car form) (cadr form)) missing :test #'equal))))
    (when missing (error "output custody host forms missing: ~s" missing))))

(fnout-load-host-forms "host/native/io.lisp"
 '((define-condition fnn-store-error) (define-condition fnn-store-fault)
   (define-condition fnn-entry-guard-fault) (defun fnn-fault)
   (defun fnn-counterpart) (defun fnn-install-raw-dispatch)
   (defun fnn-dispatch-function) (defun fnn-guard-conjuncts)
   (defun fnn-entry-guard-spec) (defun fnn-entry-guard-describe)
   (defun fnn-entry-guard) (defun fnn-call) (defun fnn-core)))
(defvar *fnn-dispatch-counterpart* nil)
(defvar *fnn-raw-dispatch* (make-hash-table :test 'eq))
(defvar *fnn-startup-creators* (make-hash-table :test 'eq))
(defvar *fnn-entry-guard-specs* (make-hash-table :test 'eq))
(defvar *fn-entry-guard-kinds* nil)
(fnn-install-raw-dispatch :report nil)


; The actual generated producer and plan entries, using the normal selected
; counterparts. Fixture construction precedes each allocation measurement.
(setq *fnn-dispatch-counterpart* t)
(dolist (name '(fn-nntp-newnews-response-stream fn-splan-of-effects
                fn-splan-cursor-step fn-splan-donep))
 (unless (eq (fnn-dispatch-function name) (fnn-counterpart name))
  (error "NEWNEWS probe route mismatch: ~s" name)))
(let* ((a (fn-make-article "<a@x>" '(13 10 13 10 65) '("fn.test")
                           '(("fn.test" . 1)) 1 5))
       (b (fn-make-article "<b@x>" '(13 10 13 10 66) '("fn.other")
                           '(("fn.other" . 1)) 2 6))
       (groups '("fn.g0" "fn.g1" "fn.g2" "fn.g3" "fn.g4" "fn.g5"
                 "fn.g6" "fn.g7" "fn.g8" "fn.g9" "fn.test"))
       (archive (fn-make-state groups nil (list b a) 0 nil nil))
       (args (list (fn-nntp-string-octets "fn.test")
                   (fn-nntp-string-octets "20000101")
                   (fn-nntp-string-octets "000000")))
       (before (sb-ext:get-bytes-consed))
       (result (fnn-core 'fn-nntp-newnews-response-stream nil archive nil args nil nil))
       (factory-consed (- (sb-ext:get-bytes-consed) before))
       (plan (fnn-core 'fn-splan-of-effects (cdr result))))
 (unless (and (null (car result)) (fn-nnw-meta-effectp (car (cdr result))))
  (error "actual NEWNEWS factory did not return the configured cursor"))
 (format t "~%native_newnews_allocation: factory ~d bytes~%" factory-consed)
 (let ((answer (fnn-call 'fn-splan-cursor-step plan 1 nil nil)))
  (unless (eq (first answer) :ok) (error "actual sparse metadata plan could not step"))
  (format t "native_newnews_allocation: first actual plan step PASS~%")))


; Matched repeated factory samples resolve SBCL's allocation-region granularity.
; Configured group and article fixture growth occurs before the timed interval.
(dolist (sizes '((11 2) (1024 2) (65536 2) (11 4096)))
 (destructuring-bind (group-count article-count) sizes
  (let* ((groups (append (make-list (- group-count 1) :initial-element "fn.other")
                        (list "fn.test")))
         (article (fn-make-article "<a@x>" '(13 10 13 10 65) '("fn.test")
                                   '(("fn.test" . 1)) 1 5))
         (archive (fn-make-state groups nil (make-list article-count :initial-element article) 0 nil nil))
         (args (list (fn-nntp-string-octets "fn.test")
                     (fn-nntp-string-octets "20000101")
                     (fn-nntp-string-octets "000000")))
         (iterations 1024) (last-result nil))
   (dotimes (i 8) (fnn-core 'fn-nntp-newnews-response-stream nil archive nil args nil nil))
   (sb-ext:gc :full t)
   (let ((before (sb-ext:get-bytes-consed)))
    (dotimes (i iterations)
     (setf last-result (fnn-core 'fn-nntp-newnews-response-stream nil archive nil args nil nil)))
    (unless (fn-nnw-meta-effectp (cadr last-result)) (error "factory benchmark changed effect"))
    (format t "native_newnews_allocation: factory-sample groups=~d articles=~d repeats=~d allocated=~d~%"
            group-count article-count iterations (- (sb-ext:get-bytes-consed) before))))))



; Actual native window allocator and renderer, followed by actual plan steps.
(fnout-load-host-forms "host/native/io.lisp"
 '((deftype fnn-octets) (defun fnn-make-octets)))
(fnout-load-host-forms "host/native/owner.lisp"
 '((defun fnn-make-render-buffer) (defun fnn-owner-render-next)))
(defun fnout-drain-newnews (archive args quantum)
 (let* ((result (fnn-core 'fn-nntp-newnews-response-stream nil archive nil args nil nil))
        (plan (fnn-core 'fn-splan-of-effects (cdr result)))
        (output (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))
        (steps 0) (cursor-steps 0))
  (loop until (fnn-core 'fn-splan-donep plan) do
   (incf steps)
   (when (> steps 10000) (error "test fixture failed to make progress"))
   (multiple-value-bind (octets rest donep cursorp) (fnn-owner-render-next plan)
    (declare (ignore donep))
    (setf plan rest)
    (if cursorp
        (let ((answer (fnn-call 'fn-splan-cursor-step plan quantum nil nil)))
         (unless (eq (first answer) :ok) (error "actual cursor could not step"))
         (incf cursor-steps) (setf plan (second answer)))
      (loop for octet across octets do (vector-push-extend octet output)))))
  (values output steps cursor-steps)))
(let* ((a (fn-make-article "<a@x>" '(13 10 13 10 65) '("fn.test") '(("fn.test" . 1)) 1 5))
       (b (fn-make-article "<b@x>" '(13 10 13 10 66) '("fn.other") '(("fn.other" . 1)) 2 6))
       (archive (fn-make-state '("fn.g0" "fn.g1" "fn.g2" "fn.test") nil (list b a) 0 nil nil))
       (args (list (fn-nntp-string-octets "fn.test") (fn-nntp-string-octets "20000101") (fn-nntp-string-octets "000000"))))
 (multiple-value-bind (tiny tiny-steps tiny-cur) (fnout-drain-newnews archive args 1)
  (multiple-value-bind (large large-steps large-cur) (fnout-drain-newnews archive args 256)
   (unless (equalp tiny large) (error "actual tiny/large window drain changed reply"))
   (let ((reference (fn-served-reply-octets
                      (cdr (fn-nntp-newnews-response-cat nil archive nil args nil nil)))))
    (unless (equalp tiny (coerce reference '(vector (unsigned-byte 8))))
     (error "actual composed window drain differs from original NEWNEWS reply")))
   (format t "native_newnews_allocation: actual-render-drain octets=~d tiny-steps=~d/~d large-steps=~d/~d~%" (length tiny) tiny-steps tiny-cur large-steps large-cur))))
(format t "native_newnews_allocation_raw: PASS normal actual configured factory, plan, native window drain and matched factory samples~%")
