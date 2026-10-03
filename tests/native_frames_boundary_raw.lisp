;;; The actual frames driver signals to its held/off-owner boundary; it never
;;; recursively acquires owner exclusion from an inline commit quantum.
(load "tests/native_section_envelope_raw.lisp")
(in-package "ACL2")
(load-deployed-forms "books/owner-queued-work.lisp"
 '((defun fn-oqw-phases) (defun fn-oqw-terminalp) (defun fn-oqw-after)
   (defun fn-oqw-start) (defun fn-oqw-step) (defun fn-oqw-outcome-of-final)))
(load-deployed-forms "books/failure-scope.lisp" '((defun fn-fs-classify-job)))
(load-deployed-forms "host/native/owner.lisp"
 '((defstruct (fnn-owner-job (:constructor %make-fnn-owner-job)))
   (defun fnn-owner-job-word) (defun fnn-owner-run-job) (defun fnn-owner-frames-job)
   (defvar *fnn-owner-last-fault*) (defun fnn-owner-stop-service)
   (defun fnn-owner-fence-service) (defun fnn-owner-fault-service)
   (defun fnn-owner-thread-escape)))
(defun fnn-core (name &rest args)
  (unless (member name '(fn-oqw-start fn-oqw-step fn-oqw-outcome-of-final))
    (error "unexpected core subject ~a" name))
  (apply (symbol-function name) args))
(define-condition frames-phase-fault (serious-condition) ())
(defvar *frames-condition* nil)
(defun fnn-owner-job-items (service items)
  (declare (ignore service items))
  (when *frames-condition* (error *frames-condition*)))

(dolist (class '(nil fnn-store-indeterminate frames-phase-fault))
  ;; The held counterpart is the real generated section fence boundary.
  (let ((s (make-svc))
        (*frames-condition* (and class (if (eq class 'fnn-store-indeterminate) (make-condition class :message "injected uncertainty") (make-condition class)))))
    (let ((answer (outcome
                   (lambda ()
                     (fnn-quantum-control
                      s nil (lambda () (fnn-owner-frames-job
                                        s (%make-fnn-owner-job :intents '(:observed)))))))))
      (case class
        ((nil) (check (equal answer '(:values nil)) "successful frames returns through held section"))
        (fnn-store-indeterminate
         (check (and (equal answer '(:condition "fnn-store-indeterminate"))
                     (member (list +fnn-exit-uncertain+ t) (svc-stops s) :test #'equal))
                "uncertain inline phase fences through held boundary"))
        (t (check (and (equal answer '(:condition "fnn-store-fault"))
                       (member (list +fnn-exit-fault+ t) (svc-stops s) :test #'equal))
                  "fault inline phase reaches held boundary without reentry")))))
  ;; The same typed verdict reaches the actual thread boundary off owner.
  (let ((s (make-svc))
        (*frames-condition* (and class (if (eq class 'fnn-store-indeterminate) (make-condition class :message "injected uncertainty") (make-condition class)))))
    (check (not (sb-thread:holding-mutex-p (svc-lock s))) "thread entry is outside owner")
    (handler-case (fnn-owner-frames-job s (%make-fnn-owner-job :intents '(:observed)))
      (serious-condition (e) (fnn-owner-thread-escape s e "frames raw")))
    (check (if class
               (member (list (if (eq class 'fnn-store-indeterminate)
                                 +fnn-exit-uncertain+ +fnn-exit-fault+) t)
                       (svc-stops s) :test #'equal)
             (null (svc-stops s)))
           "off-owner frames outcome uses the matching existing boundary")))
(format t "~&native_frames_boundary_raw: PASS held and off-owner actual driver outcomes~%")
