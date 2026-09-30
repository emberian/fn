;; Appended to the custody fixture: actual helpers, recording core callbacks.
;; The outer lock models the continuous span required by connection-operation.
;; It does not install the operation or establish a resource allowance.
(defun assert-extent-excludes-other-thread ()
  (assert (sb-thread:holding-mutex-p *fnn-extent-lock*))
  (let ((thread
          (sb-thread:make-thread
           (lambda ()
             (let ((acquired (sb-thread:grab-mutex *fnn-extent-lock* :waitp nil)))
               (when acquired (sb-thread:release-mutex *fnn-extent-lock*))
               acquired)))))
    (assert (null (sb-thread:join-thread thread :timeout 5)))))

(defun assert-extent-released ()
  (let ((thread
          (sb-thread:make-thread
           (lambda ()
             (sb-thread:with-mutex (*fnn-extent-lock*) :acquired)))))
    (assert (eq :acquired (sb-thread:join-thread thread :timeout 5)))))

(fresh)
(ecase __CASE__
  (:open
   (fnn-owner-serialized *service* nil
     (lambda ()
       (sb-thread:with-recursive-lock (*fnn-extent-lock*)
         (multiple-value-bind (id node)
             (fnn-owner-connection-open-locked *service* :reader nil nil nil)
           (assert (= id 41))
           (assert (eq node (fnn-owner-service-connection-head *service*)))
           (assert (eq :live (fnn-connection-custody-phase node))))
         (assert-extent-excludes-other-thread)))))
  (:close
   (multiple-value-bind (id node) (opened)
     (fnn-owner-serialized *service* id
       (lambda ()
         (sb-thread:with-recursive-lock (*fnn-extent-lock*)
           (assert (eq :closed-held
                       (fnn-owner-connection-close-locked *service* id node nil)))
           (assert (eq :retiring (fnn-connection-custody-phase node)))
           (assert-extent-excludes-other-thread))))))
  (:settle
   (multiple-value-bind (id node) (opened)
     (fnn-owner-serialized *service* id
       (lambda ()
         (sb-thread:with-recursive-lock (*fnn-extent-lock*)
           (multiple-value-bind (word left)
               (fnn-owner-connection-settle-locked *service* node 91 nil)
             (assert (eq word :held)) (assert (= left 91)))
           (assert (eq node (fnn-owner-service-connection-head *service*)))
           (assert-extent-excludes-other-thread))))))
  (:complete
   (setf *settle-word* :released)
   (fnn-owner-serialized *service* nil
     (lambda ()
       (sb-thread:with-recursive-lock (*fnn-extent-lock*)
         (multiple-value-bind (id node)
             (fnn-owner-connection-open-locked *service* :reader nil nil nil)
           (assert (eq :closed-held
                       (fnn-owner-connection-close-locked *service* id node nil)))
           ;; Repeated close of a retiring node calls actual SETTLE.
           (assert (eq :released
                       (fnn-owner-connection-close-locked *service* id node nil))))
         (assert (null (fnn-owner-service-connection-head *service*)))
         (assert (= 1 *refunds*))
         (assert-extent-excludes-other-thread)))))
  (:fault
   (setf *mode* :condition)
   (expect-fault
    (lambda ()
      (fnn-owner-serialized *service* nil
        (lambda ()
          (sb-thread:with-recursive-lock (*fnn-extent-lock*)
            (unwind-protect
                (fnn-owner-connection-open-locked *service* :reader nil nil nil)
              (assert-extent-excludes-other-thread)))))))
   (assert (eq *opaque-cause* (fnn-fixed-fault-cause *seen-fault*)))
   (assert (eq *token*
               (fnn-connection-custody-token
                (fnn-owner-service-connection-head *service*))))
   (assert (zerop *refunds*))))
(assert-extent-released)
(format t "PASS continuous connection exclusion ~s~%" __CASE__)
