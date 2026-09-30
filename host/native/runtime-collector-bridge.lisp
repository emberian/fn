;;; Fixed native transport for the actual allocation-epoch core callbacks.
;;; Requires the selected fixed-tag FNN-CORE-MV bridge from native/io.lisp.
;;; INTERNAL until the real installer, SAMEpool locking, turn receipts and
;;; participant coverage are joined. No function below constructs a tariff.
(in-package "ACL2")

(defstruct (fnn-runtime-collector-binding
            (:constructor %make-fnn-runtime-collector-binding)
            (:copier nil))
  pool observation request complete fence)

(defun fnn-runtime-collector-binding-make (pool)
  "Construct during funded installation; missing verified callbacks refuse.
POOL is the actual installed process pool, not a per-worker substitute."
  (%make-fnn-runtime-collector-binding
   :pool pool :observation (make-fnn-runtime-collection)
   :request (fnn-fixed-raw-callback 'fn-aec-pool-collection-request-internal)
   :complete (fnn-fixed-raw-callback 'fn-aec-pool-collect-observed-internal)
   :fence (fnn-fixed-raw-callback 'fn-aec-pool-uncertain-internal)))

(defun fnn-runtime-collection-complete-locked (binding nonce)
  "Nonce-only completion. Observe the retained primitive carrier internally.
Caller keeps the actual SAMEpool mutex and allocation barrier closed."
  (let ((sample (fnn-runtime-collector-binding-observation binding)))
    (multiple-value-bind (word pool)
        (fnn-core-mv 'fn-aec-pool-collect-observed-internal
          (funcall (fnn-runtime-collector-binding-complete binding)
                   nonce
                   (fnn-runtime-collection-association sample)
                   (fnn-runtime-collection-epoch sample)
                   (fnn-runtime-collection-nonce sample)
                   (fnn-runtime-collection-status sample)
                   (fnn-runtime-collection-dynamic-pages sample)
                   (fnn-runtime-collection-page-octets sample)
                   (fnn-runtime-collection-dynamic-reservation sample)
                   (fnn-runtime-collector-binding-pool binding)))
      (declare (ignore pool))
      word)))

(defun fnn-runtime-collection-step-locked (binding)
  "One collector scheduling step under the existing SAMEpool mutex.
A non-quiescent request returns without waiting: caller releases its locks
so admitted turns can finish. Only core :COLLECT invokes the primitive.
Every exit keeps the actual core's admission mode; no host Boolean reopens it."
  (let ((returned nil))
    (unwind-protect
        (multiple-value-prog1
            (multiple-value-bind (word association epoch nonce pool)
                (fnn-core-mv 'fn-aec-pool-collection-request-internal
                  (funcall (fnn-runtime-collector-binding-request binding)
                           (fnn-runtime-collector-binding-pool binding)))
              (declare (ignore pool))
              (if (eq word :collect)
                  (let ((sample (fnn-runtime-collector-binding-observation binding)))
                    ;; Preserve the issued request before the first GC effect.
                    (setf (fnn-runtime-collection-association sample) association
                          (fnn-runtime-collection-epoch sample) epoch
                          (fnn-runtime-collection-nonce sample) nonce
                          (fnn-runtime-collection-status sample) :unobserved)
                    (fnn-runtime-collect-into sample)
                    ;; Primitive :DEFERRED is delivered to the core as such;
                    ;; neither it nor an ambiguous callback is retried here.
                    (fnn-runtime-collection-complete-locked binding nonce))
                word))
          (setf returned t))
      ;; Includes raw nonlocal exits: the retained intent/nonce/charges are
      ;; fenced before the caller can release the serialization mutex.
      (unless returned
        (fnn-core-mv 'fn-aec-pool-uncertain-internal
          (funcall (fnn-runtime-collector-binding-fence binding)
                   (fnn-runtime-collector-binding-pool binding)))))))

(defun fnn-runtime-collection-step (binding)
  "Outer trampoline: acquire the existing pool mutex, never the owner lock.
Only pool/runtime callbacks are installed here; STATE access would require
owner exclusion before this call. Non-quiescent steps never wait for turns."
  (sb-thread:with-recursive-lock (*fnn-extent-lock*)
    (fnn-runtime-collection-step-locked binding)))

(defun fnn-runtime-collection-complete (binding nonce)
  "Public native completion accepts only the issued nonce and installed binding."
  (sb-thread:with-recursive-lock (*fnn-extent-lock*)
    (let ((returned nil))
      (unwind-protect
          (multiple-value-prog1
              (fnn-runtime-collection-complete-locked binding nonce)
            (setf returned t))
        (unless returned
          (fnn-core-mv 'fn-aec-pool-uncertain-internal
            (funcall (fnn-runtime-collector-binding-fence binding)
                     (fnn-runtime-collector-binding-pool binding))))))))
