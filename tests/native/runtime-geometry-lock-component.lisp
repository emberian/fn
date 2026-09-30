;;; Dedicated disposable selected ACL2/SBCL process only. Load after the
;;; actual collector core component; it supplies the synthetic pool fixture.
(in-package "ACL2")

(defun fnn-test-geometry-lock-returned ()
  ;; Another thread must acquire both actual locks after return or unwind.
  ;; The waiter is created outside either critical section.
  (let ((worker
         (sb-thread:make-thread
          (lambda ()
            (sb-thread:with-recursive-lock (*fnn-extent-lock*)
              (sb-sys:without-interrupts
                (sb-sys:without-gcing
                  (fnn-%runtime-page-table-acquire)
                  (unwind-protect :locks-returned
                    (fnn-%runtime-page-table-release)))))))))
    (assert (eq (sb-thread:join-thread worker :timeout 5 :default :timed-out)
                :locks-returned))))

(let ((sample (make-fnn-runtime-collection)))
  (setf (fnn-runtime-collection-association sample) :retained-association
        (fnn-runtime-collection-epoch sample) 17
        (fnn-runtime-collection-nonce sample) 23)
  (fnn-runtime-geometry-into sample)
  (assert (eq (fnn-runtime-collection-status sample) :unobserved))
  (assert (eq (fnn-runtime-collection-association sample) :retained-association))
  (assert (= (fnn-runtime-collection-epoch sample) 17))
  (assert (= (fnn-runtime-collection-nonce sample) 23))
  (assert (<= 0 (fnn-runtime-collection-dynamic-pages sample)))
  (assert (= (fnn-runtime-collection-page-octets sample) sb-vm:gencgc-page-bytes))
  (assert (= (fnn-runtime-collection-dynamic-reservation sample)
             (sb-ext:dynamic-space-size)))
  (fnn-test-geometry-lock-returned))

;; Inject an escape after the actual allocator lock has been released, before
;; the primitive can publish COMPLETED. No recording core callback is used.
;; The production primitive and actual pool/nonce completion path are loaded.
(let* ((pool (fnn-test-collector-core-pool 0 23))
       (binding (fnn-runtime-collector-binding-make pool))
       (sample (fnn-runtime-collector-binding-observation binding))
       (release (symbol-function 'fnn-%runtime-page-table-release))
       (escaped nil))
  (unwind-protect
      (progn
        (setf (symbol-function 'fnn-%runtime-page-table-release)
              (lambda () (funcall release) (error "test release-return escape")))
        (handler-case (fnn-runtime-collection-step binding)
          (error () (setf escaped t))))
    (setf (symbol-function 'fnn-%runtime-page-table-release) release))
  (assert escaped)
  (assert (eq (fnn-runtime-collection-status sample) :uncertain))
  (assert (= (fnn-runtime-collection-nonce sample) 23))
  (assert (equal (fnn-runtime-collection-association sample)
                 (fn-aec-at 1 (fn-prp-alloc-installation pool))))
  (assert (eq (fn-prp-alloc-mode pool) :recovery))
  (assert (= (fn-prp-alloc-epoch pool) 17))
  (assert (= (fn-prp-alloc-occupied pool) 65536))
  (assert (= (fn-prp-alloc-allocated pool) 640))
  (assert (= (fn-prp-alloc-active-turns pool) 0))
  (assert (= (fn-prp-alloc-gc-nonce pool) 23))
  (assert (= (fn-prl-nth 2 (fn-owner-page-read-ledger pool)) 24))
  (assert (fn-aec-pool-statep pool))
  (fnn-test-geometry-lock-returned))

(format t "~&COLLECTOR-GEOMETRY-LOCK PASS snapshot/return/escape/fence~%")
