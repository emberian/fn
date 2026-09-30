;;; Raw selected-runtime test; launch in a fresh SBCL, never an ACL2 world
;;; or a served node. The shell loads runtime-collector.lisp before this file.
(in-package "ACL2")
(defvar *fnn-test-collection* (make-fnn-runtime-collection))
(defvar *fnn-test-retained* nil)
(let ((sample *fnn-test-collection*))
  (setf (fnn-runtime-collection-association sample) '(:test-installation)
        (fnn-runtime-collection-epoch sample) 17
        (fnn-runtime-collection-nonce sample) '(:issued 29))
  ;; Actual inhibited primitive must not turn a stale sample into completion.
  (sb-sys:without-gcing
    (assert (eq (fnn-runtime-collect-into sample) :deferred))
    (assert (eq (fnn-runtime-collection-status sample) :deferred)))
  ;; This reference survives collection; no assertion promises another
  ;; object's reclamation or that a full collection makes enough room.
  (setf *fnn-test-retained*
        (make-array (* 2 1024 1024) :element-type '(unsigned-byte 8)
                    :initial-element 91))
  (let ((before sb-kernel::*gc-epoch*))
    (assert (eq (fnn-runtime-collect-into sample) :completed))
    (assert (not (eq before sb-kernel::*gc-epoch*))))
  (let ((pages (fnn-runtime-collection-dynamic-pages sample)))
    (sb-sys:without-gcing
      (assert (eq (fnn-runtime-collect-into sample) :deferred))
      (assert (eq (fnn-runtime-collection-status sample) :deferred))
      (assert (= (fnn-runtime-collection-dynamic-pages sample) pages))))
  (assert (eq (fnn-runtime-collect-into sample) :completed))
  (assert (= (aref *fnn-test-retained* (1- (length *fnn-test-retained*))) 91))
  (assert (equal (fnn-runtime-collection-association sample) '(:test-installation)))
  (assert (= (fnn-runtime-collection-epoch sample) 17))
  (assert (equal (fnn-runtime-collection-nonce sample) '(:issued 29)))
  (assert (= (fnn-runtime-collection-page-octets sample) sb-vm:gencgc-page-bytes))
  (assert (<= (* (fnn-runtime-collection-dynamic-pages sample)
                 (fnn-runtime-collection-page-octets sample))
              (fnn-runtime-collection-dynamic-reservation sample)))
  (assert (<= (length *fnn-test-retained*)
              (* (fnn-runtime-collection-dynamic-pages sample)
                 (fnn-runtime-collection-page-octets sample))))
  (format t "~&COLLECTOR-COMPONENT PASS version=~A pages=~D page-octets=~D reservation=~D~%"
          (lisp-implementation-version)
          (fnn-runtime-collection-dynamic-pages sample)
          (fnn-runtime-collection-page-octets sample)
          (fnn-runtime-collection-dynamic-reservation sample)))
