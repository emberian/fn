;;;; Image-compiler input for the matched U64 arithmetic request component.
;;;; A partial primary-request row is never an operation or installation grant.
(in-package "CL-USER")
(defun fnn-runtime-u64-primary-request-unit ()
  ;; Read only while producing the SAME compiled-image source table. Matching
  ;; target geometry alone does not authenticate the body or install authority.
  ;; The compiler additionally binds the exact e73cf25ee capture/source hashes.
  (if (and #+(and linux x86-64 sb-thread) t
           #-(and linux x86-64 sb-thread) nil
           (string= (lisp-implementation-version) "2.6.8")
           (= sb-vm:n-word-bytes 8) (= sb-vm:lowtag-mask 15)
           (= most-positive-fixnum 4611686018427387903))
      (values :conditional-primary-unit
              '(:frame-u64-arithmetic :sbcl-2.6.8 :linux-x86-64 :u64-export-4a6) 64 2 64
              '(:splitter-cons :caller-and-library-frames :first-use :fault-signaling
                :allocator-region-slack :automatic-collector :retirement-and-gc))
      (values :runtime-unit-unavailable nil nil nil nil
              :unsupported-selected-target)))
