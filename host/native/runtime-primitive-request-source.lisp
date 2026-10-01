;;;; Image compiler/export primitive facts, not an operation allowance.
(in-package "CL-USER")
(defun fnn-runtime-primitive-request-layout ()
  ;; The core/compiler consumer performs any count-to-byte arithmetic.
  ;; Complete six MVs; no per-read record/list constructor.
  (values :selected-primitive-request-layout
          sb-vm:cons-size sb-vm:n-word-bytes sb-vm:vector-data-offset
          sb-vm:lowtag-mask most-positive-fixnum))
