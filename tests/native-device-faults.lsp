;;; Raw syscall-boundary controls only; the qualified companion also checks
;;; fn2-n-storage-completions and the actual ACL2 result normalizer.
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(load "host/ffi.lisp")
(load "host/device.lisp")
(load "tests/fixtures/device-faults/control.lisp")
(fn2-device-fault-controls)
