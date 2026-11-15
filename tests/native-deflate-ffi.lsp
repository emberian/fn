;;; Real selected library + actual raw host wrapper; no ACL2/node/listener.
;;; sbcl --script tests/native-deflate-ffi.lsp /absolute/selected-library.so
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defparameter *qualified-library* (or (second sb-ext:*posix-argv*) (error "library path required")))
(sb-alien:load-shared-object *qualified-library*)
(load "host/deflate.lisp")
(let ((handle (fn2-deflate-%new))
      (plain (make-array 19 :element-type '(unsigned-byte 8) :initial-contents
                         '(110 97 116 105 118 101 32 100 101 102 108 97 116 101 32 65 66 67 10)))
      (wire (make-array 256 :element-type '(unsigned-byte 8) :initial-element 0))
      (decoded (make-array 256 :element-type '(unsigned-byte 8) :initial-element 0)))
 (assert (not (zerop (sb-sys:sap-int handle))))
 (unwind-protect
  (sb-sys:with-pinned-objects (plain wire decoded)
   (multiple-value-bind (status used made)
       (fn2-native-deflate-step handle 1 (sb-sys:vector-sap plain) (length plain)
                                (sb-sys:vector-sap wire) (length wire))
    (assert (and (= status 0) (= used (length plain)) (< 0 made) (< made (length wire))))
    (multiple-value-bind (status consumed produced)
        (fn2-native-deflate-step handle 0 (sb-sys:vector-sap wire) made
                                 (sb-sys:vector-sap decoded) (length decoded))
     (assert (and (= status 0) (= consumed made) (= produced (length plain))
                  (equalp plain (subseq decoded 0 produced)))))))
  (fn2-deflate-%free handle)))
(format t "NATIVE DEFLATE FFI PASS selected=~a actual wrapper pinned duplex roundtrip~%" *qualified-library*)
