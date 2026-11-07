;;; The simulator's newest-write-first snapshot must import identically on
;;; both native devices, including overlapping writes. Run with sbcl --script.
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(load "host/native-session-raw.lisp")
(let* ((*fn2-n-seed-store* '((1 9 8) (0 1 2 3)))
       (path (format nil "build/image-carrier-~d-~d.img" (get-universal-time) (random 1000000)))
       (host (make-fn2-nhost :ops (make-array 4) :mux (make-fn2-native-mux 4)))
       (bytes (make-array 4 :element-type '(unsigned-byte 8) :initial-element 0)))
  (unwind-protect
      (progn
        (fn2-n-device-put host *fn2-n-seed-store*)
        (assert (equal (loop for i below 4 collect (fn2-n-device-ref host i)) '(1 9 8 0)))
        (fn2-ns-install-fixture-image host path)
        (let ((job (make-fn2-device-job :kind :read :bytes bytes :address 0 :length 4 :offset 0)))
          (fn2-device-perform (fn2-nhost-storage host) job)
          (assert (= (fn2-device-job-result job) 4))
          (assert (equalp bytes #(1 9 8 0))))
        (format t "~%NATIVE IMAGE CARRIER UNIT PASS: overlapping snapshot writes~%"))
    (when (fn2-nhost-storage host) (fn2-device-stop (fn2-nhost-storage host)))
    (fn2-native-mux-destroy (fn2-nhost-mux host))))
