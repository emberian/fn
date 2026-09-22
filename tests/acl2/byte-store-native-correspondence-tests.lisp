(in-package "ACL2")
(include-book "../../books/byte-store-native-correspondence")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

; Reach the actual composed subject at the allocator commit observation.  The
; frontier changes and the node does not, so this is not an identity witness.
(assert-event
 (let* ((s0 (fn-sn-initial nil 0))
        (s1 (fn-sn-io s0 :start-frontier :ok))
        (s2 (fn-sn-io s1 :frontier-file :ok))
        (s3 (fn-sn-io s2 :frontier-replace :ok))
        (s4 (fn-sn-io s3 :frontier-directory :ok)))
   (and (equal (fn-sf-phase (fn-sn-files s3)) :frontier-attempted)
        (equal (fn-sf-phase (fn-sn-files s4)) :reserved)
        (equal (fn-sn-node s4) (fn-sn-node s3)))))

; Dropping the operation-domain hypothesis loses the typed byte-program event.
(must-fail
 (assert-event
  (fn-sf-eventp
   (fn-bs-native-io-event :not-a-native-operation :ok))))

; The result hypothesis has teeth too: a successful operation tag with an
; outcome that host/native/io.lisp never reports is not a typed event.
(must-fail
 (assert-event
  (fn-sf-eventp (fn-bs-native-io-event :record-link :known-fail))))
