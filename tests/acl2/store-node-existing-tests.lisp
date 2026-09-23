; Reachable Store outcomes and teeth for the actual host-called decision.
(in-package "ACL2")
(include-book "../../books/store-node-existing-invariants")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *snex-groups* '("fn.letters" "fn.test"))
(defconst *snex-record*
  (fn-record-make 0 0 0 "<held@example>" '(65 66) *snex-groups*
                  "snex-pin" "snex-subject" "snex-release" 2 841000000))
(defconst *snex-reserved*
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io
              (fn-sn-initial *snex-groups* 10) :start-frontier nil)
              :frontier-file :ok) :frontier-replace :ok)
              :frontier-directory :ok))
(defconst *snex-prepared* (fn-sn-prepare *snex-reserved* *snex-record*))
(defconst *snex-finished*
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io *snex-prepared* :record-file :ok)
                        :record-link :ok)
             :record-directory :ok)))

(assert-event (fn-sn-statep *snex-finished*))
(assert-event (fn-sn-committed-recordp (fn-sn-node *snex-finished*) *snex-record*))
(assert-event (equal (fn-sn-existing-action
                      "<held@example>" '(65 66) *snex-groups* *snex-finished*)
                     :duplicate))
(assert-event (equal (fn-sn-existing-action
                      "<held@example>" '(99) *snex-groups* *snex-finished*)
                     :conflict))
(assert-event (equal (fn-sn-existing-action
                      "<held@example>" '(65 66) '("fn.letters") *snex-finished*)
                     :conflict))
(assert-event (null (fn-sn-existing-action
                     "<missing@example>" '(65 66) *snex-groups* *snex-finished*)))

; Each deleted premise makes the corresponding outcome false on the same
; committed article: payload equality, group equality, or a held binding.
(must-fail
 (assert-event
  (equal (fn-sn-existing-action
          "<held@example>" '(99) *snex-groups* *snex-finished*)
         :duplicate)))
(must-fail
 (assert-event
  (equal (fn-sn-existing-action
          "<held@example>" '(65 66) '("fn.letters") *snex-finished*)
         :duplicate)))
(must-fail
 (assert-event
  (equal (fn-sn-existing-action
          "<missing@example>" '(65 66) *snex-groups* *snex-finished*)
         :duplicate)))
; A difference without a held Message-ID is missing, not a conflict.
(must-fail
 (assert-event
  (equal (fn-sn-existing-action
          "<missing@example>" '(99) *snex-groups* *snex-finished*)
         :conflict)))
